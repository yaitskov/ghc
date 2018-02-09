/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 1998-2018
 *
 * Non-moving garbage collector and allocator
 *
 * ---------------------------------------------------------------------------*/

#include "Rts.h"
#include "RtsUtils.h"
#include "NonMoving.h"
#include "Capability.h"

struct nonmoving_heap nonmoving_heap;

generation nonmoving_gen;

#define MAX(h,i) ((h) > (i) ? (h) : (i))

// Request a fresh segment from the free segment list or allocate one of the
// given node.
static struct nonmoving_segment *nonmoving_request_segment(uint32_t node)
{
    struct nonmoving_segment *ret;
    ACQUIRE_LOCK(&nonmoving_heap.mutex);
    if (nonmoving_heap.free) {
        ret = nonmoving_heap.free;
        nonmoving_heap.free = ret->link;
    } else {
        // TODO Aligned block allocation (#7)
        bdescr *bd = allocGroupOnNode_lock(node, 2*NONMOVING_SEGMENT_BLOCKS - 1);
        initBdescr(bd, &nonmoving_gen, &nonmoving_gen); // TODO: hmmmm, refactoring needed?
        bd->flags = BF_NONMOVING;
        // TODO allocation accounting?
        ret = (struct nonmoving_segment *) (bd->start + NONMOVING_SEGMENT_SIZE - ((uintptr_t) bd->start % NONMOVING_SEGMENT_SIZE)); // XXX: yuck
    }
    RELEASE_LOCK(&nonmoving_heap.mutex);
    return ret;
}

static int log2_ceil(int x)
{
    int res = 0;
    while (x) {
        res++;
        x = x >> 1;
    }
    return res;
}

static void *nonmoving_allocate_block_from_segment(struct nonmoving_segment *seg)
{
    uint8_t *bitmap = seg->bitmap;
    for (unsigned int i = seg->next_free; i < nonmoving_segment_block_count(seg); i++) {
        if (!bitmap[i]) {
            seg->next_free = i + 1;
            return nonmoving_segment_get_block(seg, i);
        }
    }
    return 0;
}

void *nonmoving_allocate(Capability *cap, StgWord sz)
{
    int allocator_idx = MAX(log2_ceil(sz), NONMOVING_ALLOCA0);
    if (allocator_idx < NONMOVING_ALLOCA0) {
        allocator_idx = NONMOVING_ALLOCA0;
    } else if (allocator_idx > NONMOVING_ALLOCA0 + NONMOVING_ALLOCA_CNT) {
        // TODO: Allocate large object? Perhaps this should be handled elsewhere
    }

    struct nonmoving_allocator *alloca = nonmoving_heap.allocators[allocator_idx];

    // First try allocating into current segment
    while (true) {
        struct nonmoving_segment *current = alloca->current[cap->no];
        void *ret = nonmoving_allocate_block_from_segment(current);
        if (ret) {
            return ret;

        // Current segments is filled; look elsewhere
        } else if (alloca->active) {
            // We want to move the current segment to the filled list and pull a
            // new segment from active. This is a bit tricky in the face of
            // parallel allocation
            struct nonmoving_segment *new_current = alloca->active;
            struct nonmoving_segment *old_current = (struct nonmoving_segment *)
                cas((StgVolatilePtr) &alloca->current[cap->no],
                    (StgWord) current,
                    (StgWord) new_current);
            if (old_current == current) {
                // we have successfully locked the allocator; insert old current into filled list
                while (true) {
                    old_current->link = alloca->filled;
                    write_barrier(); // Ensure ->link update appears; TODO: Is this implied by CAS?
                    struct nonmoving_segment *out = (struct nonmoving_segment *)
                        cas((StgVolatilePtr) &alloca->filled,
                            (StgWord) old_current->link,
                            (StgWord) old_current);
                    if (out == old_current->link) {
                        break; // successful insert
                    }
                }
            } else {
                // someone else locked the allocator to perform the insertion
            }

        // There are no active segments, allocate more segments
        } else {
            // Lock the allocator by setting current=NULL while we request a new segment.
            struct nonmoving_segment *old_current = (struct nonmoving_segment *)
                cas((StgVolatilePtr) &alloca->current[cap->no],
                    (StgWord) current,
                    0);
            if (old_current == NULL) {
                // Wait until other thread has finished
                while (alloca->current[cap->no] == NULL) {}
            } else {
                alloca->current[cap->no] = nonmoving_request_segment(cap->node);
            }
        }
    }
}

static struct nonmoving_allocator *alloc_nonmoving_allocator(uint32_t n_caps)
{
    size_t allocator_sz =
        sizeof(struct nonmoving_allocator) +
        sizeof(void*) * n_caps; // current segment pointer for each capability
    struct nonmoving_allocator *alloc =
        stgMallocBytes(allocator_sz, "nonmoving_init");
    memset(alloc, 0, allocator_sz);
    return alloc;
}

void nonmoving_init(void)
{
    initMutex(&nonmoving_heap.mutex);
    for (unsigned int i = 0; i < NONMOVING_ALLOCA_CNT; i++) {
        nonmoving_heap.allocators[i] = alloc_nonmoving_allocator(n_capabilities);
    }
}

// Assumes that no garbage collector or mutator threads are running to safely
// resize the nonmoving_allocators.
void nonmoving_add_capabilities(uint32_t new_n_caps)
{
    unsigned int old_n_caps = nonmoving_heap.n_caps;
    struct nonmoving_allocator **allocs = nonmoving_heap.allocators;

    for (unsigned int i = 0; i < NONMOVING_ALLOCA_CNT; i++) {
        struct nonmoving_allocator *old = allocs[i];
        allocs[i] = alloc_nonmoving_allocator(new_n_caps);

        // Copy the old state
        allocs[i]->filled = old->filled;
        allocs[i]->active = old->active;
        for (int j = 0; i < old_n_caps; i++) {
            allocs[i]->current[j] = old->current[j];
        }
        stgFree(old);

        // Initialize current segments for the new capabilities
        for (int j = old_n_caps; i < new_n_caps; i++) {
            allocs[i]->current[j] = nonmoving_request_segment(capabilities[j]->node);
            allocs[i]->current[j]->link = NULL;
        }
    }
    nonmoving_heap.n_caps = new_n_caps;
}
