{-
(c) Galois, 2006
(c) University of Glasgow, 2007
-}

{-# LANGUAGE NondecreasingIndentation, RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

{-# OPTIONS_GHC -Wno-incomplete-record-updates #-}

module GHC.HsToCore.Coverage (addTicksToBinds, hpcInitCode) where

import GHC.Prelude as Prelude

import qualified GHC.Runtime.Interpreter as GHCi
import GHCi.RemoteTypes
import Data.Array
import GHC.ByteCode.Types
import GHC.Stack.CCS
import GHC.Core.Type
import GHC.Hs
import GHC.Unit
import GHC.Utils.Outputable as Outputable
import GHC.Driver.Session
import GHC.Core.ConLike
import Control.Monad
import GHC.Types.SrcLoc
import GHC.Utils.Error
import GHC.Types.Name.Set hiding (FreeVars)
import GHC.Types.Name
import GHC.Data.Bag
import GHC.Types.CostCentre
import GHC.Types.CostCentre.State
import GHC.Core
import GHC.Types.Id
import GHC.Types.Var.Set
import Data.List
import GHC.Data.FastString
import GHC.Driver.Types
import GHC.Core.TyCon
import GHC.Types.Basic
import GHC.Utils.Monad
import GHC.Data.Maybe
import GHC.Cmm.CLabel
import GHC.Utils.Misc

import Data.Time
import System.Directory

import Trace.Hpc.Mix
import Trace.Hpc.Util

import qualified Data.ByteString as BS
import Data.Set (Set)
import qualified Data.Set as Set

{-
************************************************************************
*                                                                      *
*              The main function: addTicksToBinds
*                                                                      *
************************************************************************
-}

addTicksToBinds
        :: HscEnv
        -> Module
        -> ModLocation          -- ... off the current module
        -> NameSet              -- Exported Ids.  When we call addTicksToBinds,
                                -- isExportedId doesn't work yet (the desugarer
                                -- hasn't set it), so we have to work from this set.
        -> [TyCon]              -- Type constructor in this module
        -> LHsBinds GhcTc
        -> IO (LHsBinds GhcTc, HpcInfo, Maybe ModBreaks)

addTicksToBinds hsc_env mod mod_loc exports tyCons binds
  | let dflags = hsc_dflags hsc_env
        passes = coveragePasses dflags, not (null passes),
    Just orig_file <- ml_hs_file mod_loc,
    not ("boot" `isSuffixOf` orig_file) = do

     let  orig_file2 = guessSourceFile binds orig_file

          tickPass tickish (binds,st) =
            let env = TTE
                      { fileName     = mkFastString orig_file2
                      , declPath     = []
                      , tte_dflags   = dflags
                      , exports      = exports
                      , inlines      = emptyVarSet
                      , inScope      = emptyVarSet
                      , blackList    = Set.fromList $
                                       mapMaybe (\tyCon -> case getSrcSpan (tyConName tyCon) of
                                                             RealSrcSpan l _ -> Just l
                                                             UnhelpfulSpan _ -> Nothing)
                                                tyCons
                      , density      = mkDensity tickish dflags
                      , this_mod     = mod
                      , tickishType  = tickish
                      }
                (binds',_,st') = unTM (addTickLHsBinds binds) env st
            in (binds', st')

          initState = TT { tickBoxCount = 0
                         , mixEntries   = []
                         , ccIndices    = newCostCentreState
                         }

          (binds1,st) = foldr tickPass (binds, initState) passes

     let tickCount = tickBoxCount st
         entries = reverse $ mixEntries st
     hashNo <- writeMixEntries dflags mod tickCount entries orig_file2
     modBreaks <- mkModBreaks hsc_env mod tickCount entries

     dumpIfSet_dyn dflags Opt_D_dump_ticked "HPC" FormatHaskell
       (pprLHsBinds binds1)

     return (binds1, HpcInfo tickCount hashNo, Just modBreaks)

  | otherwise = return (binds, emptyHpcInfo False, Nothing)

guessSourceFile :: LHsBinds GhcTc -> FilePath -> FilePath
guessSourceFile binds orig_file =
     -- Try look for a file generated from a .hsc file to a
     -- .hs file, by peeking ahead.
     let top_pos = catMaybes $ foldr (\ (L pos _) rest ->
                                 srcSpanFileName_maybe pos : rest) [] binds
     in
     case top_pos of
        (file_name:_) | ".hsc" `isSuffixOf` unpackFS file_name
                      -> unpackFS file_name
        _ -> orig_file


mkModBreaks :: HscEnv -> Module -> Int -> [MixEntry_] -> IO ModBreaks
mkModBreaks hsc_env mod count entries
  | HscInterpreted <- hscTarget (hsc_dflags hsc_env) = do
    breakArray <- GHCi.newBreakArray hsc_env (length entries)
    ccs <- mkCCSArray hsc_env mod count entries
    let
           locsTicks  = listArray (0,count-1) [ span  | (span,_,_,_)  <- entries ]
           varsTicks  = listArray (0,count-1) [ vars  | (_,_,vars,_)  <- entries ]
           declsTicks = listArray (0,count-1) [ decls | (_,decls,_,_) <- entries ]
    return emptyModBreaks
                       { modBreaks_flags = breakArray
                       , modBreaks_locs  = locsTicks
                       , modBreaks_vars  = varsTicks
                       , modBreaks_decls = declsTicks
                       , modBreaks_ccs   = ccs
                       }
  | otherwise = return emptyModBreaks

mkCCSArray
  :: HscEnv -> Module -> Int -> [MixEntry_]
  -> IO (Array BreakIndex (RemotePtr GHC.Stack.CCS.CostCentre))
mkCCSArray hsc_env modul count entries = do
  case hsc_interp hsc_env of
    Just interp | GHCi.interpreterProfiled interp -> do
      let module_str = moduleNameString (moduleName modul)
      costcentres <- GHCi.mkCostCentres hsc_env module_str (map mk_one entries)
      return (listArray (0,count-1) costcentres)

    _ -> return (listArray (0,-1) [])
 where
    dflags = hsc_dflags hsc_env
    mk_one (srcspan, decl_path, _, _) = (name, src)
      where name = concat (intersperse "." decl_path)
            src = showSDoc dflags (ppr srcspan)


writeMixEntries
  :: DynFlags -> Module -> Int -> [MixEntry_] -> FilePath -> IO Int
writeMixEntries dflags mod count entries filename
  | not (gopt Opt_Hpc dflags) = return 0
  | otherwise   = do
        let
            hpc_dir = hpcDir dflags
            mod_name = moduleNameString (moduleName mod)

            hpc_mod_dir
              | moduleUnit mod == mainUnitId  = hpc_dir
              | otherwise = hpc_dir ++ "/" ++ unitString (moduleUnit mod)

            tabStop = 8 -- <tab> counts as a normal char in GHC's
                        -- location ranges.

        createDirectoryIfMissing True hpc_mod_dir
        modTime <- getModificationUTCTime filename
        let entries' = [ (hpcPos, box)
                       | (span,_,_,box) <- entries, hpcPos <- [mkHpcPos span] ]
        when (entries' `lengthIsNot` count) $ do
          panic "the number of .mix entries are inconsistent"
        let hashNo = mixHash filename modTime tabStop entries'
        mixCreate hpc_mod_dir mod_name
                       $ Mix filename modTime (toHash hashNo) tabStop entries'
        return hashNo


-- -----------------------------------------------------------------------------
-- TickDensity: where to insert ticks

data TickDensity
  = TickForCoverage       -- for Hpc
  | TickForBreakPoints    -- for GHCi
  | TickAllFunctions      -- for -prof-auto-all
  | TickTopFunctions      -- for -prof-auto-top
  | TickExportedFunctions -- for -prof-auto-exported
  | TickCallSites         -- for stack tracing
  deriving Eq

mkDensity :: TickishType -> DynFlags -> TickDensity
mkDensity tickish dflags = case tickish of
  HpcTicks             -> TickForCoverage
  SourceNotes          -> TickForCoverage
  Breakpoints          -> TickForBreakPoints
  ProfNotes ->
    case profAuto dflags of
      ProfAutoAll      -> TickAllFunctions
      ProfAutoTop      -> TickTopFunctions
      ProfAutoExports  -> TickExportedFunctions
      ProfAutoCalls    -> TickCallSites
      _other           -> panic "mkDensity"

-- | Decide whether to add a tick to a binding or not.
shouldTickBind  :: TickDensity
                -> Bool         -- top level?
                -> Bool         -- exported?
                -> Bool         -- simple pat bind?
                -> Bool         -- INLINE pragma?
                -> Bool

shouldTickBind density top_lev exported _simple_pat inline
 = case density of
      TickForBreakPoints    -> False
        -- we never add breakpoints to simple pattern bindings
        -- (there's always a tick on the rhs anyway).
      TickAllFunctions      -> not inline
      TickTopFunctions      -> top_lev && not inline
      TickExportedFunctions -> exported && not inline
      TickForCoverage       -> True
      TickCallSites         -> False

shouldTickPatBind :: TickDensity -> Bool -> Bool
shouldTickPatBind density top_lev
  = case density of
      TickForBreakPoints    -> False
      TickAllFunctions      -> True
      TickTopFunctions      -> top_lev
      TickExportedFunctions -> False
      TickForCoverage       -> False
      TickCallSites         -> False

-- -----------------------------------------------------------------------------
-- Adding ticks to bindings

addTickLHsBinds :: LHsBinds GhcTc -> TM (LHsBinds GhcTc)
addTickLHsBinds = mapBagM addTickLHsBind

addTickLHsBind :: LHsBind GhcTc -> TM (LHsBind GhcTc)
addTickLHsBind (L pos bind@(AbsBinds { abs_binds   = binds,
                                       abs_exports = abs_exports })) = do
  withEnv add_exports $ do
  withEnv add_inlines $ do
  binds' <- addTickLHsBinds binds
  return $ L pos $ bind { abs_binds = binds' }
 where
   -- in AbsBinds, the Id on each binding is not the actual top-level
   -- Id that we are defining, they are related by the abs_exports
   -- field of AbsBinds.  So if we're doing TickExportedFunctions we need
   -- to add the local Ids to the set of exported Names so that we know to
   -- tick the right bindings.
   add_exports env =
     env{ exports = exports env `extendNameSetList`
                      [ idName mid
                      | ABE{ abe_poly = pid, abe_mono = mid } <- abs_exports
                      , idName pid `elemNameSet` (exports env) ] }

   -- See Note [inline sccs]
   add_inlines env =
     env{ inlines = inlines env `extendVarSetList`
                      [ mid
                      | ABE{ abe_poly = pid, abe_mono = mid } <- abs_exports
                      , isInlinePragma (idInlinePragma pid) ] }

addTickLHsBind (L pos (funBind@(FunBind { fun_id = L _ id }))) = do
  let name = getOccString id
  decl_path <- getPathEntry
  density <- getDensity

  inline_ids <- liftM inlines getEnv
  -- See Note [inline sccs]
  let inline   = isInlinePragma (idInlinePragma id)
                 || id `elemVarSet` inline_ids

  -- See Note [inline sccs]
  tickish <- tickishType `liftM` getEnv
  if inline && tickish == ProfNotes then return (L pos funBind) else do

  (fvs, mg) <-
        getFreeVars $
        addPathEntry name $
        addTickMatchGroup False (fun_matches funBind)

  blackListed <- isBlackListed pos
  exported_names <- liftM exports getEnv

  -- We don't want to generate code for blacklisted positions
  -- We don't want redundant ticks on simple pattern bindings
  -- We don't want to tick non-exported bindings in TickExportedFunctions
  let simple = isSimplePatBind funBind
      toplev = null decl_path
      exported = idName id `elemNameSet` exported_names

  tick <- if not blackListed &&
               shouldTickBind density toplev exported simple inline
             then
                bindTick density name pos fvs
             else
                return Nothing

  let mbCons = maybe Prelude.id (:)
  return $ L pos $ funBind { fun_matches = mg
                           , fun_tick = tick `mbCons` fun_tick funBind }

   where
   -- a binding is a simple pattern binding if it is a funbind with
   -- zero patterns
   isSimplePatBind :: HsBind GhcTc -> Bool
   isSimplePatBind funBind = matchGroupArity (fun_matches funBind) == 0

-- TODO: Revisit this
addTickLHsBind (L pos (pat@(PatBind { pat_lhs = lhs
                                    , pat_rhs = rhs }))) = do

  let simplePatId = isSimplePat lhs

  -- TODO: better name for rhs's for non-simple patterns?
  let name = maybe "(...)" getOccString simplePatId

  (fvs, rhs') <- getFreeVars $ addPathEntry name $ addTickGRHSs False False rhs
  let pat' = pat { pat_rhs = rhs'}

  -- Should create ticks here?
  density <- getDensity
  decl_path <- getPathEntry
  let top_lev = null decl_path
  if not (shouldTickPatBind density top_lev)
    then return (L pos pat')
    else do

    let mbCons = maybe id (:)

    let (initial_rhs_ticks, initial_patvar_tickss) = pat_ticks pat'

    -- Allocate the ticks

    rhs_tick <- bindTick density name pos fvs
    let rhs_ticks = rhs_tick `mbCons` initial_rhs_ticks

    patvar_tickss <- case simplePatId of
      Just{} -> return initial_patvar_tickss
      Nothing -> do
        let patvars = map getOccString (collectPatBinders lhs)
        patvar_ticks <- mapM (\v -> bindTick density v pos fvs) patvars
        return
          (zipWith mbCons patvar_ticks
                          (initial_patvar_tickss ++ repeat []))

    return $ L pos $ pat' { pat_ticks = (rhs_ticks, patvar_tickss) }

-- Only internal stuff, not from source, uses VarBind, so we ignore it.
addTickLHsBind var_bind@(L _ (VarBind {})) = return var_bind
addTickLHsBind patsyn_bind@(L _ (PatSynBind {})) = return patsyn_bind

bindTick
  :: TickDensity -> String -> SrcSpan -> FreeVars -> TM (Maybe (Tickish Id))
bindTick density name pos fvs = do
  decl_path <- getPathEntry
  let
      toplev        = null decl_path
      count_entries = toplev || density == TickAllFunctions
      top_only      = density /= TickAllFunctions
      box_label     = if toplev then TopLevelBox [name]
                                else LocalBox (decl_path ++ [name])
  --
  allocATickBox box_label count_entries top_only pos fvs


-- Note [inline sccs]
--
-- The reason not to add ticks to INLINE functions is that this is
-- sometimes handy for avoiding adding a tick to a particular function
-- (see #6131)
--
-- So for now we do not add any ticks to INLINE functions at all.
--
-- We used to use isAnyInlinePragma to figure out whether to avoid adding
-- ticks for this purpose. However, #12962 indicates that this contradicts
-- the documentation on profiling (which only mentions INLINE pragmas).
-- So now we're more careful about what we avoid adding ticks to.

-- -----------------------------------------------------------------------------
-- Decorate an LHsExpr with ticks

-- selectively add ticks to interesting expressions
addTickLHsExpr :: LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTickLHsExpr e@(L pos e0) = do
  d <- getDensity
  case d of
    TickForBreakPoints | isGoodBreakExpr e0 -> tick_it
    TickForCoverage    -> tick_it
    TickCallSites      | isCallSite e0      -> tick_it
    _other             -> dont_tick_it
 where
   tick_it      = allocTickBox (ExpBox False) False False pos $ addTickHsExpr e0
   dont_tick_it = addTickLHsExprNever e

-- Add a tick to an expression which is the RHS of an equation or a binding.
-- We always consider these to be breakpoints, unless the expression is a 'let'
-- (because the body will definitely have a tick somewhere).  ToDo: perhaps
-- we should treat 'case' and 'if' the same way?
addTickLHsExprRHS :: LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTickLHsExprRHS e@(L pos e0) = do
  d <- getDensity
  case d of
     TickForBreakPoints | HsLet{} <- e0 -> dont_tick_it
                        | otherwise     -> tick_it
     TickForCoverage -> tick_it
     TickCallSites   | isCallSite e0 -> tick_it
     _other          -> dont_tick_it
 where
   tick_it      = allocTickBox (ExpBox False) False False pos $ addTickHsExpr e0
   dont_tick_it = addTickLHsExprNever e

-- The inner expression of an evaluation context:
--    let binds in [], ( [] )
-- we never tick these if we're doing HPC, but otherwise
-- we treat it like an ordinary expression.
addTickLHsExprEvalInner :: LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTickLHsExprEvalInner e = do
   d <- getDensity
   case d of
     TickForCoverage -> addTickLHsExprNever e
     _otherwise      -> addTickLHsExpr e

-- | A let body is treated differently from addTickLHsExprEvalInner
-- above with TickForBreakPoints, because for breakpoints we always
-- want to tick the body, even if it is not a redex.  See test
-- break012.  This gives the user the opportunity to inspect the
-- values of the let-bound variables.
addTickLHsExprLetBody :: LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTickLHsExprLetBody e@(L pos e0) = do
  d <- getDensity
  case d of
     TickForBreakPoints | HsLet{} <- e0 -> dont_tick_it
                        | otherwise     -> tick_it
     _other -> addTickLHsExprEvalInner e
 where
   tick_it      = allocTickBox (ExpBox False) False False pos $ addTickHsExpr e0
   dont_tick_it = addTickLHsExprNever e

-- version of addTick that does not actually add a tick,
-- because the scope of this tick is completely subsumed by
-- another.
addTickLHsExprNever :: LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTickLHsExprNever (L pos e0) = do
    e1 <- addTickHsExpr e0
    return $ L pos e1

-- general heuristic: expressions which do not denote values are good
-- break points
isGoodBreakExpr :: HsExpr GhcTc -> Bool
isGoodBreakExpr (HsApp {})     = True
isGoodBreakExpr (HsAppType {}) = True
isGoodBreakExpr (OpApp {})     = True
isGoodBreakExpr _other         = False

isCallSite :: HsExpr GhcTc -> Bool
isCallSite HsApp{}     = True
isCallSite HsAppType{} = True
isCallSite OpApp{}     = True
isCallSite _ = False

addTickLHsExprOptAlt :: Bool -> LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTickLHsExprOptAlt oneOfMany (L pos e0)
  = ifDensity TickForCoverage
        (allocTickBox (ExpBox oneOfMany) False False pos $ addTickHsExpr e0)
        (addTickLHsExpr (L pos e0))

addBinTickLHsExpr :: (Bool -> BoxLabel) -> LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addBinTickLHsExpr boxLabel (L pos e0)
  = ifDensity TickForCoverage
        (allocBinTickBox boxLabel pos $ addTickHsExpr e0)
        (addTickLHsExpr (L pos e0))


-- -----------------------------------------------------------------------------
-- Decorate the body of an HsExpr with ticks.
-- (Whether to put a tick around the whole expression was already decided,
-- in the addTickLHsExpr family of functions.)

addTickHsExpr :: HsExpr GhcTc -> TM (HsExpr GhcTc)
addTickHsExpr e@(HsVar _ (L _ id)) = do freeVar id; return e
addTickHsExpr (HsUnboundVar {})    = panic "addTickHsExpr.HsUnboundVar"
addTickHsExpr e@(HsConLikeOut _ con)
  | Just id <- conLikeWrapId_maybe con = do freeVar id; return e
addTickHsExpr e@(HsIPVar {})       = return e
addTickHsExpr e@(HsOverLit {})     = return e
addTickHsExpr e@(HsOverLabel{})    = return e
addTickHsExpr e@(HsLit {})         = return e
addTickHsExpr (HsLam x matchgroup) = liftM (HsLam x)
                                           (addTickMatchGroup True matchgroup)
addTickHsExpr (HsLamCase x mgs)    = liftM (HsLamCase x)
                                           (addTickMatchGroup True mgs)
addTickHsExpr (HsApp x e1 e2)      = liftM2 (HsApp x) (addTickLHsExprNever e1)
                                                      (addTickLHsExpr      e2)
addTickHsExpr (HsAppType x e ty)   = liftM3 HsAppType (return x)
                                                      (addTickLHsExprNever e)
                                                      (return ty)

addTickHsExpr (OpApp fix e1 e2 e3) =
        liftM4 OpApp
                (return fix)
                (addTickLHsExpr e1)
                (addTickLHsExprNever e2)
                (addTickLHsExpr e3)
addTickHsExpr (NegApp x e neg) =
        liftM2 (NegApp x)
                (addTickLHsExpr e)
                (addTickSyntaxExpr hpcSrcSpan neg)
addTickHsExpr (HsPar x e) =
        liftM (HsPar x) (addTickLHsExprEvalInner e)
addTickHsExpr (SectionL x e1 e2) =
        liftM2 (SectionL x)
                (addTickLHsExpr e1)
                (addTickLHsExprNever e2)
addTickHsExpr (SectionR x e1 e2) =
        liftM2 (SectionR x)
                (addTickLHsExprNever e1)
                (addTickLHsExpr e2)
addTickHsExpr (ExplicitTuple x es boxity) =
        liftM2 (ExplicitTuple x)
                (mapM addTickTupArg es)
                (return boxity)
addTickHsExpr (ExplicitSum ty tag arity e) = do
        e' <- addTickLHsExpr e
        return (ExplicitSum ty tag arity e')
addTickHsExpr (HsCase x e mgs) =
        liftM2 (HsCase x)
                (addTickLHsExpr e) -- not an EvalInner; e might not necessarily
                                   -- be evaluated.
                (addTickMatchGroup False mgs)
addTickHsExpr (HsIf x cnd e1 e2 e3) =
        liftM3 (HsIf x cnd)
                (addBinTickLHsExpr (BinBox CondBinBox) e1)
                (addTickLHsExprOptAlt True e2)
                (addTickLHsExprOptAlt True e3)
addTickHsExpr (HsMultiIf ty alts)
  = do { let isOneOfMany = case alts of [_] -> False; _ -> True
       ; alts' <- mapM (liftL $ addTickGRHS isOneOfMany False) alts
       ; return $ HsMultiIf ty alts' }
addTickHsExpr (HsLet x (L l binds) e) =
        bindLocals (collectLocalBinders binds) $
          liftM2 (HsLet x . L l)
                  (addTickHsLocalBinds binds) -- to think about: !patterns.
                  (addTickLHsExprLetBody e)
addTickHsExpr (HsDo srcloc cxt (L l stmts))
  = do { (stmts', _) <- addTickLStmts' forQual stmts (return ())
       ; return (HsDo srcloc cxt (L l stmts')) }
  where
        forQual = case cxt of
                    ListComp -> Just $ BinBox QualBinBox
                    _        -> Nothing
addTickHsExpr (ExplicitList ty wit es) =
        liftM3 ExplicitList
                (return ty)
                (addTickWit wit)
                (mapM (addTickLHsExpr) es)
             where addTickWit Nothing = return Nothing
                   addTickWit (Just fln)
                     = do fln' <- addTickSyntaxExpr hpcSrcSpan fln
                          return (Just fln')

addTickHsExpr (HsStatic fvs e) = HsStatic fvs <$> addTickLHsExpr e

addTickHsExpr expr@(RecordCon { rcon_flds = rec_binds })
  = do { rec_binds' <- addTickHsRecordBinds rec_binds
       ; return (expr { rcon_flds = rec_binds' }) }

addTickHsExpr expr@(RecordUpd { rupd_expr = e, rupd_flds = flds })
  = do { e' <- addTickLHsExpr e
       ; flds' <- mapM addTickHsRecField flds
       ; return (expr { rupd_expr = e', rupd_flds = flds' }) }

addTickHsExpr (ExprWithTySig x e ty) =
        liftM3 ExprWithTySig
                (return x)
                (addTickLHsExprNever e) -- No need to tick the inner expression
                                        -- for expressions with signatures
                (return ty)
addTickHsExpr (ArithSeq ty wit arith_seq) =
        liftM3 ArithSeq
                (return ty)
                (addTickWit wit)
                (addTickArithSeqInfo arith_seq)
             where addTickWit Nothing = return Nothing
                   addTickWit (Just fl) = do fl' <- addTickSyntaxExpr hpcSrcSpan fl
                                             return (Just fl')

-- We might encounter existing ticks (multiple Coverage passes)
addTickHsExpr (HsTick x t e) =
        liftM (HsTick x t) (addTickLHsExprNever e)
addTickHsExpr (HsBinTick x t0 t1 e) =
        liftM (HsBinTick x t0 t1) (addTickLHsExprNever e)

addTickHsExpr (HsPragE _ HsPragTick{} (L pos e0)) = do
    e2 <- allocTickBox (ExpBox False) False False pos $
                addTickHsExpr e0
    return $ unLoc e2
addTickHsExpr (HsPragE x p e) =
        liftM (HsPragE x p) (addTickLHsExpr e)
addTickHsExpr e@(HsBracket     {})   = return e
addTickHsExpr e@(HsTcBracketOut  {}) = return e
addTickHsExpr e@(HsRnBracketOut  {}) = return e
addTickHsExpr e@(HsSpliceE  {})      = return e
addTickHsExpr (HsProc x pat cmdtop) =
        liftM2 (HsProc x)
                (addTickLPat pat)
                (liftL (addTickHsCmdTop) cmdtop)
addTickHsExpr (XExpr (HsWrap w e)) =
        liftM XExpr $
        liftM (HsWrap w)
              (addTickHsExpr e)        -- Explicitly no tick on inside

-- Others should never happen in expression content.
addTickHsExpr e  = pprPanic "addTickHsExpr" (ppr e)

addTickTupArg :: LHsTupArg GhcTc -> TM (LHsTupArg GhcTc)
addTickTupArg (L l (Present x e))  = do { e' <- addTickLHsExpr e
                                        ; return (L l (Present x e')) }
addTickTupArg (L l (Missing ty)) = return (L l (Missing ty))


addTickMatchGroup :: Bool{-is lambda-} -> MatchGroup GhcTc (LHsExpr GhcTc)
                  -> TM (MatchGroup GhcTc (LHsExpr GhcTc))
addTickMatchGroup is_lam mg@(MG { mg_alts = L l matches }) = do
  let isOneOfMany = matchesOneOfMany matches
  matches' <- mapM (liftL (addTickMatch isOneOfMany is_lam)) matches
  return $ mg { mg_alts = L l matches' }

addTickMatch :: Bool -> Bool -> Match GhcTc (LHsExpr GhcTc)
             -> TM (Match GhcTc (LHsExpr GhcTc))
addTickMatch isOneOfMany isLambda match@(Match { m_pats = pats
                                               , m_grhss = gRHSs }) =
  bindLocals (collectPatsBinders pats) $ do
    gRHSs' <- addTickGRHSs isOneOfMany isLambda gRHSs
    return $ match { m_grhss = gRHSs' }

addTickGRHSs :: Bool -> Bool -> GRHSs GhcTc (LHsExpr GhcTc)
             -> TM (GRHSs GhcTc (LHsExpr GhcTc))
addTickGRHSs isOneOfMany isLambda (GRHSs x guarded (L l local_binds)) = do
  bindLocals binders $ do
    local_binds' <- addTickHsLocalBinds local_binds
    guarded' <- mapM (liftL (addTickGRHS isOneOfMany isLambda)) guarded
    return $ GRHSs x guarded' (L l local_binds')
  where
    binders = collectLocalBinders local_binds

addTickGRHS :: Bool -> Bool -> GRHS GhcTc (LHsExpr GhcTc)
            -> TM (GRHS GhcTc (LHsExpr GhcTc))
addTickGRHS isOneOfMany isLambda (GRHS x stmts expr) = do
  (stmts',expr') <- addTickLStmts' (Just $ BinBox $ GuardBinBox) stmts
                        (addTickGRHSBody isOneOfMany isLambda expr)
  return $ GRHS x stmts' expr'

addTickGRHSBody :: Bool -> Bool -> LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTickGRHSBody isOneOfMany isLambda expr@(L pos e0) = do
  d <- getDensity
  case d of
    TickForCoverage  -> addTickLHsExprOptAlt isOneOfMany expr
    TickAllFunctions | isLambda ->
       addPathEntry "\\" $
         allocTickBox (ExpBox False) True{-count-} False{-not top-} pos $
           addTickHsExpr e0
    _otherwise ->
       addTickLHsExprRHS expr

addTickLStmts :: (Maybe (Bool -> BoxLabel)) -> [ExprLStmt GhcTc]
              -> TM [ExprLStmt GhcTc]
addTickLStmts isGuard stmts = do
  (stmts, _) <- addTickLStmts' isGuard stmts (return ())
  return stmts

addTickLStmts' :: (Maybe (Bool -> BoxLabel)) -> [ExprLStmt GhcTc] -> TM a
               -> TM ([ExprLStmt GhcTc], a)
addTickLStmts' isGuard lstmts res
  = bindLocals (collectLStmtsBinders lstmts) $
    do { lstmts' <- mapM (liftL (addTickStmt isGuard)) lstmts
       ; a <- res
       ; return (lstmts', a) }

addTickStmt :: (Maybe (Bool -> BoxLabel)) -> Stmt GhcTc (LHsExpr GhcTc)
            -> TM (Stmt GhcTc (LHsExpr GhcTc))
addTickStmt _isGuard (LastStmt x e noret ret) = do
        liftM3 (LastStmt x)
                (addTickLHsExpr e)
                (pure noret)
                (addTickSyntaxExpr hpcSrcSpan ret)
addTickStmt _isGuard (BindStmt xbs pat e) = do
        liftM4 (\b f -> BindStmt $ XBindStmtTc
                    { xbstc_bindOp = b
                    , xbstc_boundResultType = xbstc_boundResultType xbs
                    , xbstc_failOp = f
                    })
                (addTickSyntaxExpr hpcSrcSpan (xbstc_bindOp xbs))
                (mapM (addTickSyntaxExpr hpcSrcSpan) (xbstc_failOp xbs))
                (addTickLPat pat)
                (addTickLHsExprRHS e)
addTickStmt isGuard (BodyStmt x e bind' guard') = do
        liftM3 (BodyStmt x)
                (addTick isGuard e)
                (addTickSyntaxExpr hpcSrcSpan bind')
                (addTickSyntaxExpr hpcSrcSpan guard')
addTickStmt _isGuard (LetStmt x (L l binds)) = do
        liftM (LetStmt x . L l)
                (addTickHsLocalBinds binds)
addTickStmt isGuard (ParStmt x pairs mzipExpr bindExpr) = do
    liftM3 (ParStmt x)
        (mapM (addTickStmtAndBinders isGuard) pairs)
        (unLoc <$> addTickLHsExpr (L hpcSrcSpan mzipExpr))
        (addTickSyntaxExpr hpcSrcSpan bindExpr)
addTickStmt isGuard (ApplicativeStmt body_ty args mb_join) = do
    args' <- mapM (addTickApplicativeArg isGuard) args
    return (ApplicativeStmt body_ty args' mb_join)

addTickStmt isGuard stmt@(TransStmt { trS_stmts = stmts
                                    , trS_by = by, trS_using = using
                                    , trS_ret = returnExpr, trS_bind = bindExpr
                                    , trS_fmap = liftMExpr }) = do
    t_s <- addTickLStmts isGuard stmts
    t_y <- fmapMaybeM  addTickLHsExprRHS by
    t_u <- addTickLHsExprRHS using
    t_f <- addTickSyntaxExpr hpcSrcSpan returnExpr
    t_b <- addTickSyntaxExpr hpcSrcSpan bindExpr
    t_m <- fmap unLoc (addTickLHsExpr (L hpcSrcSpan liftMExpr))
    return $ stmt { trS_stmts = t_s, trS_by = t_y, trS_using = t_u
                  , trS_ret = t_f, trS_bind = t_b, trS_fmap = t_m }

addTickStmt isGuard stmt@(RecStmt {})
  = do { stmts' <- addTickLStmts isGuard (recS_stmts stmt)
       ; ret'   <- addTickSyntaxExpr hpcSrcSpan (recS_ret_fn stmt)
       ; mfix'  <- addTickSyntaxExpr hpcSrcSpan (recS_mfix_fn stmt)
       ; bind'  <- addTickSyntaxExpr hpcSrcSpan (recS_bind_fn stmt)
       ; return (stmt { recS_stmts = stmts', recS_ret_fn = ret'
                      , recS_mfix_fn = mfix', recS_bind_fn = bind' }) }

addTick :: Maybe (Bool -> BoxLabel) -> LHsExpr GhcTc -> TM (LHsExpr GhcTc)
addTick isGuard e | Just fn <- isGuard = addBinTickLHsExpr fn e
                  | otherwise          = addTickLHsExprRHS e

addTickApplicativeArg
  :: Maybe (Bool -> BoxLabel) -> (SyntaxExpr GhcTc, ApplicativeArg GhcTc)
  -> TM (SyntaxExpr GhcTc, ApplicativeArg GhcTc)
addTickApplicativeArg isGuard (op, arg) =
  liftM2 (,) (addTickSyntaxExpr hpcSrcSpan op) (addTickArg arg)
 where
  addTickArg (ApplicativeArgOne m_fail pat expr isBody) =
    ApplicativeArgOne
      <$> mapM (addTickSyntaxExpr hpcSrcSpan) m_fail
      <*> addTickLPat pat
      <*> addTickLHsExpr expr
      <*> pure isBody
  addTickArg (ApplicativeArgMany x stmts ret pat) =
    (ApplicativeArgMany x)
      <$> addTickLStmts isGuard stmts
      <*> (unLoc <$> addTickLHsExpr (L hpcSrcSpan ret))
      <*> addTickLPat pat

addTickStmtAndBinders :: Maybe (Bool -> BoxLabel) -> ParStmtBlock GhcTc GhcTc
                      -> TM (ParStmtBlock GhcTc GhcTc)
addTickStmtAndBinders isGuard (ParStmtBlock x stmts ids returnExpr) =
    liftM3 (ParStmtBlock x)
        (addTickLStmts isGuard stmts)
        (return ids)
        (addTickSyntaxExpr hpcSrcSpan returnExpr)

addTickHsLocalBinds :: HsLocalBinds GhcTc -> TM (HsLocalBinds GhcTc)
addTickHsLocalBinds (HsValBinds x binds) =
        liftM (HsValBinds x)
                (addTickHsValBinds binds)
addTickHsLocalBinds (HsIPBinds x binds)  =
        liftM (HsIPBinds x)
                (addTickHsIPBinds binds)
addTickHsLocalBinds (EmptyLocalBinds x)  = return (EmptyLocalBinds x)

addTickHsValBinds :: HsValBindsLR GhcTc (GhcPass a)
                  -> TM (HsValBindsLR GhcTc (GhcPass b))
addTickHsValBinds (XValBindsLR (NValBinds binds sigs)) = do
        b <- liftM2 NValBinds
                (mapM (\ (rec,binds') ->
                                liftM2 (,)
                                        (return rec)
                                        (addTickLHsBinds binds'))
                        binds)
                (return sigs)
        return $ XValBindsLR b
addTickHsValBinds _ = panic "addTickHsValBinds"

addTickHsIPBinds :: HsIPBinds GhcTc -> TM (HsIPBinds GhcTc)
addTickHsIPBinds (IPBinds dictbinds ipbinds) =
        liftM2 IPBinds
                (return dictbinds)
                (mapM (liftL (addTickIPBind)) ipbinds)

addTickIPBind :: IPBind GhcTc -> TM (IPBind GhcTc)
addTickIPBind (IPBind x nm e) =
        liftM2 (IPBind x)
                (return nm)
                (addTickLHsExpr e)

-- There is no location here, so we might need to use a context location??
addTickSyntaxExpr :: SrcSpan -> SyntaxExpr GhcTc -> TM (SyntaxExpr GhcTc)
addTickSyntaxExpr pos syn@(SyntaxExprTc { syn_expr = x }) = do
        x' <- fmap unLoc (addTickLHsExpr (L pos x))
        return $ syn { syn_expr = x' }
addTickSyntaxExpr _ NoSyntaxExprTc = return NoSyntaxExprTc

-- we do not walk into patterns.
addTickLPat :: LPat GhcTc -> TM (LPat GhcTc)
addTickLPat pat = return pat

addTickHsCmdTop :: HsCmdTop GhcTc -> TM (HsCmdTop GhcTc)
addTickHsCmdTop (HsCmdTop x cmd) =
        liftM2 HsCmdTop
                (return x)
                (addTickLHsCmd cmd)

addTickLHsCmd ::  LHsCmd GhcTc -> TM (LHsCmd GhcTc)
addTickLHsCmd (L pos c0) = do
        c1 <- addTickHsCmd c0
        return $ L pos c1

addTickHsCmd :: HsCmd GhcTc -> TM (HsCmd GhcTc)
addTickHsCmd (HsCmdLam x matchgroup) =
        liftM (HsCmdLam x) (addTickCmdMatchGroup matchgroup)
addTickHsCmd (HsCmdApp x c e) =
        liftM2 (HsCmdApp x) (addTickLHsCmd c) (addTickLHsExpr e)
{-
addTickHsCmd (OpApp e1 c2 fix c3) =
        liftM4 OpApp
                (addTickLHsExpr e1)
                (addTickLHsCmd c2)
                (return fix)
                (addTickLHsCmd c3)
-}
addTickHsCmd (HsCmdPar x e) = liftM (HsCmdPar x) (addTickLHsCmd e)
addTickHsCmd (HsCmdCase x e mgs) =
        liftM2 (HsCmdCase x)
                (addTickLHsExpr e)
                (addTickCmdMatchGroup mgs)
addTickHsCmd (HsCmdLamCase x mgs) =
        liftM (HsCmdLamCase x) (addTickCmdMatchGroup mgs)
addTickHsCmd (HsCmdIf x cnd e1 c2 c3) =
        liftM3 (HsCmdIf x cnd)
                (addBinTickLHsExpr (BinBox CondBinBox) e1)
                (addTickLHsCmd c2)
                (addTickLHsCmd c3)
addTickHsCmd (HsCmdLet x (L l binds) c) =
        bindLocals (collectLocalBinders binds) $
          liftM2 (HsCmdLet x . L l)
                   (addTickHsLocalBinds binds) -- to think about: !patterns.
                   (addTickLHsCmd c)
addTickHsCmd (HsCmdDo srcloc (L l stmts))
  = do { (stmts', _) <- addTickLCmdStmts' stmts (return ())
       ; return (HsCmdDo srcloc (L l stmts')) }

addTickHsCmd (HsCmdArrApp  arr_ty e1 e2 ty1 lr) =
        liftM5 HsCmdArrApp
               (return arr_ty)
               (addTickLHsExpr e1)
               (addTickLHsExpr e2)
               (return ty1)
               (return lr)
addTickHsCmd (HsCmdArrForm x e f fix cmdtop) =
        liftM4 (HsCmdArrForm x)
               (addTickLHsExpr e)
               (return f)
               (return fix)
               (mapM (liftL (addTickHsCmdTop)) cmdtop)

addTickHsCmd (XCmd (HsWrap w cmd)) =
  liftM XCmd $
  liftM (HsWrap w) (addTickHsCmd cmd)

-- Others should never happen in a command context.
--addTickHsCmd e  = pprPanic "addTickHsCmd" (ppr e)

addTickCmdMatchGroup :: MatchGroup GhcTc (LHsCmd GhcTc)
                     -> TM (MatchGroup GhcTc (LHsCmd GhcTc))
addTickCmdMatchGroup mg@(MG { mg_alts = (L l matches) }) = do
  matches' <- mapM (liftL addTickCmdMatch) matches
  return $ mg { mg_alts = L l matches' }

addTickCmdMatch :: Match GhcTc (LHsCmd GhcTc) -> TM (Match GhcTc (LHsCmd GhcTc))
addTickCmdMatch match@(Match { m_pats = pats, m_grhss = gRHSs }) =
  bindLocals (collectPatsBinders pats) $ do
    gRHSs' <- addTickCmdGRHSs gRHSs
    return $ match { m_grhss = gRHSs' }

addTickCmdGRHSs :: GRHSs GhcTc (LHsCmd GhcTc) -> TM (GRHSs GhcTc (LHsCmd GhcTc))
addTickCmdGRHSs (GRHSs x guarded (L l local_binds)) = do
  bindLocals binders $ do
    local_binds' <- addTickHsLocalBinds local_binds
    guarded' <- mapM (liftL addTickCmdGRHS) guarded
    return $ GRHSs x guarded' (L l local_binds')
  where
    binders = collectLocalBinders local_binds

addTickCmdGRHS :: GRHS GhcTc (LHsCmd GhcTc) -> TM (GRHS GhcTc (LHsCmd GhcTc))
-- The *guards* are *not* Cmds, although the body is
-- C.f. addTickGRHS for the BinBox stuff
addTickCmdGRHS (GRHS x stmts cmd)
  = do { (stmts',expr') <- addTickLStmts' (Just $ BinBox $ GuardBinBox)
                                   stmts (addTickLHsCmd cmd)
       ; return $ GRHS x stmts' expr' }

addTickLCmdStmts :: [LStmt GhcTc (LHsCmd GhcTc)]
                 -> TM [LStmt GhcTc (LHsCmd GhcTc)]
addTickLCmdStmts stmts = do
  (stmts, _) <- addTickLCmdStmts' stmts (return ())
  return stmts

addTickLCmdStmts' :: [LStmt GhcTc (LHsCmd GhcTc)] -> TM a
                  -> TM ([LStmt GhcTc (LHsCmd GhcTc)], a)
addTickLCmdStmts' lstmts res
  = bindLocals binders $ do
        lstmts' <- mapM (liftL addTickCmdStmt) lstmts
        a <- res
        return (lstmts', a)
  where
        binders = collectLStmtsBinders lstmts

addTickCmdStmt :: Stmt GhcTc (LHsCmd GhcTc) -> TM (Stmt GhcTc (LHsCmd GhcTc))
addTickCmdStmt (BindStmt x pat c) = do
        liftM2 (BindStmt x)
                (addTickLPat pat)
                (addTickLHsCmd c)
addTickCmdStmt (LastStmt x c noret ret) = do
        liftM3 (LastStmt x)
                (addTickLHsCmd c)
                (pure noret)
                (addTickSyntaxExpr hpcSrcSpan ret)
addTickCmdStmt (BodyStmt x c bind' guard') = do
        liftM3 (BodyStmt x)
                (addTickLHsCmd c)
                (addTickSyntaxExpr hpcSrcSpan bind')
                (addTickSyntaxExpr hpcSrcSpan guard')
addTickCmdStmt (LetStmt x (L l binds)) = do
        liftM (LetStmt x . L l)
                (addTickHsLocalBinds binds)
addTickCmdStmt stmt@(RecStmt {})
  = do { stmts' <- addTickLCmdStmts (recS_stmts stmt)
       ; ret'   <- addTickSyntaxExpr hpcSrcSpan (recS_ret_fn stmt)
       ; mfix'  <- addTickSyntaxExpr hpcSrcSpan (recS_mfix_fn stmt)
       ; bind'  <- addTickSyntaxExpr hpcSrcSpan (recS_bind_fn stmt)
       ; return (stmt { recS_stmts = stmts', recS_ret_fn = ret'
                      , recS_mfix_fn = mfix', recS_bind_fn = bind' }) }
addTickCmdStmt ApplicativeStmt{} =
  panic "ToDo: addTickCmdStmt ApplicativeLastStmt"

-- Others should never happen in a command context.
addTickCmdStmt stmt  = pprPanic "addTickHsCmd" (ppr stmt)

addTickHsRecordBinds :: HsRecordBinds GhcTc -> TM (HsRecordBinds GhcTc)
addTickHsRecordBinds (HsRecFields fields dd)
  = do  { fields' <- mapM addTickHsRecField fields
        ; return (HsRecFields fields' dd) }

addTickHsRecField :: LHsRecField' id (LHsExpr GhcTc)
                  -> TM (LHsRecField' id (LHsExpr GhcTc))
addTickHsRecField (L l (HsRecField id expr pun))
        = do { expr' <- addTickLHsExpr expr
             ; return (L l (HsRecField id expr' pun)) }


addTickArithSeqInfo :: ArithSeqInfo GhcTc -> TM (ArithSeqInfo GhcTc)
addTickArithSeqInfo (From e1) =
        liftM From
                (addTickLHsExpr e1)
addTickArithSeqInfo (FromThen e1 e2) =
        liftM2 FromThen
                (addTickLHsExpr e1)
                (addTickLHsExpr e2)
addTickArithSeqInfo (FromTo e1 e2) =
        liftM2 FromTo
                (addTickLHsExpr e1)
                (addTickLHsExpr e2)
addTickArithSeqInfo (FromThenTo e1 e2 e3) =
        liftM3 FromThenTo
                (addTickLHsExpr e1)
                (addTickLHsExpr e2)
                (addTickLHsExpr e3)

data TickTransState = TT { tickBoxCount:: Int
                         , mixEntries  :: [MixEntry_]
                         , ccIndices   :: CostCentreState
                         }

data TickTransEnv = TTE { fileName     :: FastString
                        , density      :: TickDensity
                        , tte_dflags   :: DynFlags
                        , exports      :: NameSet
                        , inlines      :: VarSet
                        , declPath     :: [String]
                        , inScope      :: VarSet
                        , blackList    :: Set RealSrcSpan
                        , this_mod     :: Module
                        , tickishType  :: TickishType
                        }

--      deriving Show

data TickishType = ProfNotes | HpcTicks | Breakpoints | SourceNotes
                 deriving (Eq)

coveragePasses :: DynFlags -> [TickishType]
coveragePasses dflags =
    ifa (hscTarget dflags == HscInterpreted) Breakpoints $
    ifa (gopt Opt_Hpc dflags)                HpcTicks $
    ifa (gopt Opt_SccProfilingOn dflags &&
         profAuto dflags /= NoProfAuto)      ProfNotes $
    ifa (debugLevel dflags > 0)              SourceNotes []
  where ifa f x xs | f         = x:xs
                   | otherwise = xs

-- | Tickishs that only make sense when their source code location
-- refers to the current file. This might not always be true due to
-- LINE pragmas in the code - which would confuse at least HPC.
tickSameFileOnly :: TickishType -> Bool
tickSameFileOnly HpcTicks = True
tickSameFileOnly _other   = False

type FreeVars = OccEnv Id
noFVs :: FreeVars
noFVs = emptyOccEnv

-- Note [freevars]
--   For breakpoints we want to collect the free variables of an
--   expression for pinning on the HsTick.  We don't want to collect
--   *all* free variables though: in particular there's no point pinning
--   on free variables that are will otherwise be in scope at the GHCi
--   prompt, which means all top-level bindings.  Unfortunately detecting
--   top-level bindings isn't easy (collectHsBindsBinders on the top-level
--   bindings doesn't do it), so we keep track of a set of "in-scope"
--   variables in addition to the free variables, and the former is used
--   to filter additions to the latter.  This gives us complete control
--   over what free variables we track.

newtype TM a = TM { unTM :: TickTransEnv -> TickTransState -> (a,FreeVars,TickTransState) }
    deriving (Functor)
        -- a combination of a state monad (TickTransState) and a writer
        -- monad (FreeVars).

instance Applicative TM where
    pure a = TM $ \ _env st -> (a,noFVs,st)
    (<*>) = ap

instance Monad TM where
  (TM m) >>= k = TM $ \ env st ->
                                case m env st of
                                  (r1,fv1,st1) ->
                                     case unTM (k r1) env st1 of
                                       (r2,fv2,st2) ->
                                          (r2, fv1 `plusOccEnv` fv2, st2)

instance HasDynFlags TM where
  getDynFlags = TM $ \ env st -> (tte_dflags env, noFVs, st)

-- | Get the next HPC cost centre index for a given centre name
getCCIndexM :: FastString -> TM CostCentreIndex
getCCIndexM n = TM $ \_ st -> let (idx, is') = getCCIndex n $
                                                 ccIndices st
                              in (idx, noFVs, st { ccIndices = is' })

getState :: TM TickTransState
getState = TM $ \ _ st -> (st, noFVs, st)

setState :: (TickTransState -> TickTransState) -> TM ()
setState f = TM $ \ _ st -> ((), noFVs, f st)

getEnv :: TM TickTransEnv
getEnv = TM $ \ env st -> (env, noFVs, st)

withEnv :: (TickTransEnv -> TickTransEnv) -> TM a -> TM a
withEnv f (TM m) = TM $ \ env st ->
                                 case m (f env) st of
                                   (a, fvs, st') -> (a, fvs, st')

getDensity :: TM TickDensity
getDensity = TM $ \env st -> (density env, noFVs, st)

ifDensity :: TickDensity -> TM a -> TM a -> TM a
ifDensity d th el = do d0 <- getDensity; if d == d0 then th else el

getFreeVars :: TM a -> TM (FreeVars, a)
getFreeVars (TM m)
  = TM $ \ env st -> case m env st of (a, fv, st') -> ((fv,a), fv, st')

freeVar :: Id -> TM ()
freeVar id = TM $ \ env st ->
                if id `elemVarSet` inScope env
                   then ((), unitOccEnv (nameOccName (idName id)) id, st)
                   else ((), noFVs, st)

addPathEntry :: String -> TM a -> TM a
addPathEntry nm = withEnv (\ env -> env { declPath = declPath env ++ [nm] })

getPathEntry :: TM [String]
getPathEntry = declPath `liftM` getEnv

getFileName :: TM FastString
getFileName = fileName `liftM` getEnv

isGoodSrcSpan' :: SrcSpan -> Bool
isGoodSrcSpan' pos@(RealSrcSpan _ _) = srcSpanStart pos /= srcSpanEnd pos
isGoodSrcSpan' (UnhelpfulSpan _) = False

isGoodTickSrcSpan :: SrcSpan -> TM Bool
isGoodTickSrcSpan pos = do
  file_name <- getFileName
  tickish <- tickishType `liftM` getEnv
  let need_same_file = tickSameFileOnly tickish
      same_file      = Just file_name == srcSpanFileName_maybe pos
  return (isGoodSrcSpan' pos && (not need_same_file || same_file))

ifGoodTickSrcSpan :: SrcSpan -> TM a -> TM a -> TM a
ifGoodTickSrcSpan pos then_code else_code = do
  good <- isGoodTickSrcSpan pos
  if good then then_code else else_code

bindLocals :: [Id] -> TM a -> TM a
bindLocals new_ids (TM m)
  = TM $ \ env st ->
                 case m env{ inScope = inScope env `extendVarSetList` new_ids } st of
                   (r, fv, st') -> (r, fv `delListFromOccEnv` occs, st')
  where occs = [ nameOccName (idName id) | id <- new_ids ]

isBlackListed :: SrcSpan -> TM Bool
isBlackListed (RealSrcSpan pos _) = TM $ \ env st -> (Set.member pos (blackList env), noFVs, st)
isBlackListed (UnhelpfulSpan _) = return False

-- the tick application inherits the source position of its
-- expression argument to support nested box allocations
allocTickBox :: BoxLabel -> Bool -> Bool -> SrcSpan -> TM (HsExpr GhcTc)
             -> TM (LHsExpr GhcTc)
allocTickBox boxLabel countEntries topOnly pos m =
  ifGoodTickSrcSpan pos (do
    (fvs, e) <- getFreeVars m
    env <- getEnv
    tickish <- mkTickish boxLabel countEntries topOnly pos fvs (declPath env)
    return (L pos (HsTick noExtField tickish (L pos e)))
  ) (do
    e <- m
    return (L pos e)
  )

-- the tick application inherits the source position of its
-- expression argument to support nested box allocations
allocATickBox :: BoxLabel -> Bool -> Bool -> SrcSpan -> FreeVars
              -> TM (Maybe (Tickish Id))
allocATickBox boxLabel countEntries topOnly  pos fvs =
  ifGoodTickSrcSpan pos (do
    let
      mydecl_path = case boxLabel of
                      TopLevelBox x -> x
                      LocalBox xs  -> xs
                      _ -> panic "allocATickBox"
    tickish <- mkTickish boxLabel countEntries topOnly pos fvs mydecl_path
    return (Just tickish)
  ) (return Nothing)


mkTickish :: BoxLabel -> Bool -> Bool -> SrcSpan -> OccEnv Id -> [String]
          -> TM (Tickish Id)
mkTickish boxLabel countEntries topOnly pos fvs decl_path = do

  let ids = filter (not . isUnliftedType . idType) $ occEnvElts fvs
          -- unlifted types cause two problems here:
          --   * we can't bind them  at the GHCi prompt
          --     (bindLocalsAtBreakpoint already filters them out),
          --   * the simplifier might try to substitute a literal for
          --     the Id, and we can't handle that.

      me = (pos, decl_path, map (nameOccName.idName) ids, boxLabel)

      cc_name | topOnly   = head decl_path
              | otherwise = concat (intersperse "." decl_path)

  dflags <- getDynFlags
  env <- getEnv
  case tickishType env of
    HpcTicks -> do
      c <- liftM tickBoxCount getState
      setState $ \st -> st { tickBoxCount = c + 1
                           , mixEntries = me : mixEntries st }
      return $ HpcTick (this_mod env) c

    ProfNotes -> do
      let nm = mkFastString cc_name
      flavour <- HpcCC <$> getCCIndexM nm
      let cc = mkUserCC nm (this_mod env) pos flavour
          count = countEntries && gopt Opt_ProfCountEntries dflags
      return $ ProfNote cc count True{-scopes-}

    Breakpoints -> do
      c <- liftM tickBoxCount getState
      setState $ \st -> st { tickBoxCount = c + 1
                           , mixEntries = me:mixEntries st }
      return $ Breakpoint c ids

    SourceNotes | RealSrcSpan pos' _ <- pos ->
      return $ SourceNote pos' cc_name

    _otherwise -> panic "mkTickish: bad source span!"


allocBinTickBox :: (Bool -> BoxLabel) -> SrcSpan -> TM (HsExpr GhcTc)
                -> TM (LHsExpr GhcTc)
allocBinTickBox boxLabel pos m = do
  env <- getEnv
  case tickishType env of
    HpcTicks -> do e <- liftM (L pos) m
                   ifGoodTickSrcSpan pos
                     (mkBinTickBoxHpc boxLabel pos e)
                     (return e)
    _other   -> allocTickBox (ExpBox False) False False pos m

mkBinTickBoxHpc :: (Bool -> BoxLabel) -> SrcSpan -> LHsExpr GhcTc
                -> TM (LHsExpr GhcTc)
mkBinTickBoxHpc boxLabel pos e =
 TM $ \ env st ->
  let meT = (pos,declPath env, [],boxLabel True)
      meF = (pos,declPath env, [],boxLabel False)
      meE = (pos,declPath env, [],ExpBox False)
      c = tickBoxCount st
      mes = mixEntries st
  in
     ( L pos $ HsTick noExtField (HpcTick (this_mod env) c)
          $ L pos $ HsBinTick noExtField (c+1) (c+2) e
   -- notice that F and T are reversed,
   -- because we are building the list in
   -- reverse...
     , noFVs
     , st {tickBoxCount=c+3 , mixEntries=meF:meT:meE:mes}
     )

mkHpcPos :: SrcSpan -> HpcPos
mkHpcPos pos@(RealSrcSpan s _)
   | isGoodSrcSpan' pos = toHpcPos (srcSpanStartLine s,
                                    srcSpanStartCol s,
                                    srcSpanEndLine s,
                                    srcSpanEndCol s - 1)
                              -- the end column of a SrcSpan is one
                              -- greater than the last column of the
                              -- span (see SrcLoc), whereas HPC
                              -- expects to the column range to be
                              -- inclusive, hence we subtract one above.
mkHpcPos _ = panic "bad source span; expected such spans to be filtered out"

hpcSrcSpan :: SrcSpan
hpcSrcSpan = mkGeneralSrcSpan (fsLit "Haskell Program Coverage internals")

matchesOneOfMany :: [LMatch GhcTc body] -> Bool
matchesOneOfMany lmatches = sum (map matchCount lmatches) > 1
  where
        matchCount :: LMatch GhcTc body -> Int
        matchCount (L _ (Match { m_grhss = GRHSs _ grhss _ }))
          = length grhss

type MixEntry_ = (SrcSpan, [String], [OccName], BoxLabel)

-- For the hash value, we hash everything: the file name,
--  the timestamp of the original source file, the tab stop,
--  and the mix entries. We cheat, and hash the show'd string.
-- This hash only has to be hashed at Mix creation time,
-- and is for sanity checking only.

mixHash :: FilePath -> UTCTime -> Int -> [MixEntry] -> Int
mixHash file tm tabstop entries = fromIntegral $ hashString
        (show $ Mix file tm 0 tabstop entries)

{-
************************************************************************
*                                                                      *
*              initialisation
*                                                                      *
************************************************************************

Each module compiled with -fhpc declares an initialisation function of
the form `hpc_init_<module>()`, which is emitted into the _stub.c file
and annotated with __attribute__((constructor)) so that it gets
executed at startup time.

The function's purpose is to call hs_hpc_module to register this
module with the RTS, and it looks something like this:

static void hpc_init_Main(void) __attribute__((constructor));
static void hpc_init_Main(void)
{extern StgWord64 _hpc_tickboxes_Main_hpc[];
 hs_hpc_module("Main",8,1150288664,_hpc_tickboxes_Main_hpc);}
-}

hpcInitCode :: Module -> HpcInfo -> SDoc
hpcInitCode _ (NoHpcInfo {}) = Outputable.empty
hpcInitCode this_mod (HpcInfo tickCount hashNo)
 = vcat
    [ text "static void hpc_init_" <> ppr this_mod
         <> text "(void) __attribute__((constructor));"
    , text "static void hpc_init_" <> ppr this_mod <> text "(void)"
    , braces (vcat [
        text "extern StgWord64 " <> tickboxes <>
               text "[]" <> semi,
        text "hs_hpc_module" <>
          parens (hcat (punctuate comma [
              doubleQuotes full_name_str,
              int tickCount, -- really StgWord32
              int hashNo,    -- really StgWord32
              tickboxes
            ])) <> semi
       ])
    ]
  where
    tickboxes = ppr (mkHpcTicksLabel $ this_mod)

    module_name  = hcat (map (text.charToC) $ BS.unpack $
                         bytesFS (moduleNameFS (moduleName this_mod)))
    package_name = hcat (map (text.charToC) $ BS.unpack $
                         bytesFS (unitFS  (moduleUnit this_mod)))
    full_name_str
       | moduleUnit this_mod == mainUnitId
       = module_name
       | otherwise
       = package_name <> char '/' <> module_name
