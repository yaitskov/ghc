#!/bin/bash

# This is the primary driver of the Win32 CI infrastructure.

set -e

case $MSYSTEM in
  MINGW32)
    triple="i386-unknown-mingw32"
    cabal_arch="i386"
    ;;
  MINGW64)
    triple="x86_64-unknown-mingw32"
    cabal_arch="x86_64"
    ;;
  *)
    echo "win32-init: Unknown MSYSTEM $MSYSTEM"
    exit 1
    ;;
esac

# Bring mingw64 toolchain into PATH
source /etc/profile

# This will contain GHC's local native toolchain
toolchain="$PWD/toolchain"
PATH="$toolchain/bin:$PATH"

# Use a local temporary directory to ensure that concurrent builds don't
# interfere with one another
mkdir -p tmp
export TMP=$PWD/tmp
export TEMP=$PWD/tmp

# Extract GHC toolchain
setup() {
  if [ -d "`pwd`/cabal-cache" ]; then
      cp -Rf cabal-cache $APPDATA/cabal
  fi

  if [ ! -e $toolchain/bin/ghc ]; then
      curl https://downloads.haskell.org/~ghc/$GHC_VERSION/ghc-$GHC_VERSION-$triple.tar.xz | tar -xJ
      mv ghc-$GHC_VERSION toolchain
  fi

  if [ ! -e $toolchain/bin/cabal ]; then
      url="https://downloads.haskell.org/~cabal/cabal-install-2.4.1.0/cabal-install-2.4.1.0-$cabal_arch-unknown-mingw32.zip"
      curl $url > /tmp/cabal.zip
      unzip /tmp/cabal.zip
      mv cabal.exe $toolchain/bin
  fi

  if [ ! -e $toolchain/bin/happy ]; then
      cabal update
      cabal install happy
      cp $APPDATA/cabal/bin/happy $toolchain/bin
  fi

  if [ ! -e $toolchain/bin/alex ]; then
      cabal update
      cabal install alex
      cp $APPDATA/cabal/bin/alex $toolchain/bin
  fi
}

configure() {
  python boot
  ./configure \
    --enable-tarballs-autodownload \
    GHC=$toolchain/bin/ghc \
    HAPPY=$toolchain/bin/happy \
    ALEX=$toolchain/bin/alex
}

build_make() {
  echo "include mk/flavours/${BUILD_FLAVOUR}.mk" > mk/build.mk
  echo 'GhcLibHcOpts+=-haddock' >> mk/build.mk
  make -j`mk/detect-cpu-count.sh`
  mv _build/bindist/ghc*.tar.xz ghc.tar.xz
}

test_make() {
  make binary-dist-prep TAR_COMP_OPTS=-1
  make test_bindist TEST_PREP=YES
  make V=0 test \
    THREADS=`mk/detect-cpu-count.sh` \
    JUNIT_FILE=../../junit.xml
}

build_hadrian() {
  hadrian/build.cabal.sh \
    --flavour=$FLAVOUR \
    -j`mk/detect-cpu-count.sh` \
    --flavour=Quick \
    --docs=no-sphinx \
    binary-dist

  mv _build/bindist/ghc*.tar.xz ghc.tar.xz
}

test_hadrian() {
  export TOP=$(pwd)
  cd _build/bindist/ghc-*/
  ./configure --prefix=$TOP/_build/install
  make install
  cd ../../../

  # skipping perf tests for now since we build a quick-flavoured GHC,
  # which might result in some broken perf tests?
  hadrian/build.cabal.sh \
    --flavour=$FLAVOUR \
    -j`mk/detect-cpu-count.sh` \
    --flavour=quick \
    test \
    --summary-junit=./junit.xml \
    --skip-perf \
    --test-compiler=$TOP/_build/install/bin/ghc
}

case $1 in
  setup) setup ;;
  configure) configure ;;
  build_make) build_make ;;
  test_make) test_make ;;
  build_hadrian) build_hadrian ;;
  test_hadrian) test_hadrian ;;
  *)
    echo "unknown mode $1"
    exit 1 ;;
esac
