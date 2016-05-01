#!/bin/bash
#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

# 7.8.3 doesn't work well any longer
# 7.8.4 is the default compiler, so not tested here
# The following are the 'extra' versions that we support
GHC_VERSIONS=('7.10.1' '7.10.2' '7.10.3')
UNAME=`uname | tr [A-Z] [a-z]`
ARCH="`arch`-${UNAME}"

declare -i tests=0 passed=0

echo `cabal --version`

echo "\$PATH is $PATH"

for i in ${GHC_VERSIONS[@]}; do
  tests+=1
  echo "***** Compiling with GHC ${i} *****" 

  if ! which "ghc-${i}"; then 
    echo "ghc-${i} not found, skip!"
    continue
  fi

  export GHC="ghc-${i}"
  export HC_PKG="ghc-pkg-${i}"
  export DIST="dist-${i}"
  export ARCH="$ARCH"
  export GHC_VER="${i}"
  export PACKAGE_DB=".cabal-sandbox/${ARCH}-${GHC}-packages.conf.d"

  # check if the new dep is the same as old
  cabal install --upgrade-dependencies --dry-run --only-dependencies \
                --with-compiler="ghc-${i}" --with-hc-pkg="ghc-pkg-${i}" \
                --package-db="$PACKAGE_DB" > "$0.tmp"
  if grep -q "^All the requested packages are already installed:" "$0.tmp"  # nothing changed
    then cabal install --upgrade-dependencies \
           --with-compiler="ghc-${i}" --with-hc-pkg="ghc-pkg-${i}" --package-db=$PACKAGE_DB
         if [[ $? -eq 0 ]]; then
           echo "PASSED with GHC ${i} without changes"
           passed+=1
           echo -n
           continue
         fi
  fi
  
  # if dep changed, or unchanged but installation failed, then redo from scratch
  ./validate.sh -update-cabal # -keep-sandbox
  if [[ $? -eq 0 ]]; then 
    echo "PASSED with GHC ${i} with changes"
    passed+=1
  else
    echo "FAILED with GHC ${i}"
  fi
  echo -n
done

rm -f "$0.tmp"

echo "$passed out of $tests tests passed!"

if [[ $passed -lt $tests ]]; then
  exit 1
fi

