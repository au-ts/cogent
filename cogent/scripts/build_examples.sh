#!/bin/bash

cd "$(dirname "${BASH_SOURCE[0]}")"

#Directories
COGENTDIR=../
TLD=../../
EXAMPLEDIR=$COGENTDIR/examples

source $TLD/build-env.sh || exit


if [[ $# > 1 ]]; then 
  echo "Usage: build_example.sh [ARG]" && exit 1 
fi

ARG=
if [[ -n $1 ]]; then
  ARG=$1
fi

cd $EXAMPLEDIR

for ex in */
do
  pushd $ex
  make $ARG
  popd
done
