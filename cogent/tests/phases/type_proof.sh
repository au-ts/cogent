#!/usr/bin/env bash

#
# type-proof COGENT_FILE
#
# Expects the env vars
#   COGENT_PATH
#

echo $(pwd)

if [ $# -ne 1 ]; then
  echo "USAGE:"
  echo "  type_proof.sh COGENT_FILE"
  exit 1
fi

if [ ! -z "$COGENT_REPO" ]; then
  if [ ! -d "$COGENT_REPO" ]; then
    echo "error: '$COGENT_REPO' is not a directory"
    exit 1
  fi
else
  echo "type_proof.sh requires COGENT_REPO"
  exit 1
fi

COGENT_REPO=${COGENT_REPO%/}

COGENT=cogent
if [ ! -f cogent ]; then
  COGENT=$HOME/.cabal/bin/cogent
fi

ISABELLE=$COGENT_REPO/isabelle/bin/isabelle
AC_DIR=$COGENT_REPO/autocorres

if [ ! -f "$COGENT" ]; then
  echo "error: could not find cogent"
  exit 1
fi
if [ ! -f "$ISABELLE" ]; then
  echo "error: could not find isabelle"
  exit 1
fi
if [ ! -d "$AC_DIR" ]; then
  echo "error: could not find autocorres"
  exit 1
fi
if [ -z "$TEST_DIST_DIR" ]; then
  TEST_DIST_DIR=testing_tmp
fi

FILE=$1
TEST_NAME_BASE=Test

$COGENT -o $TEST_NAME_BASE --dist-dir $TEST_DIST_DIR --type-proof $FILE

if [ ! $? ]; then
  echo "error: cogent failed!"
  exit 1
fi

cat > $TEST_DIST_DIR/ROOT <<EOF
session Test_TypeProof = CogentCRefinement +
  theories
    "Test_TypeProof"
EOF

if [ -z $L4V_ARCH ]; then
  export L4V_ARCH=ARM
fi

$ISABELLE build -d $COGENT_REPO -d $AC_DIR -d $TEST_DIST_DIR ${TEST_NAME_BASE}_TypeProof
