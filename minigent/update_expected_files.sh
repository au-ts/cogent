#!/bin/bash
stack test --no-run-tests --verbosity warn
TEST_BIN=`stack path --dist-dir`/build/minigent-test/minigent-test
EXAMPLES=`find examples | grep 'in.minigent$' | xargs -L 1 dirname | sort`
for i in $EXAMPLES; do
  $TEST_BIN update-expected $i
done
