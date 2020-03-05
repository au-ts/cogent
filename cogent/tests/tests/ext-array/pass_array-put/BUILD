#!/bin/bash

cogent -g put.cogent -o pass_array-put && \
gcc -g -O2 main.c -I. -I../../../lib/ -std=gnu99 -o pass_array-put && \
./pass_array-put > actual.out && \
diff expected.out actual.out
result=$?

if [[ $# -lt 1 || $1 != '--no-rm' ]]; then
 rm -f pass_array-put.[ch] pass_array-put actual.out
fi

if [ $result -ne 0 ]; then
     exit 1
fi

