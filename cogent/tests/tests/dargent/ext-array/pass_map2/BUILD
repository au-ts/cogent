#!/bin/bash


cogent -g pass_map2.cogent && \
gcc -g -O2 pass_map2_main.c -I. -I../../../lib/ -std=gnu99 -o pass_map2 && \
./pass_map2

if [[ $# -lt 1 || $1 != '--no-rm' ]]; then
 rm -f pass_map2.h pass_map2.c pass_map2
fi


