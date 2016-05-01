#!/bin/sh
#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

TESTS=./tests
INC=./tests/include

for source in "$TESTS"/pass_*.cogent
do
  out=$INC/$(basename "$source" .cogent)_dummy.h
  egrep "^type +([A-Z][a-zA-Z0-9_']*)( [a-z][a-zA-Z0-9_']*)* *$" "$source" | \
  sed -e "s/type \([A-Z][a-zA-Z0-9_']*\).*$/typedef void* \1;/" >"$out"
done
