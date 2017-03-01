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

code=0
TEST_FILE=_regression.cogent

cd "$(dirname "${BASH_SOURCE[0]}")"
source ../../../build-env.sh

# ensure set
shopt -s globstar

# since some libgum stuff depends on this type
echo $'type FsInode\ntype FsState\n_COGENT_LOG_LEVEL: U32\n_COGENT_LOG_LEVEL = 0' > "$TEST_FILE"

flist=`find . -name *.cogent`
# include everything
for src in $flist
do
  echo "include \"$src\"" >> "$TEST_FILE"
done

# typecheck, and save result
cogent -t "$TEST_FILE"
code=$?

rm "$TEST_FILE"

if ! [ $code -eq 0 ]; then
	echo "!! libgum failed"
	exit $code
fi

echo "!! libgum okay, checking examples"

# and try to typecheck examples, currently no examples
# for src in examples/*.cogent
# do
# 	if ! cogent -t $src; then
# 		code=$?
# 	fi
# done
# 
# if ! [ $code -eq 0 ]; then
# 	echo "!! examples failed"
# 	exit $code
# else
# 	echo "!! examples okay"
# fi
