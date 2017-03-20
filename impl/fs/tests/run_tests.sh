#!/bin/bash
set -e
if [ "$#" -ne 2 ]; then
	echo "Usage: ./run_scripts <fstype1> <fstype2>"
	exit 1
fi

if [ "$UID" -ne 0 ]; then
	echo "Must be run as root."
	exit 1
fi

cd scripts
num_scripts=$(expr `ls -l | wc -l` - 1)

count=0
fail=0
pass=0

for script in *
do
	rm -rf ../new.txt ../orig.txt
	((++count))
	echo "Test $count/$num_scripts ($script)..."
	./$script $1 new.txt
	./$script $2 orig.txt
	DIFF=$(diff ../new.txt ../orig.txt)
	if [ "$DIFF" != "" ]
	then
		echo "-> Test failed."
		((++fail))
		echo $DIFF
	else
		echo "-> Test passed."
		((++pass))
	fi
	rm -f ../new.txt ../orig.txt
done

echo -e "\n$pass/$count tests passed."
