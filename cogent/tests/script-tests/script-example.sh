#!/bin/bash

mkdir -p temporary

echo "Some test" > temporary/out.txt

LEN=`wc -c temporary/out.txt | cut -d' ' -f1`

if [[ $LEN -eq 10 ]];
then
    echo "Passed!"
    rm -rf temporary
    exit 0
else
    echo "Failed!"    
    rm -rf temporary
    exit 1
fi
