#!/bin/bash

make && ./ffi-gen
if [ $? -eq 42 ]; then 
  result=0
else
  result=1
fi
make clean && exit $result
