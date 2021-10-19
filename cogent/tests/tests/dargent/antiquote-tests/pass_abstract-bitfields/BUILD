#!/bin/bash

make
make manual

if [[ $? -eq 0 ]]; then
  ./bitfields > bitfields.out.1
  ./bitfields-manual > bitfields.out.2
  result=`diff bitfields.out.[12]`
fi

make clean
rm bitfields.out.[12]

exit $result
