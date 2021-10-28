#!/bin/bash

make
./flexible > out.actual
diff out.actual out.expected
result=$?
make clean
rm out.actual
exit $result

