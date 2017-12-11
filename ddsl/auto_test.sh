#!/bin/sh


for t in `find ./tests -name *ddsl -not -type d -print`
do
  echo "========================== $t ================================"
  ./dist/build/ddsl/ddsl $1 $t
done
