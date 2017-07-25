#!/bin/sh

# we don't do it anymore
### # TODO: run hsc2hs first to generate FFI.hs

# we need to install `derive' and put it in $PATH
PATH="`pwd`/../.cabal-sandbox/bin:$PATH"

# make o-gen V=1

ghci-8.0.1 -i../../proof/spec -i../ -package=extra -package=QuickCheck -Wno-partial-type-signatures -package-db=../.cabal-sandbox/x86_64-linux-ghc-8.0.1-packages.conf.d/ build/wa.o WordArray.hs 

