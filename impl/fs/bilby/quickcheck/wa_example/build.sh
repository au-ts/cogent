#!/bin/sh

# we need to install `derive' and put it in $PATH
PATH="`pwd`/../.cabal-sandbox/bin:$PATH"

make V=1

hsc2hs Wa_FFI_Types_Abs.hsc -I. -I`cogent --stdgum-dir` -o build/Wa_FFI_Types_Abs.hs
hsc2hs build/Wa_FFI_Types.hsc -I. -I./build -I`cogent --stdgum-dir`

cabal v1-repl --ghc-options="-i../ -i./build/ -i. -Wno-partial-type-signatures  build/wa.o WordArray.hs"
