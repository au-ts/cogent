#!/bin/sh

# TODO: run hsc2hs first to generate FFI.hs
ghci -i../proof/spec -i../../../../cogent/lib/gum/common -package=extra -package=QuickCheck -Wno-partial-type-signatures -package-db=.cabal-sandbox/x86_64-linux-ghc-8.0.1-packages.conf.d/
