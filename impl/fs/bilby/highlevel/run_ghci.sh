#!/bin/sh

# we don't do it anymore
### # TODO: run hsc2hs first to generate FFI.hs

# we need to install `derive' and put it in $PATH

ghci-8.0.1 -i../proof/spec -i../highlevel -i../../../../cogent/lib/gum/common -package=extra -package=QuickCheck -Wno-partial-type-signatures -package-db=.cabal-sandbox/x86_64-linux-ghc-8.0.1-packages.conf.d/ ../cogent/fsm_example/build/fsm_wrapper_pp_inferred.o fsm.hs 
