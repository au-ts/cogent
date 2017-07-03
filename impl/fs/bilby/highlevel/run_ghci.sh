#!/bin/sh

# TODO: run hsc2hs first to generate FFI.hs
ghci -i../proof/spec -i../../../../cogent/lib/gum/common -package=extra -package=QuickCheck -Wpartial-type-signatures 
