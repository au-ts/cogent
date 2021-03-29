From Coq Require Import ExtrHaskellString ExtrHaskellZInteger.

From Checker Require Import Compiler.

Extraction Language Haskell.

Extraction "extracted/Compiler.hs" compile_cogent.
