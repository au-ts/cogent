From Coq Require Import ExtrHaskellString ExtrHaskellZInteger ExtrHaskellNatInt.

From Checker Require Import Compiler Denotation.

Extraction Language Haskell.

Extraction "extracted/Compiler.hs" compile_cogent run_cogent.
