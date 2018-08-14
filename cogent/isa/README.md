
# Isabelle Proofs

## Proof Dependencies

```
file                                    depends on
├── AssocLookup.thy
├── Cogent.thy
├── CogentHelper.thy                    (TypeTrackingSemantics,ML_Old)
├── Correspondence.thy                  (UpdateSemantics)
├── ML_Old.thy
├── Mono.thy                            (ValueSemantics)
├── Mono_Tac.thy                        (Mono,AssocLookup)
├── ProofTrace.thy                      (ML_Old)
├── StringMap.thy                       (StaticFun)
├── TypeProofTest.thy                   (CogentHelper,ProofTrace,ML_Old)
├── TypeTrackingSemantics.thy           (UpdateSemantics)
├── UpdateSemantics.thy                 (ValueSemantics,Cogent)
├── Util.thy
├── ValueSemantics.thy                  (Cogent)
└── shallo
    ├── Shallow.thy                     (ValueSemantics,Util)
    ├── ShallowTuples.thy               (Util)
    ├── Shallow_Normalisation_Tac.thy   (Util)
    └── Shallow_Tac.thy                 (Shallow)
```
