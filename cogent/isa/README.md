
# Typesystem Proofs

These proofs are about the Cogent type-system, and it's semantics.

## Proof Dependencies

```
file                                    depends on
├── AssocLookup.thy
├── Cogent.thy                          (Util)
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
└── shallow
    ├── Shallow.thy                     (ValueSemantics,ShallowUtil)
    ├── ShallowTuples.thy               (ShallowUtil)
    ├── Shallow_Normalisation_Tac.thy   (ShallowUtil)
    ├── ShallowUtil.thy
    └── Shallow_Tac.thy                 (Shallow)
```
