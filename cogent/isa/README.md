
# Isabelle Proofs

## Status

The proofs are in the middle of being updated.

This is the status of the proofs at the moment:
```
file                                    depends on                    status
├── AssocLookup.thy                                                   [good]
├── Cogent.thy                                                        [good]
├── CogentHelper.thy                    (TypeTrackingSemantics)       [good]
├── Correspondence.thy                  (UpdateSemantics)             [good]
├── Mono.thy                            (ValueSemantics)              [good]
├── Mono_Tac.thy                        (Mono,AssocLookup)            [good]
├── ProofTrace.thy                                                    [broken]
├── StringMap.thy                       (StaticFun)                   [good]
├── TypeProofTest.thy                   (CogentHelper,ProofTrace)     [broken]
├── TypeTrackingSemantics.thy           (UpdateSemantics)             [good]
├── UpdateSemantics.thy                 (ValueSemantics,Cogent)       [good]
├── Util.thy                                                          [good]
├── ValueSemantics.thy                  (Cogent)                      [good]
└── shallow
    ├── Shallow.thy                     (ValueSemantics,Util)         [broken]
    ├── ShallowTuples.thy               (Util)                        [good]
    ├── Shallow_Normalisation_Tac.thy   (Util)                        [broken]
    └── Shallow_Tac.thy                 (Shallow)                     [broken]
```
