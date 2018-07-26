
# Isabelle Proofs

## Status

The proofs are in the middle of being updated.

This is the status of the proofs at the moment:
```
file                                    depends on                    status
├── AssocLookup.thy                                                   [broken]
├── Cogent.thy                                                        [good]
├── CogentHelper.thy                    (TypeTrackingSemantics)       [broken]
├── Correspondence.thy                  (UpdateSemantics)             [broken]
├── Focus.thy                                                         [broken]
├── Mono.thy                            (ValueSemantics)              [broken]
├── Mono_Tac.thy                        (Mono,AssocLookup)            [broken]
├── ProofTrace.thy                                                    [broken]
├── StringMap.thy                       (StaticFun)                   [broken]
├── TypeProofTest.thy                   (CogentHelper,ProofTrace)     [broken]
├── TypeTrackingSemantics.thy           (UpdateSemantics,Focus)       [in progress]
├── UpdateSemantics.thy                 (ValueSemantics,Cogent)       [good]
├── Util.thy                                                          [good]
├── ValueSemantics.thy                  (Cogent)                      [good]
└── shallow
    ├── Shallow.thy                     (ValueSemantics,Util)         [broken]
    ├── ShallowTuples.thy               (Util)                        [good]
    ├── Shallow_Normalisation_Tac.thy   (Util)                        [broken]
    └── Shallow_Tac.thy                 (Shallow)                     [broken]
```