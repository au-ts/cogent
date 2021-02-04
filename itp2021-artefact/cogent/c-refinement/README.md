
# C-Refinement Proofs

These proofs are currently being updated

## Proof Dependencies

These proofs depend on the Cogent Type-system proofs, and AutoCorres.

```
file                                    depends on
├── Cogent_C_Heap_Auto.thy              (Read_Table)
├── Cogent_C_Val_Auto.thy               (Value_Relation_Generation, Type_Relation_Generation)
├── Cogent_Corres_Sanity_Check.thy
├── Cogent_Corres_Shallow_C.thy         (Deep_Embedding_Auto, Cogent_Corres, Corres_Tac, TypeProofGen, Tidy)
├── Cogent_Corres.thy                   (Value_Relation)
├── CogentHigherOrder.thy               (TypeProofGen)
├── Corres_Tac.thy                      (Cogent_Corres, Value_Relation_Generation)
├── Deep_Embedding_Auto.thy             (Specialised_Lemma, Cogent_C_Val_Auto, Cogent_C_Heap_Auto, Heap_Relation_Generation)
├── Heap_Relation_Generation.thy        (Read_Table)
├── Read_Table.thy                      (Specialised_Lemma_Utils)
├── SpecialisedLemmaTactic.thy          (Cogent_Corres, Specialised_Lemma_Utils)
├── Specialised_Lemma.thy               (Read_Table, SpecialisedLemmaTactic)
├── Specialised_Lemma_URecord.thy       (Read_Table, SpecialisedLemmaTactic)
├── Specialised_Lemma_USum.thy          (Read_Table, SpecialisedLemmaTactic)
├── Specialised_Lemma_Utils.thy         (Utils)
├── Tidy.thy
├── Type_Relation_Generation.thy        (Cogent_Corres, Read_Table)
├── TypeProofGen.thy
├── Utils.thy
├── Value_Relation_Generation.thy       (Cogent_Corres, Specialised_Lemma_Utils)
└── Value_Relation.thy                  
```
