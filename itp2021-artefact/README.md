# ARTIFACT

[ITP 2021 Artefact](https://github.com/NICTA/cogent/tree/wordarray-example/itp2021-artefact)
---

## Sum Example

### Important Files

* _Sum.cogent_: Contains the Cogent program for sum and other functions.
* _wordarray.cogent_: Cogent declarations for word arrays and its operations.
* _wordarray.ac_: Antiquoted C definitions of the word array operations.
* _WordArray.ah_: Antiquoted C definition of word arrays.
* _main.ac_: Main "program".
* _main\_pp\_inferred.c_: Contains the generated C from the main program.
* _Sum\_AllRefine.thy_: Contains the shallow to C refinement proof and functional correctness proof.
* _WordArray\_Abstractions.thy_: Contains the value typing for word arrays, the value relation between update and value for word arrays,
  and the proof that word arrays adhere to the FFI constraints, i.e. the locale constraints.
* _WordArray\_Shallow.thy_: Contains the shallow embedding for word array operations.
* _WordArray\_Value.thy_: Contains both the polymorphic and monomorphic embedding of word array operations in the value semantics, and the proofs for type preservation and monomorphisation.
* _WordArray\_Update.thy_: Contains the embedding of word array operations in the update semantics, and the type preservation and frame constraint proofs.
* _WordArray\_VAbsFun.thy_: Contains the function that maps the name of word array operations to their embedding in the value semantics. 
* _WordArray\_UAbsFun,thy_: Contains the function that maps the name of word array operations to their embedding in the update semantics. 
* _WordArray\_SVCorres.thy_: Contains the shallow to value refinement proofs for the word array operations.
* _WordArray\_UpdCCorres.thy_: Contains the update to C refinement proofs for the word array operations.
* _WordArray\_CorresProof_Asm.thy_: Contains the value to update refinement proofs for the word array operations, and other assumptions.

### Running the Sum Example

This formalisation works with Isabele2019. 
First extract the **autocorres.tar.gz** located in the top **cogent** folder.
Install AutoCorres for 32-bit architecture, i.e. ARM, following the instructions located in the **autocorres** folder.

To run the example, go into the **sum-example** folder and use the command:

`$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres -d . -l AutoCorres Sum_AllRefine.thy`

### Running the Sum Example Manually

Note that if you wish to build from source, you will need to download the Cogent compiler from the branch **wordarray-example**.
Then inside of the **sum-example-manual** folder, run

`$ make`

and then

`$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres -d . -l AutoCorres Sum_AllRefine.thy`

---

## BilbyFS Functional Correctness Proofs

### Important Files
* _WordArrayT.thy_: The axiomatization of word arrays in located here.
* _WordArray\_Shallow.thy_: The shallow embedding of word arrays used in Bilby is in here, minor differences to the one used to sum example since the types are named differently, the shallow for wordarray_get has undefined behaviour when accessing an element out of bounds.
* _FsopIgetR.thy_: Contains the functional correctness proof for the iget operation.
* _FsopSyncR.tny_: Contains the functional correctness proof for the sync operation.
* _AfsS.thy_: Contains the functional correctness specifications.

### Running the BilbyFS Functional Correctness Proofs

To build the proofs without launching jedit, run

`$ make iget`

or

`$ make sync`

in the directory **bilby** and these will make the proofs for *iget* and *sync* respectively.

To launch with jedit run

`$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres -d . -l AutoCorres refine/FsopIgetR.thy`

or

`$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres -d . -l AutoCorres refine/FsopSyncR.thy`

___

## Directory Structure

.  
├── bilby  
│   ├── adt  
│   │   ├── ...  
│   │   ├── WordArray_Shallow.thy  
│   │   └── WordArrayT.thy  
│   ├── impl  
│   │   └── ...  
│   ├── lib  
│   │   └── ...  
│   ├── Makefile  
│   ├── refine  
│   │   ├── ...  
│   │   ├── FsopIgetR.thy  
│   │   └── FsopSyncR.thy  
│   ├── ROOT  
│   └── spec  
│       ├── ..  
│       └── AfsS.thy  
├── cogent  
│   ├── autocorres.tar.gz  
│   ├── cogent  
│   │   └── ...  
│   ├── c-refinement  
│   │   └── ...  
│   └── ROOTS  
├── README.md  
├── sum-example  
│   ├── ...  
│   ├── main.ac  
│   ├── main_pp_inferred.c  
│   ├── ROOT  
│   ├── Sum_AllRefine.thy  
│   ├── Sum.cogent  
│   ├── WordArray_Abstractions.thy  
│   ├── wordarray.ac  
│   ├── WordArray.ah  
│   ├── wordarray.cogent  
│   ├── WordArray_CorresProof_Asm.thy  
│   ├── WordArray_Shallow.thy  
│   ├── WordArray_SVCorres.thy  
│   ├── WordArray_UAbsFun.thy  
│   ├── WordArray_Update.thy  
│   ├── WordArray_UpdCCorres.thy  
│   ├── WordArray_VAbsFun.thy  
│   └── WordArray_Value.thy  
└── sum-example-manual  
    ├── ...  
    └── Makefile  

