# ARTEFACT
---

This formalisation works with [Isabele2019](https://isabelle.in.tum.de/website-Isabelle2019/index.html),
[AutoCorres version 1.6.1](https://trustworthy.systems/projects/TS/autocorres/) and
Cogent from this [branch](https://github.com/au-ts/cogent/tree/uabsfuns-decl-fix).

The work that is being presented are all the files in **loops**, **sum-example** and the file _bilby/adt/WordArray\_Shallow.thy_.

## Install Isabelle2019

Follow the instructions for installing.
Ensure that it is on the PATH.

## Install AutoCorres

Install AutoCorres for a 32-bit architecture, i.e. ARM.
Set the environment variable **AC_DIR** to the top level directory of AutoCorres.

## Install Cogent

Follow the installation instructions.
Set the environment variable **COGENT_DIR** to be the top level directory of Cogent.

## Sum Example

### Important Files

* _Sum.cogent_: Contains the Cogent program for sum and other functions.
* _wordarray.cogent_: Cogent declarations for word arrays and its operations.
* _wordarray.ac_: Antiquoted C definitions of the word array operations.
* _WordArray.ah_: Antiquoted C definition of word arrays.
* _main.ac_: Main "program".
* _abstract/WordArray\_u32.h_: Contains the generated C definition of 32-bit word arrays.
* _main\_pp\_inferred.c_: Contains the generated C from the main program.
* _Sum\_AllRefine.thy_: Contains the shallow to C refinement proof and functional correctness proof.
* _Generated\_ShallowShared.thy_: Contains the shallow embedding of word arrays.
* _Generated\_CorresSetup.thy_: Contains the update-C value relation for word arrays and the state relation.
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

To build the example, use the command:

`$ make`

To run the example, go into the **sum-example** folder and use the command:

`$ L4V_ARCH=ARM isabelle jedit -d $COGENT_DIR -d $AC_DIR -d . -l CogentCRefinement Sum_AllRefine.thy`

---

## Loops Example

### Important Files

* _repeat.cogent_: Cogent declarations for the higher order polymorphic loop.
* _wordarray.cogent_: Cogent declarations for word arrays and the operations for length, put, get and get\_opt.
* _test.cogent_: Contains the Cogent program for binary search, calculating the log base 2 of a number, calculating the exponent of a number,
				 and some word array operations.
* _WordArray.ah_: Template C definition of word arrays.
* _main.ac_: Main "program".
* _repeat.ac_: Template C definitions of the higher order polymorphic loop.
* _wordarray.ac_: Template C definitions of the word array operations.
* _build/abstract/WordArray\_u32.h_: Contains the generated C definition of 32-bit word arrays.
* _build/main\_pp\_inferred.c_: Contains the generated C from the main program that is verified.
* _BinarySearch.thy_: Contains the functional correctness proof of binary search.
* _BinarySearchAsm.thy_: Contains the proofs to discharge the FFI assumptions that Cogent makes when compiling _test.cogent_,
						 and the manual instantiation of the abstract function environments.
* _build/Generated\_CorresSetup.thy_: Contains the update-C value relation for word arrays and the state relation.
* _build/Generated\_ShallowShared.thy_: Contains the shallow embedding of word arrays.
* _RepeatCorrespondence.thy_: Contains the value to update refinement proof for the loop.
* _RepeatCorres.thy_: Contains the update to C refinement proof for the loop.
* _RepeatMono.thy_: Contains the wrapper polymorphic value embedding of the loop, and the monomorphisation proof.
* _RepeatScorres.thy_: Contains the wrapper shallow embedding and the shallow to value refinement proof for the loop.
* _RepeatShallow.thy_: Contains the neat shallow embedding of the loop and proofs about loop invariants.
* _RepeatUpdate.thy_: Contains the neat and wrapper update semantic embedding of the loop and proofs for type preservation and invariants.
* _RepeatValue.thy_: Contains the value semantic embedding of the loop, proofs for type preservation and invariants, and the wrapper monomorphic embedding of the loop.
* _WordArrayCorrespondence.thy_: Contains the value to update value relation and refinement proofs for the word array operations.
* _WordArrayCorres.thy_: Contains the update to C refinement proofs for the word array operations.
* _WordArrayMono.thy_: Contains the monomorphisation proofs for the word array operations.
* _WordArrayScorres.thy_: Contains the shallow embedding of word array operations and the shallow to value refinement proofs for the word array operations.
* _WordArrayUpdate.thy_: Contains the value typing of word arrays, the embedding of the word array operations and the type preservation and frame constraint proofs.
* _WordArrayValue.thy_: Contains the value typing of word arrays, the embedding of the word array operations, and the proofs for type preservation.

The **build** directory contains all the files that the Cogent compiler would generate for the _test.cogent_ program,
with some minor manual edits to add in the C to update value and type relation for word arrays, state relation, the shallow embedding for word arrays.

#### Helper theory files

Below are the files that contain helper lemmas used in the work.

* _CogentTypingHelper.thy_
* _CorresHelper.thy_
* _CorrespondenceHelper.thy_
* _DeterministicRelation3.thy_
* _MonoHelper.thy_
* _PartialOrderRelation3.thy_
* _UpdateSemHelper.thy_
* _ValueSemHelper.thy_

### Running the Loops Example

To build the example, use the command:

`$ make`

To run the example, go into the **loops** folder and use the command:

`$ L4V_ARCH=ARM isabelle jedit -d $COGENT_DIR -d $AC_DIR -d build -l CogentCRefinement BinarySearch.thy`

---

## BilbyFS Functional Correctness Proofs

### Important Files
* _WordArrayT.thy_: The axiomatization of word arrays in located here.
* _WordArray\_Shallow.thy_: The shallow embedding of word arrays used in Bilby is in here, minor differences to the one used to sum example since the types are named differently, the shallow for wordarray_get has undefined behaviour when accessing an element out of bounds.
* _FsopIgetR.thy_: Contains the functional correctness proof for the iget operation.
* _FsopSyncR.tny_: Contains the functional correctness proof for the sync operation.
* _AfsS.thy_: Contains the functional correctness specifications.

Besides _WordArrayT.thy_ and _WordArray\_Shallow.thy_ there were some minor modifications 

### Running the BilbyFS Functional Correctness Proofs

To build the proofs without launching jedit, run

`$ make iget`

or

`$ make sync`

in the directory **bilby** and these will make the proofs for *iget* and *sync* respectively.

To launch with jedit run

`$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres-1.6.1 -d . -l BilbyFs refine/FsopIgetR.thy`

or

`$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres-1.6.1 -d . -l BilbyFs refine/FsopSyncR.thy`

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
│   ├── autocorres-1.6.1 
│   ├── cogent  
│   │   └── ...  
│   ├── c-refinement  
│   │   └── ...  
│   └── ROOTS  
├── loops  
│   ├── ...  
│   ├── BinarySearchAsm.thy  
│   ├── BinarySearch.thy  
│   ├── build  
│   │   ├── abstract  
│   │   │   └── WordArray_u32.h   
│   │   ├── Generated_CorresSetup.thy   
│   │   ├── Generated_ShallowShared.thy   
│   │   ├── main_pp_inferred.c   
│   │   ├── ROOT   
│   │   └── ...   
│   ├── CogentTypingHelper.thy   
│   ├── CorresHelper.thy   
│   ├── CorrespondenceHelper.thy   
│   ├── DeterministicRelation3.thy   
│   ├── main.ac   
│   ├── MonoHelper.thy   
│   ├── PartialOrderRelation3.thy   
│   ├── repeat.ac   
│   ├── repeat.cogent   
│   ├── RepeatCorrespondence.thy   
│   ├── RepeatCorres.thy   
│   ├── RepeatMono.thy   
│   ├── RepeatScorres.thy   
│   ├── RepeatShallow.thy   
│   ├── RepeatUpdate.thy   
│   ├── RepeatValue.thy   
│   ├── test.cogent   
│   ├── UpdateSemHelper.thy   
│   ├── ValueSemHelper.thy   
│   ├── wordarray.ac   
│   ├── WordArray.ah   
│   ├── wordarray.cogent   
│   ├── WordArrayCorrespondence.thy   
│   ├── WordArrayCorres.thy   
│   ├── WordArrayMono.thy   
│   ├── WordArrayScorres.thy   
│   ├── WordArrayUpdate.thy   
│   └── WordArrayValue.thy   
├── README.md    
└── sum-example  
    ├── ...    
    ├── abstract  
    │   └── WordArray_u32.h   
    ├── main.ac  
    ├── main_pp_inferred.c  
    ├── ROOT  
    ├── Sum_AllRefine.thy  
    ├── Sum.cogent  
    ├── WordArray_Abstractions.thy  
    ├── wordarray.ac  
    ├── WordArray.ah  
    ├── wordarray.cogent  
    ├── WordArray_CorresProof_Asm.thy  
    ├── WordArray_Shallow.thy  
    ├── WordArray_SVCorres.thy  
    ├── WordArray_UAbsFun.thy  
    ├── WordArray_Update.thy  
    ├── WordArray_UpdCCorres.thy  
    ├── WordArray_VAbsFun.thy  
    └── WordArray_Value.thy  
