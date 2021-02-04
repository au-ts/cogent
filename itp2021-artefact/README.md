# ARTIFACT

### Directory Structure
* cogent
	* autocorres
	* c-refinement
	* cogent
		* isa
			* shallow
* sum-example
* sum-example-manual

### Sum Example

## Important Files

* _Sum_AllRefine.thy_: Contains the shallow to C refinement proof and functional correctness proof.
* _WordArray_Abstractions.thy_: Contains the value typing for word arrays, the value relation between update and value for word arrays,
  and the proof that word arrays adhere to the FFI constraints, i.e. the locale constraints.
* _WordArray_Shallow.thy_: Contains the shallow embedding for word array operations.
* _WordArray_Value.thy_: Contains both the polymorphic and monomorphic embedding of word array operations in the value semantics, and the proofs for type preservation and monomorphisation.
* _WordArray_Update.thy_: Contains the embedding of word array operations in the update semantics, and the type preservation and frame constraint proofs.
* _WordArray_VAbsFun

## Running the Sum Example

This formalisation works with Isabele2019. 
First extract the **autocorres.tar.gz** located in the top **cogent** folder.
Install AutoCorres for 32-bit architecture, i.e. ARM, following the instructions located in the **autocorres** folder.

To run the example, go into the **sum-example** folder and use the command:

$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres -d . -l AutoCorres Sum_AllRefine.thy

## Running the Sum Example Manually

Note that if you wish to build from source, you will need to download the Cogent compiler from the branch **wordarray-example**.
Then inside of the **sum-example-manual** folder, run
$ make
and then
$ L4V_ARCH=ARM isabelle jedit -d ../cogent -d ../cogent/autocorres -d . -l AutoCorres Sum_AllRefine.thy

### Running the Shallow BilbyFS Functional Correctness Proofs

## Important Files
* _WordArrayT.thy*: The axiomatization of word arrays in located here.
* _WordArray_Shallow.thy*: The shallow embedding of word arrays used in Bilby is in here, minor differences to the one used to sum example since the types are named differently, the shallow for wordarray_get has undefined behaviour when accessing an element out of bounds.
* _FsopIgetR.thy_: Contains the functional correctness proof for the iget operation.
* _FsopSyncR.tny_: Contains the functional correctness proof for the sync operation.

