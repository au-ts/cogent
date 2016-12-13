# Cogent: Code and Proof Co-Generation

## Project homepage

For general context of this project, motivation, an overview, and published papers, see
our [project homepage](http://ts.data61.csiro.au/projects/TS/cogent.pml).


## Installation

Instructions tested on Debian GNU/Linux 8.2 (“jessie”). May need to be adapted for other systems.

Install dependencies from the Debian repository.
```
sudo apt-get install git # git
sudo apt-get install libgmp-dev libncurses5-dev # Haskell
sudo apt-get install python-lxml python-psutil python-pycparser # regression tester
```

You need a recent version of Glasgow Haskell Compiler (7.10.1+), cabal-install, alex, and happy.
For instructions, consult file [cogent/README.md](./cogent/README.md) for details. 

[`l4v`](https://github.com/seL4/l4v/tree/47d5b746fc2f052586db11aa6048c5ae7c357155) and [`isabelle`](https://github.com/seL4/isabelle/tree/Isabelle2015) are two submodules in the repository.
To get them: `git submodule update --init --recursive`.

If you already have them on your machine, you can symlink them as `l4v` and `isabelle` respectively
in the top-level directory of this repository and checkout relevant revisions:
* `l4v`: `ffc7b107e5bd5978295da61f64ea87b9ea3ad4d1`
* `isabelle`: any Isabelle2015 revision

Add `isabelle/bin` to your PATH: `export PATH="$(pwd)/isabelle/bin:$PATH"`
If you have an existing Isabelle install, you may want to set `ISABELLE_IDENTIFIER` instead of `PATH`.

Initialise Isabelle and install components:
```
isabelle components -I
isabelle components -a
```
Consult [Isabelle manual](https://isabelle.in.tum.de/documentation.html) for more information.

For more customised settings to run proofs and regression tests, modify [`build-env.sh`](build-env.sh).

Note: also see [Proofs](#proofs) and [Regression tests](#regression-tests) below.


## Regression tests

Run build system and regression tests. (ETA: 2–3 CPU hours)
This also builds the Cogent compiler and Isabelle theories.
If this works, your install is probably ok.
Run `./run_tests`.

For C-refinement proofs, which are excluded from the regression tests because of
their size, follow instructions in [Proofs](#proofs) section.


## Proofs

To build the proofs, it is recommended that your machine (or virtual machine)
provides 32G of memory and 4–8 CPU threads.

```
# Build compilation correctness proof for ext2. (ETA: 120 CPU hours)
(cd impl/ext2/cogent;
 make verification;
 isabelle build -d plat/verification -d ../../../cogent/isa -d ../../../l4v -b Ext2_AllRefine)

# Build compilation correctness proof for BilbyFs. (ETA: 120 CPU hours)
(cd impl/bilby/cogent;
 make verification;
 patch -d plat/verification <../../../BilbyFs_CorresProof.patch;
 isabelle build -d . -d ../../../cogent/isa -d ../../../l4v -b -o process_output_limit=999 BilbyFs_AllRefine)

# View end-to-end theorems. Each theory has a "print_theorems" command for this.
# For ext2:
isabelle jedit -d impl/ext2/cogent/plat/verification -d cogent/isa -d l4v -l Ext2_CorresProof impl/ext2/cogent/plat/verification/Ext2_AllRefine.thy
# For BilbyFs:
isabelle jedit -d impl/bilby/cogent/plat/verification -d cogent/isa -d l4v -l BilbyFs_CorresProof impl/bilby/cogent/plat/verification/BilbyFs_AllRefine.thy
```

The functional correctness proofs for BilbyFs's `sync` and `iget` operations are in
`impl/bilby/proof/`.
They are built as part of the [regression tests](#regression-tests), and can be rebuilt with

```
regression/run_tests.py -x l4v -x isabelle -v sync iget
```


## File systems

See [impl/ext2/README](./impl/ext2/README) and [impl/bilby/README](./impl/bilby/README) for more information on how to build the kernel modules


## Directory

* `cogent`: Cogent compiler
  * `isa`: Isabelle/HOL semantics for Cogent
  * `tests`: Compiler test suite
* `c-refinement`: Isabelle/HOL theories and proof procedures for Cogent-C refinement
  * `tests`: Cogent test programs for proof procedures
* `isa-parser`: Haskell library for parsing and pretty-printing Isabelle/HOL
* `impl`: Cogent programs and libraries
  * `libgum`: Common Cogent and C libraries
  * `bilby`: Bilby file system
    * `cogent`: Cogent code for BilbyFs
    * `c`: C implementation for BilbyFs
    * `proof`: Functional correctness specs and proofs for BilbyFs
  * `ext2`: ext2 file system
    * `cogent`: Cogent code for ext2
* `regression`: Regression test script
