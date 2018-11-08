[![Build Status](https://api.travis-ci.org/NICTA/cogent.svg?branch=master)](https://travis-ci.org/NICTA/cogent)

# Cogent: Code and Proof Co-Generation

## Project homepage

For general context of this project, motivation, an overview, and published papers, see
our [project homepage](http://ts.data61.csiro.au/projects/TS/cogent.pml).


## Installation

Instructions tested on Debian GNU/Linux 8.2 ("jessie") and Ubuntu 16.04 ("xenial"). May need to be adapted for other systems.

Install dependencies from the Debian repository.
```
sudo apt-get install git # git
sudo apt-get install python-lxml python-psutil python-pycparser # regression tester
```

To install the Cogent compiler, consult file [cogent/README.md](./cogent/README.md) for details. 

[`l4v`](https://github.com/seL4/l4v), [`isabelle`](https://github.com/seL4/isabelle) and [`z3`](https://github.com/Z3Prover/z3)
are submodules that the Cogent framework depends on. To get them: `git submodule update --init --recursive`.

If you already have them on your machine, you can use your local copies, by checking out the compatible revisions:
* `l4v`: `ecc84ffc6ead5a4d80aac7dabacf4b010c05dfca`
* `isabelle`: any Isabelle2018 revision
* `z3`: see [cogent/INSTALL.md](./cogent/INSTALL.md) for more information

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
(cd impl/fs/ext2/cogent;
 make verification;
 isabelle build -d plat/verification -d ../../../../cogent/isa -d ../../../../l4v -b Ext2_AllRefine)

# Build compilation correctness proof for BilbyFs. (ETA: 120 CPU hours)
(cd impl/fs/bilby/cogent;
 make verification;
 patch -d plat/verification < ../../../../BilbyFs_CorresProof.patch;
 isabelle build -d . -d ../../../../cogent/isa -d ../../../../l4v -b -o process_output_limit=999 BilbyFs_AllRefine)

# View end-to-end theorems. Each theory has a "print_theorems" command for this.
# For ext2:
isabelle jedit -d impl/ext2/cogent/plat/verification -d cogent/isa -d l4v -l Ext2_CorresProof impl/fs/ext2/cogent/plat/verification/Ext2_AllRefine.thy
# For BilbyFs:
isabelle jedit -d impl/fs/bilby/cogent/plat/verification -d cogent/isa -d l4v -l BilbyFs_CorresProof impl/fs/bilby/cogent/plat/verification/BilbyFs_AllRefine.thy
```

The functional correctness proofs for BilbyFs's `sync` and `iget` operations are in
`impl/fs/bilby/proof/`.
They are built as part of the [regression tests](#regression-tests), and can be rebuilt with

```
regression/run_tests.py -x l4v -x isabelle -v sync iget
```


## File systems

See [impl/fs/ext2/README](./impl/fs/ext2/README) and [impl/fs/bilby/README](./impl/fs/bilby/README) for more information on how to build the kernel modules


## Directory

* `cogent`: Cogent compiler
* `c-refinement`: Isabelle/HOL theories and proof procedures for Cogent-C refinement
  * `tests`: Cogent test programs for proof procedures
* `isa-parser`: Haskell library for parsing and pretty-printing Isabelle/HOL
* `impl`: Systems implemented in Cogent
  * `fs`: File systems
    * `bilby`: Bilby file system
      * `cogent`: Cogent code for BilbyFs
      * `c`: C implementation for BilbyFs
      * `proof`: Functional correctness specs and proofs for BilbyFs
    * `ext2`: ext2 file system
      * `cogent`: Cogent code for ext2
* `regression`: Regression test script
