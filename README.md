[![Build Status](https://github.com/au-ts/cogent/actions/workflows/ci.yml/badge.svg?branch=master)](https://github.com/au-ts/cogent/actions/workflows/ci.yml)
[![Documentation Status](https://readthedocs.org/projects/cogent/badge/?version=latest)](https://cogent.readthedocs.io/en/latest/?badge=latest)

# Cogent: Code and Proof Co-Generation

## Project homepage

For general context of this project, motivation, an overview, and published papers, see
our [project homepage](https://trustworthy.systems/projects/TS/cogent.pml).

## Online documentation

https://cogent.readthedocs.io

## Installation

Instructions tested on Debian GNU/Linux 9.8 ("stretch") and Ubuntu 18.04 ("bionic"). Similar distributions may also work.

Install dependencies from the Debian repository.
```
sudo apt-get install git # git
sudo apt-get install python-lxml python-psutil python-pycparser # regression tester
```

To install the Cogent compiler, consult file [cogent/README.md](./cogent/README.md) for details. 

The Cogent framework depends on [Isabelle-2019](https://isabelle.in.tum.de/).
If you already have them on your machine, you can use your local copy.
Otherwise you can either obtain it from their website or from the `isabelle` submodule, via
`git submodule update --init --recursive -- isabelle`.

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


## Compiler

See [cogent/README.md](./cogent/README.md) for more information.


## File systems

See [impl/fs/ext2/README](./impl/fs/ext2/README) and [impl/fs/bilby/README](./impl/fs/bilby/README) for more information on how to build the kernel modules.


## Proofs

Firstly, download the AutoCorres release v1.6.1 from [https://trustworthy.systems/projects/TS/autocorres](https://trustworthy.systems/projects/TS/autocorres/),
move the extracted folder to this directory, and rename the folder to `autocorres`.

To build the proofs, it is recommended that your machine (or virtual machine)
provides 32G of memory and 4–8 CPU threads.

```
# Build compilation correctness proof for ext2. (ETA: 120 CPU hours)
(cd impl/fs/ext2/cogent;
 make verification;
 export L4V_ARCH="ARM";
 isabelle build -d plat/verification -d ../../../../cogent/isa -d ../../../../autocorres -b Ext2_AllRefine)

# Build compilation correctness proof for BilbyFs. (ETA: 120 CPU hours)
(cd impl/fs/bilby/cogent;
 make verification;
 patch -d plat/verification < ../../../../BilbyFs_CorresProof.patch;
 export L4V_ARCH="ARM";
 isabelle build -d plat/verification -d ../../../../cogent/isa -d ../../../../autocorres -b -o process_output_limit=999 BilbyFs_AllRefine)

# View end-to-end theorems. Each theory has a "print_theorems" command for this.
# For ext2:
L4V_ARCH="ARM" isabelle jedit -d impl/ext2/cogent/plat/verification -d cogent/isa -d autocorres -l Ext2_CorresProof impl/fs/ext2/cogent/plat/verification/Ext2_AllRefine.thy
# For BilbyFs:
L4V_ARCH="ARM" isabelle jedit -d impl/fs/bilby/cogent/plat/verification -d cogent/isa -d autocorres -l BilbyFs_CorresProof impl/fs/bilby/cogent/plat/verification/BilbyFs_AllRefine.thy
```

The functional correctness proofs for BilbyFs's `sync` and `iget` operations are in
`impl/fs/bilby/proof/`.
They are built as part of the [regression tests](#regression-tests), and can be rebuilt with

```
regression/run_tests.py -x autocorres -x isabelle -v sync iget
```


## Regression tests (for developers; ETA: 2–3 CPU hours)

For testing the compiler, refer to [travis.yml](./travis.yml) for commands.

Run `./run_tests` to test systems implementations and parts of their Isabelle proofs.

For C-refinement proofs, which are excluded from the regression tests because of
their size, follow instructions in [Proofs](#proofs) section.


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


## The Gencot Tool

Gencot is a tool for translating C code to Cogent. It's developed by our collaborators.
The repository is hosted on [Github](https://github.com/F1-C0D3/gencot). See the
README file and the documentation for more details.

