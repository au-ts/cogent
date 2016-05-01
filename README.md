# File System Verification & Synthesis project


## Installation

Instructions tested on Debian GNU/Linux 8.2 (“jessie”). May need to be adapted for other systems.

If you are running the virtual machine image, skip to the next section.

```
# Install dependencies from the Debian repository.
sudo apt-get install git # git
sudo apt-get install libgmp-dev libncurses5-dev # Haskell
sudo apt-get install python-lxml python-psutil python-pycparser # regression tester

# Need a recent version of Glasgow Haskell Compiler (7.8.4+), cabal-install, alex, and happy.
# For instructions, consult file cogent/README for details. Or, if unsure, install Haskell Platform:
#   wget 'https://haskell.org/platform/download/7.10.2/haskell-platform-7.10.2-a-unknown-linux-deb7.tar.gz'
#   tar -xzf haskell-platform-7.10.2-a-unknown-linux-deb7.tar.gz
#   sudo ./install-haskell-platform.sh
#   sudo apt-get install libgmp-dev libncurses-dev

# Install Isabelle2015. If you have an existing Isabelle install,
# you may want to set ISABELLE_IDENTIFIER instead of PATH.
export PATH="$(pwd)/isabelle/bin:$PATH"
isabelle components -I
isabelle components -a
```


## Proofs

To build the proofs, it is recommended that your machine (or virtual machine)
provides 32G of memory and 4–8 CPU threads.

```
# Run build system and regression tests. (ETA: 2–3 CPU hours)
# This also builds the COGENT compiler and Isabelle theories.
# If this works, your install is probably ok.
regression/run_tests.py -x l4v -x isabelle -v

# Build compilation correctness proof for BilbyFS. (ETA: 120 CPU hours)
(cd impl/bilby/cogent;
 make verification;
 patch <../../../BilbyFS_CorresProof.patch;
 isabelle build -d . -d ../../../cogent/isa -d ../../../l4v -b -o process_output_limit=999 BilbyFS_AllRefine)

# View end-to-end theorems. Each theory has a "print_theorems" command for this.
# For BilbyFS:
isabelle jedit -d impl/bilby/cogent -d cogent/isa -d l4v -l BilbyFS_CorresProof impl/bilby/cogent/BilbyFS_AllRefine.thy
```

The functional correctness proofs for BilbyFS's `sync` and `iget` operations are in
[`impl/bilby/proof/`](`impl/bilby/proof/`).
They are built as part of the regression tests (above), and can be rebuilt with

```
regression/run_tests.py -x l4v -x isabelle -v sync iget
```


## File system

See [`impl/bilby/README`](`impl/bilby/README`) for more information


## Directory

* [`cogent`](cogent/): COGENT compiler
  * [`isa`](cogent/isa/): Isabelle/HOL semantics for COGENT
  * [`tests`](cogent/tests/): Compiler test suite
* [`c-refinement`](c-refinement/): Isabelle/HOL theories and proof procedures for COGENT-C refinement
  * [`tests`](c-refinement/tests/): COGENT test programs for proof procedures
* [`isa-parser`](isa-parser/): Haskell library for parsing and pretty-printing Isabelle/HOL
* [`impl`](impl/): COGENT programs and libraries
  * [`libgum`](impl/libgum/): Common COGENT and C libraries
  * [`bilby`](impl/bilby/): Bilby file system
    * [`cogent/fs`](impl/bilby/cogent/fs/): COGENT code for BilbyFS
* [`regression`](regression/): Regression test script
