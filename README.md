# Cogent: Code and Proof Co-Generation

## Project homepage

For general context of this project, motivation, an overview, and published papers, see
our [project homepage](https://trustworthy.systems/projects/TS/cogent.pml).

## Online documentation

https://cogent.readthedocs.io

## Installation

Instructions tested on Debian GNU/Linux 9.8 ("stretch") and Ubuntu 18.04 ("bionic"). Similar distributions may also work.

To install the Cogent compiler, consult file [cogent/README.md](./cogent/README.md) for details. 

The Cogent framework depends on [Isabelle-2019](https://isabelle.in.tum.de/).
If you already have them on your machine, you can use your local copy.
Add the isabelle executable to your PATH.

Consult [Isabelle manual](https://isabelle.in.tum.de/documentation.html) for more information.

For more customised settings to run proofs and regression tests, modify [`build-env.sh`](build-env.sh).


## Compiler

See [cogent/README.md](./cogent/README.md) for more information.


## Proofs

Firstly, download the patched version of AutoCorres release v1.6.1 from [https://github.com/amblafont/AutoCorres](https://github.com/amblafont/AutoCorres),
move the extracted folder to this directory, and rename the folder to `autocorres`.

To build the proofs, it is recommended that your machine (or virtual machine)
provides 32G of memory and 4–8 CPU threads.


## Directory

* `cogent`: Cogent compiler
* `c-refinement`: Isabelle/HOL theories and proof procedures for Cogent-C refinement
* `isa-parser`: Haskell library for parsing and pretty-printing Isabelle/HOL

