========================================================================
                  Cogent: Code and Proof Co-Generation
========================================================================

:Homepage:	https://ts.data61.csiro.au/projects/TS/cogent.pml
:Repository:	https://github.com/NICTA/cogent
:Documentation:	https://cogent.readthedocs.io/

:Version:	3.0.1
:License:
   - ``GPL-2.0-only``, the `GNU General Public License v2.0 only`_:
     files with ``@TAG(NICTA_GPL)`` or ``@TAG(DATA61_GPL)``;
   - ``GPL-2.0-or-later``, the `GNU General Public License v2.0 or later`_:
     ``cogent/lib/c/rbt.h`` and ``cogent/lib/gum/anti/rbt.ac``;
   - ``BSD-2-Clause``, the `BSD 2-Clause "Simplified" License`_:
     files with ``@TAG(NICTA_BSD)`` or ``@TAG(DATA61_BSD)``;

:Build Status:
   .. image::	https://api.travis-ci.org/NICTA/cogent.svg?branch=master
      :target:	https://travis-ci.org/NICTA/cogent
      :alt:	build status for ``master``
:Documentation:
   .. image::	https://readthedocs.org/projects/cogent/badge/?version=latest
      :target:	https://cogent.readthedocs.io/en/latest/?badge=latest
      :alt:	documentation status

.. _`GNU General Public License v2.0 only`:     LICENSE_GPLv2.txt
.. _`GNU General Public License v2.0 or later`: LICENSE_GPLv2.txt
.. _`BSD 2-Clause "Simplified" License`:        LICENSE_BSD2.txt

For a general context of this project, motivation,
an overview, and published papers,
see the project homepage,
at <https://ts.data61.csiro.au/projects/TS/cogent.pml>.

For documentation, see <https://cogent.readthedocs.io/>.


Installation
------------------------------------

See the installation instructions in the documentation,
in ``doc/introduction/installation.rst``.


What's Here?
------------------------------------

``cogent``:
   the Cogent compiler
``c-refinement``:
   Isabelle/HOL theories and proof procedures for Cogent-to-C refinement

   ``tests``:
      Cogent test programs for proof procedures

``isa-parser``:
   a Haskell library for parsing and pretty-printing Isabelle/HOL

``impl``:
   Systems implemented in Cogent

   ``fs``:
      file systems

      ``bilby``:
         the Bilby File System

         ``cogent``:
            Cogent implementation of BilbyFS
         ``c``:
            a C implementation of BilbyFS
         ``proof``:
            functional correctness specs and proofs

      ``ext2``:
         the ext2 file system

         ``cogent``:
            Cogent implementaion of ext2fs

``regression``:
   regression testing scripts

``minigent``:
   a tiny reimplementation of Cogent,
   often used for prototyping features

///



Instructions tested on Debian GNU/Linux 9.8 ("stretch") and Ubuntu 18.04 ("bionic"). Similar distributions may also work.

Install dependencies::

  # apt-get install git
  # apt-get install python-lxml python-psutil python-pycparser

To install the Cogent compiler,
consult file [cogent/README.md](./cogent/README.md) for details. 

The Cogent framework depends on [Isabelle-2019](https://isabelle.in.tum.de/).
If you already have them on your machine, you can use your local copy.
Otherwise you can either obtain it from their website or from the `isabelle` submodule, via
`git submodule update --init --recursive -- isabelle`.

Add `isabelle/bin` to your PATH: `export PATH="$(pwd)/isabelle/bin:$PATH"`
If you have an existing Isabelle install, you may want to set `ISABELLE_IDENTIFIER` instead of `PATH`.

Initialise Isabelle and install components::

  $ isabelle components -I
  $ isabelle components -a

Consult [Isabelle manual](https://isabelle.in.tum.de/documentation.html) for more information.

For more customised settings to run proofs and regression tests, modify [`build-env.sh`](build-env.sh).

Note: also see [Proofs](#proofs) and [Regression tests](#regression-tests) below.


## Compiler

See [cogent/README.md](./cogent/README.md) for more information.


## File systems

See [impl/fs/ext2/README](./impl/fs/ext2/README) and [impl/fs/bilby/README](./impl/fs/bilby/README) for more information on how to build the kernel modules.


## Proofs

Firstly, download the AutoCorres release from [http://ts.data61.csiro.au/projects/TS/autocorres/](http://ts.data61.csiro.au/projects/TS/autocorres/),
move the extracted folder to this directory, and rename the folder to `autocorres`.

To build the proofs, it is recommended that your machine (or virtual machine)
provides 32G of memory and 4–8 CPU threads.

To build the compilation correctness proof for ext2fs
(est. 120 CPU hours)::

  $ cd impl/fs/ext2/cogent
  $ make verification
  $ export L4V_ARCH='ARM'
  $ isabelle build -d plat/verification \
                   -d ../../../../cogent/isa \
                   -d ../../../../autocorres \
                   -b -v Ext2_AllRefine

To build the compilation correctness proof for BilbyFs
(est. 120 CPU hours)::

  $ cd impl/fs/bilby/cogent
  $ make verification
  $ patch -d plat/verification ../../../../BilbyFs_CorresProof.patch
  $ export L4V_ARCH='ARM'
  $ isabelle build -d plat/verification \
                   -d ../../../../cogent/isa \
                   -d ../../../../autocorres \
                   -b -o process_output_limit=999 -v BilbyFs_AllRefine

To view end-to-end theorems
(each theory has a "print_theorems" command for this)::

  $ export L4V_ARCH='ARM'

  # For ext2:
  $ isabelle jedit -d impl/fs/ext2/cogent/plat/verification \
                   -d cogent/isa \
                   -d autocorres \
                   -l Ext2_CorresProof impl/fs/ext2/cogent/plat/verification/Ext2_AllRefine.thy

  # For bilbyfs:
  $ isabelle jedit -d impl/fs/bilby/cogent/plat/verification \
                   -d cogent/isa \
                   -d autocorres \
                   -l BilbyFs_CorresProof impl/fs/bilby/cogent/plat/verification/BilbyFs_AllRefine.thy

The functional correctness proofs for
BilbyFs's `sync` and `iget` operations
are in `impl/fs/bilby/proof/`.
They are built as part of the [regression tests](#regression-tests),
and can be rebuilt with::

   regression/run_tests.py -x autocorres -x isabelle -v sync iget


## Regression tests (for developers; ETA: 2–3 CPU hours)

For testing the compiler, refer to [travis.yml](./travis.yml) for commands.

Run `./run_tests` to test systems implementations and parts of their Isabelle proofs.

For C-refinement proofs, which are excluded from the regression tests because of
their size, follow instructions in [Proofs](#proofs) section.


## The Gencot Tool

Gencot is a tool for translating C code to Cogent. It's developed by our collaborators.
The repository is hosted on [Github](https://github.com/F1-C0D3/gencot). See the
README file and the documentation for more details.
