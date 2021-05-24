=========================
Cogent Installation Guide
=========================

.. highlight:: bash


In a Nutshell
=============

See :ref:`install-more-details` below for a more elaborate guide.

0. We primarily support Debian-style Linux OS. Other \*nix systems should also work, provided
   your platform supports all the dependencies Cogent needs.
1. Install `GHC <https://www.haskell.org/downloads/>`__. For supported versions of GHC,
   see the ``tested-with`` section of `cogent/cogent.cabal <https://github.com/NICTA/cogent/blob/master/cogent/cogent.cabal>`_.
2. Install `Cabal <https://www.haskell.org/cabal/download.html>`__ *or*
   `Stack <https://docs.haskellstack.org/en/stable/README/>`__.

.. note:: We say ``Cabal`` to mean the ``cabal-install`` tool, which is not the same as
   the ``Cabal`` library. In particular, the version of ``cabal-install`` is not
   necessarily the same as that of the ``Cabal`` library.

3. Install `Alex <https://www.haskell.org/alex/>`__ and `Happy <https://www.haskell.org/happy/>`__.
4. Clone the `Cogent repository <https://github.com/NICTA/cogent>`__.
   Suppose the Cogent repository is located ``$COGENT``. Upon this point you should be able to install
   the Cogent compiler and compile Cogent programs. Move to directory ``$COGENT/cogent``, and use
   either Cabal or Stack to build the Cogent compiler. 

.. note:: For ``cabal`` users, we require cabal version 3.0+ and we use the ``new-*`` commands.

5. As a sanity check, you should be able to run ``make test-compiler`` in the ``$COGENT/cogent`` folder,
   and the tests should pass.
6. To run verification, install `Isabelle-2019 <https://isabelle.in.tum.de/>`_ either from their
   website, or you can simply checkout the ``isabelle`` submodule in the Cogent repository.
   You also need to download `AutoCorres (v1.6.1) <http://ts.data61.csiro.au/projects/TS/autocorres.html>`_.


.. _install-more-details:

Detailed Instructions
=====================

Dependencies
------------

-  `The Glasgow Haskell Compiler (GHC) <https://www.haskell.org/>`__
-  `Cabal <https://www.haskell.org/cabal/>`__  *or*
   `Stack <https://docs.haskellstack.org/en/stable/README/>`__
-  `Alex <https://www.haskell.org/alex/>`__
-  `Happy <https://www.haskell.org/happy/>`__
-  `z3 <https://github.com/Z3Prover/z3>`__ (which is also included
   as a submodule for convenience)

Install Cogent dependencies
---------------------------

The GHC compiler and Cabal
^^^^^^^^^^^^^^^^^^^^^^^^^^

Follow the instructions on the `Haskell Downloads page <https://www.haskell.org/downloads/>`__
to install GHC. Any of the options (Minimal installer, Stack, or Haskell Platform) will work.

.. note:: The supported versions of GHC and Cabal are specified
          in `cogent/cogent.cabal <https://github.com/NICTA/cogent/blob/master/cogent/cogent.cabal>`__.

.. note:: On Linux you may also have to install ``libgmp-dev``. This can
          be done with the command

::

  sudo apt-get install libgmp-dev

or the equivalent command for your Linux distribution.

``alex`` and ``happy``
^^^^^^^^^^^^^^^^^^^^^^

::

  cabal new-install alex happy

or the equivalent commands using ``stack``.

Usually, the executables are located ``$HOME/.cabal/bin/``. Make sure
you add them to your ``$PATH``.

``z3`` SMT-solver
^^^^^^^^^^^^^^^^^

.. note:: This is optional. You don’t have to install ``z3`` if you don’t
          plan to use Cogent’s type-level computation features (see :ref:`static-arrays`).

Follow their `README.md <https://github.com/Z3Prover/z3/blob/b79440a21d404bcf0c2e34e83f1c04555342cfb9/README.md>`__.
Make sure that the executable is included in your ``$PATH``. Alternatively you can use the included
`submodule <https://github.com/Z3Prover/z3/tree/b79440a21d404bcf0c2e34e83f1c04555342cfb9>`__ 
by ``git submodule update --init --recursive -- z3``.

.. note:: We only tested against the snapshot checked-in in the
          `submodule <https://github.com/Z3Prover/z3/tree/b79440a21d404bcf0c2e34e83f1c04555342cfb9>`__.
          Similar versions of ``z3`` have a chance to work but is not guaranteed.

Install Cogent
--------------

.. _optional-features:

Optional features
^^^^^^^^^^^^^^^^^

Cogent comes with several experimental (reads: very unstable) or
additional features that you can opt-in. These features are (with the
names of the respective flags in parentheses): 

   1. built-in static arrays (``builtin-arrays``)
   2. documentation generation (``docgent``)
   3. property-based testing in Haskell (``haskell-backend``)
   4. LLVM backend (``llvm-backend``)

Depending on which (combination of) features are needed, the
dependencies will be different. By default, none of them are enabled. If
you want them enabled, appropriate flags should be given while building
Cogent (see below for instructions).

There are three ways of building the Cogent compiler:

  * Stack (simple, more robust)
  * Makefile (simple, but can be fragile)
  * Cabal (also simple, and more advanced)

Detailed instructions for each of them are given below:

Build with Stack (simple, more robust)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Stack_ is a cross-platform program for developing Haskell projects.
To build Cogent with Stack, simply run ``stack build`` in the ``cogent`` directory in
which ``stack.yaml`` is located. We provide such config files (``stack-<ghc-version>.yaml``) for several different
stack snapshots.

.. _Stack: https://docs.haskellstack.org/

Build with Makefile (simple, but can be fragile)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-  To configure, edit `config.mk <https://github.com/NICTA/cogent/blob/master/config.mk>`__. The default values
   should work for most people.
-  Change the flags for building Cogent in that file.
-  Run ``make`` or ``make dev``. The latter builds Cogent instead of
   installing it, which is more suitable for developers.

For more info, run ``make help``.

Build with Cabal (also simple, and more advanced)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``Makefile`` calls Cabal under the hood. The new (3.0+) version of Cabal
is made relatively easy to use. You can use ``cabal new-configure`` with relevant options
to set the flags and compiler version that are desired. Or it can be set manually
in a ``cabal.project.local`` file.
After the configuration, Cogent can be easily installed by
``cabal new-install --installdir=<BINDIR>`` command, where ``<BINDIR>`` is the directory
in which you want the ``Cogent`` executable to be placed. This location should be added
to your ``$PATH``.


Test your installation
----------------------

1. Run ``make`` with relevant targets in the ``cogent`` directory.

-  ``make tests`` runs the entire test suite, which is **not** what you
   would like to do in most cases, as it also tests some Isabelle/HOL proofs, which
   will take very long time.
-  ``make test-compiler`` tests many of the compiler phases without involving Isabelle.
-  There are individual tests that can be triggered by ``make test-*``.
   See ``make help`` for details. The test files are grouped in sub-directories under
   `cogent/tests/tests <https://github.com/NICTA/cogent/tree/master/cogent/tests/tests>`_.
-  ``make examples`` builds a group of small but complete Cogent
   examples. The examples are located in `cogent/examples <https://github.com/NICTA/cogent/tree/master/cogent/examples>`_. You
   can run ``make`` in each example's directory to build them individually.

2. Cogent compiler also comes with a small unit-test module. To run
   that, do this:

::

  $> cabal new-build
  $> cabal new-test



.. _install-macos-hints:

Testing on macOS
^^^^^^^^^^^^^^^^

To run Cogent examples and some tests, you need a GNU compatible version
of ``cpp`` installed in your ``PATH``. The default ``cpp`` installed on
``macOS`` isn't GNU compatible.

A solution:

  1. Install Homebrew
  2. Run ``brew install gcc``. This will create symlinks ``gcc-8`` and ``cpp-8``
     (or whatever the latest gcc version number is) in ``/usr/local/bin`` to the newly installed version
     of ``gcc``.
  3. Provided ``ls /usr/local/bin/cpp`` outputs
     ``No such file or directory``, it should be safe to run
     ``ln -s /usr/local/bin/cpp-8 /usr/local/bin/cpp`` (remember to adapt the command to the ``cpp`` version you installed).
  4. If ``which cpp`` doesn't print ``/usr/local/bin/cpp``, then running
     ``export PATH=/usr/local/bin:$PATH`` in any shell where you want run the
     examples will ensure that the correct version of ``cpp`` is used.

Running ``make examples`` should now be successful.


Common Issues and Troubleshooting
=================================

Cabal Version
-------------

Cogent currently relies on ``cabal >= 3.0``. Please ensure that you are using version 3. 

Missing Dependencies
--------------------

Before trying to build Cogent, ensure that ``happy`` and ``alex`` are installed with cabal/stack::

  cabal new-install happy
  cabal new-install alex

