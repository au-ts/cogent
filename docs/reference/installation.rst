************************************************************************
                           Installation Guide
************************************************************************

.. highlight:: bash


In a Nutshell
=============

See :ref:`install-more-details` below for a more elaborate guide.

0. We primarily support Debian-style Linux OS. Other \*nix systems should also work, provided
   your platform supports all the dependencies |cogent| needs.
1. Install `GHC <https://www.haskell.org/downloads/>`__. For supported versions of GHC,
   see the ``tested-with`` section of `cogent/cogent.cabal <https://github.com/NICTA/cogent/blob/master/cogent/cogent.cabal>`_.
2. Install `Cabal <https://www.haskell.org/cabal/download.html>`__ *or*
   `Stack <https://docs.haskellstack.org/en/stable/README/>`__.
3. Install `Alex <https://www.haskell.org/alex/>`__ and `Happy <https://www.haskell.org/happy/>`__.
4. Clone the `Cogent repository <https://github.com/NICTA/cogent>`__.
   Suppose the |cogent| repository is located ``$COGENT``. Upon this point you should be able to install
   the |cogent| compiler and compile |cogent| programs. Move to directory ``$COGENT/cogent``, and use
   either Cabal or Stack to build the |cogent| compiler. 

.. note:: For ``cabal`` users, we provide
   a config file for each supported version of GHC, so that you always get consistent dependencies.
   These config files are located in `cogent/misc/cabal.config.d <https://github.com/NICTA/cogent/tree/master/cogent/misc/cabal.config.d>`_.
   Move the one that matches your GHC version to ``$COGENT/cogent/cabal.config``. Then run Cabal
   as normal.

5. As a sanity check, you should be able to run ``make test-compiler`` in the ``$COGENT/cogent`` folder,
   and the tests should pass.
6. To run verification, install `Isabelle-2019 <https://isabelle.in.tum.de/>`_ either from their
   website, or you can simply checkout the ``isabelle`` submodule in the |cogent| repository.
   You also need to download `AutoCorres (v1.6) <http://ts.data61.csiro.au/projects/TS/autocorres/>`_.


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

Install |cogent| dependencies
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

  cabal install alex happy

or the equivalent commands using ``stack``.

Usually, the executables are located ``$HOME/.cabal/bin/``. Make sure
you add them to your ``$PATH``.

``z3`` SMT-solver
^^^^^^^^^^^^^^^^^

.. note:: This is optional. You don’t have to install ``z3`` if you don’t
          plan to use |cogent|’s type-level computation features (see :ref:`static-arrays`).

Follow their `README.md <https://github.com/Z3Prover/z3/blob/b79440a21d404bcf0c2e34e83f1c04555342cfb9/README.md>`__.
Make sure that the executable is included in your ``$PATH``. Alternatively you can use the included
`submodule <https://github.com/Z3Prover/z3/tree/b79440a21d404bcf0c2e34e83f1c04555342cfb9>`__ 
by ``git submodule update --init --recursive -- z3``.

.. note:: We only tested against the snapshot checked-in in the
          `submodule <https://github.com/Z3Prover/z3/tree/b79440a21d404bcf0c2e34e83f1c04555342cfb9>`__.
          Similar versions of ``z3`` have a chance to work but is not guaranteed.

Install |cogent|
--------------

.. _optional-features:

Optional features
^^^^^^^^^^^^^^^^^

|cogent| comes with several experimental (reads: very unstable) or
additional features that you can opt-in. These features are (with the
names of the respective flags in parentheses): 

   1. built-in static arrays (``builtin-arrays``)
   2. documentation generation (``docgent``)
   3. property-based testing in Haskell (``haskell-backend``)

Depending on which (combination of) features are needed, the
dependencies will be different. By default, none of them are enabled. If
you want them enabled, appropriate flags should be given while building
|cogent| (see below for instructions).

There are three ways of building the |cogent| compiler:

  * Makefile (simple, but can be fragile)
  * Cabal (more advanced)
  * Stack (simple, more robust)

Detailed instructions for each of them are given below:


Build with Makefile (simple, but can be fragile)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-  To configure, edit `config.mk <https://github.com/NICTA/cogent/blob/master/config.mk>`__. The default values
   should work for most people.
-  Copy the config file of the GHC version you want to use from
   `cogent/misc/cabal.config.d <https://github.com/NICTA/cogent/tree/master/cogent/misc/cabal.config.d>`__
   into the ``cogent`` folder, and then rename it to ``cabal.config``.
-  Change the flags for building |cogent| in that file.
-  Run ``make`` or ``make dev``. The latter builds |cogent| instead of
   installing it, which is more suitable for developers.

For more info, run ``make help``.

Build with Cabal (more advanced)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The ``Makefile`` calls Cabal under the hood. It installs |cogent| using a
Cabal sandbox. If this is not ideal for you (in rare cases), or you want
to customise your installation further, just use Cabal in the normal
way. You need to install `isa-parser <https://github.com/NICTA/cogent/tree/master/isa-parser>`__
before you build/install |cogent|.

Copy the config file of the GHC version you want to use from
`/cogent/misc/cabal.config.d <https://github.com/NICTA/cogent/tree/master/cogent/misc/cabal.config.d>`__
into this folder, and then rename it to ``cabal.config``, and change the flags at the very beginning
of that config file accordingly.
Alternatively, the flags can be overwritten if something like
``--flags="flag1 flag2"`` is given when running ``cabal configure`` and
``cabal install``.


Build with Stack (simple, more robust)
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Stack_ is a cross-platform program for developing Haskell projects.
To build |cogent| with Stack, simply run ``stack build``.

.. _Stack: https://docs.haskellstack.org/


Test your installation
----------------------

1. Test files are in `cogent/tests <https://github.com/NICTA/cogent/tree/master/cogent/tests>`__.
   Run ``make`` with relevant targets.

-  ``make tests`` runs the entire test suite, which is **not** what you
   would like to do in most cases, as it also tests some Isabelle/HOL proofs, which
   will take very long time.
-  ``make test-compiler`` tests many of the compiler phases without involving Isabelle.
-  There are individual tests that can be triggered by ``make test-*``.
   See ``make help`` for details.
-  ``make examples`` builds a group of small but complete |cogent|
   examples.

2. |cogent| compiler also comes with a small unit-test module. To run
   that, do this:

::

  $> cabal configure --enable-tests
  $> cabal build
  $> cabal test



.. _install-macos-hints:

Testing on macOS
^^^^^^^^^^^^^^^^

To run |cogent| examples and some tests, you need a GNU compatible version
of ``cpp`` installed in your ``PATH``. The default ``cpp`` installed on
``macOS`` isn't GNU compatible.

A solution:

  1. Install Homebrew
  2. Run ``brew install gcc``. This will create symlinks ``gcc-8`` and ``cpp-8``
     (or whatever the latest gcc version number is) in ``/usr/local/bin`` to the newly installed version
     of ``gcc``.
  3. Provided ``ls /usr/local/bin/cpp`` outputs
     ``No such file or directory``, it should be safe to run
     ``ln -s /usr/local/bin/cpp-8 /usr/local/bin/cpp``.
  4. If ``which cpp`` doesn't print ``/usr/local/bin/cpp``, then running
     ``export PATH=/usr/local/bin:$PATH`` in any shell where you want run the
     examples will ensure that the correct version of ``cpp`` is used.

Running ``make examples`` should now be successful.


Common Issues and Troubleshooting
=================================

Cabal Version
-------------

|cogent| currently relies on ``cabal >= 2.4.*``. Please ensure that you are not using version 3. 

Missing Dependencies
--------------------

Before trying to build |cogent|, ensure that ``happy`` and ``alex`` are installed with cabal/stack::

  cabal install happy
  cabal install alex

Could not resolve dependency ``isa-parser``
-------------------------------------------

You may see the following error message::

  Resolving dependencies...
  cabal: Could not resolve dependencies:
  [__0] trying: cogent-2.9.0.0 (user goal)
  [__1] unknown package: isa-parser (dependency of cogent)
  [__1] fail (backjumping, conflict set: cogent, isa-parser)
  After searching the rest of the dependency tree exhaustively, these were the
  goals I've had most trouble fulfilling: cogent, isa-parser

``isa-parser`` must be installed manually in this case. Change to the directory ``isa-parser`` at
the root of the repository, and run ``cabal install``. Then, retry installing/building |cogent|.

