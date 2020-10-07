************************************************************************
                      Getting the |cogent| Compiler
************************************************************************


What follows is a *very* quick guide
to setting up the |cogent| compiler,
enough to be able to write and compile code.
To do anything more complex,
including working on proofs,
you should also read the
:doc:`full installation instructions <../reference/installation>`.

|cogent|'s compiler is still a work in progress:
we don't (yet) provide compiled executables,
and it's not (yet) available in package managers,
so to install it, you'll need to do some work.

We assume you're running a recent \*nix-like operating system:
development primarily happens on
recent versions of Debian GNU/Linux,
and it's highly likely that
similar GNU/Linux systems will also work,
possibly with some minor tweaks.
macOS also generally works,
although you may need to acquire
some of the GNU development tools.


Install Haskell_.  An easy way to do this
is using the `Haskell Stack`_ tool.
If you're not planning on actively developing |cogent|,
this is an excellent option.

.. _Haskell:         https://www.haskell.org/
.. _`Haskell Stack`: https://www.haskellstack.org/

Once you've installed Stack,
get the |cogent| source code using Git:

.. code-block:: bash

   $ git clone https://github.com/NICTA/cogent.git
   $ cd cogent/cogent
   $ stack build

This will take several minutes,
depending on how fast your system is,
and how fast your Internet connection is.
Once this finishes, you can use:

.. code-block:: bash

   $ stack exec -- cogent

You can also copy the compiled executable
to a more convenient location
that might already be on your ``$PATH``.
To find out where the compiler is, run:

.. code-block:: bash

   $ stack exec -- which cogent

For much of this document,
we'll assume that you can just run ``cogent``
to invoke the |cogent| compiler.


For more information, check out the
:doc:`detailed installation instructions <../reference/installation>`.
