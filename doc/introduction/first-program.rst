************************************************************************
			    A First Program
************************************************************************


The program we are going to walk through is
a simple program which adds two natural numbers up,
and prints out the result, or reports an overflow error.

|cogent| is a restricted, pure, functional language.
For example, |cogent| is unable to express
input/output operations, memory management, and loops.
For this reason, we will only write
the core functionality in |cogent|,
which adds up two natural numbers,
and check if overflow has happened.
To carry the result of the check,
we need a result type::

  type R a b = < Success a | Error b >

It has similar meaning to a sum type in Haskell
(or in any functional language)::

  -- in Haskell, we might say:
  data R a b = Success a | Error b

It says the result may be
either ``Success`` or ``Error`` ---
which are referred to as tags or variants ---
and, in each case,
a value will be associated with a tag:
``Success`` has an associated ``a``, and
``Error`` has an associated ``b``.
Note that ``R a b`` is *polymorphic* on ``a`` and ``b``:
we may replace those *type variables* with any concrete types.

One notable difference to the Haskell version above is
that the ``type`` keyword only introduces a *type synonym*,
where in Haskell it would introduce a new type.
Thus, wherever an ``R a b`` is needed,
it may be equivalently spelled in full
as ``< Success a | Error b >``
(which, of course, is more verbose in many cases).


Next we define a function ``add``.
As with other strongly-typed functional languages,
we do so by first giving its type signature::

  add : (U32, U32) -> R U32 ()

``U32`` is a type representing
an unsigned 32-bit integer;
here, we use it to model the natural numbers.
|cogent| has built-in types for
common sizes of unsigned integers:
``U8``, ``U16`` and ``U64`` also exist.

Unlike many other functional languages,
a |cogent|'s functions can only take **one argument**.
When we wish to pass two ``U32``\ s,
we make them into a pair (or, more generally, a tuple).

Ignoring, for the moment, the error handling,
our first attempt at writing ``add`` might look like::

  add : (U32, U32) -> R U32 ()
  add (x, y) = Success (x + y)

Similar to Haskell,
we give a function's definition
by declaring the computation it does:
here, ``add (x, y)`` becomes ``(x + y)``,
wrapped in ``Success``.
Cogent also supports *pattern matching*,
so the names ``x`` and ``y`` bind,
as expected,
to the values of the tuple passed in.

.. todo:

   - introduce let/in
   - introduce patterns
   - full definition

Let's have a look at the rest of ``add``'s definition::

.. code-block:: none

  add : (U32, U32) -> R U32 ()
  add (x, y) = let sum = x + y
                in sum < x || sum < y
                   | True -> Error ()
                   | False -> Success sum

|cogent| is a layout-sensitive language, like Python or Haskell.
In this function,
we bind the value of ``x + y`` to ``sum``.
In the body of the ``let ... in`` expression,
a pattern match is done
on the condition ``sum < x || sum < y`` ---
that is, if ``sum`` is less than ``x``
or less than ``y`` ---
and, if this condition is ``True``,
then we return an ``Error``.

``()`` is "unit", the single value of type ``()``
(also reads "unit"). If the condition is ``False``, which means that overflow didn't
happen, then we return ``Success sum``, which carries the summation.

That's pretty much all that we can do in |cogent|. We can save the above program in
a file called ``Adder.cogent``. For more information about the |cogent| language,
its syntax and semantics, you can read :doc:`../reference/surface-syntax`.

.. todo:: Part of the language reference will become a section in this doc later.

Next we will have to write the C code, which does
the things that |cogent| cannot do. |cogent| code will be compiled to C code, and is
always invoked as a subroutine, by a C program. The C programs we write for |cogent|
are not plain C; they are called *antiquoted C* (c.f. :doc:`../reference/antiquoted-c`).

.. code-block:: c
  :linenos:
  :emphasize-lines: 1,3,6,9,13

  $esc:(#include <stdio.h>)
  $esc:(#include <stdlib.h>)
  #include "generated.c"
  
  int main(void){
    $ty:(U32) first_num = 19;
    $ty:(U32) second_num = 2;
  
    $ty:((U32, U32)) args;
    args.p1 = first_num;
    args.p2 = second_num;
  
    $ty:(R U32 ()) ret = $exp:add(args);
    if(ret.tag == TAG_ENUM_Success){
      $ty:(U32) sum = ret.Success;
      printf("Sum is %u\n", sum);
      return 0;
    } else {
      printf("Error: Overflow detected.\n");
      return 1;
    }
  }

An antiquoted C file is very similar to a regular C file. The only
difference is that you can write *antiquotes* in the C code. An antiquote
is comprised of an antiquote name (e.g. ``$ty``, ``$exp``,
``$esc``, ``$spec``), a colon, and a |cogent| snippet enclosed by a pair of parentheses.
The purpose of having antiquotes is that you can refer to |cogent| types, expressions, etc.
without knowing what they get compiled to. In particular, with the current implementation of
the |cogent| compiler, it's very difficult to know what C names will be generated. See
`ticket #322 <https://github.com/NICTA/cogent/issues/322>`_ on GitHub.

Let's first look at the ``main`` function. In line 6, the antiquote ``$ty:(U32)``
means that we want to use a ``U32`` (a primitive type in |cogent|) equivalent in C. On line 9,
it's similar that we want a pair of two ``U32``\ s. Note the two pairs of
parentheses---the inner one is for the tuple, and the outer one is the antiquotation syntax.
Both of them are necessary. The ``$exp:add`` antiquote on line 13 is for
|cogent| expressions, in this case a function name. Strictly speaking, this antiquote
is not necessary, as we know that the C name of the |cogent| ``add`` function is ``add``.
However for polymorphic functions, the names of the generated C functions will be slightly
different than the |cogent| function name, in which case the antiquote is necessary.
Another minor syntactic flexibility that can be seen is that, if the antiquoted string is a single
identifier starting with a lowercase character, the enclosing parentheses can be omitted.

For more details about antiquoted C in |cogent|, see :doc:`../reference/antiquoted-c`.

Finally on line 1 of the antiquoted C program, the ``$esc`` tells the |cogent| compiler
not to preprocess the ``#include``. To understand the reason behind it, we need to briefly
talk about how antiquoted C is compiled by the |cogent| compiler: The compiler tries to parse
the antiquoted C files; however, because the syntax of C (or antiquoted C) is context-sensitive,
it needs to know what types have already been declared in the program. This requires
the antiquoted C files to be preprocessed by ``cpp``, inlining the included files.
The C parser that the |cogent| compiler uses does not support full GNU extensions, which means
if in your included files, unsupported syntax is used (which is very likely to be the case 
if you include Linux kernel headers, or ``glibc`` for example), then the parser will fail.
To work around this limitation, the files that contains unsupported features need to be
included, but enclosed by a ``$esc`` antiquote, so that they won't be expanded before parsing.
A file that includes all the type names declared in these excluded files will be passed
to the compiler via a flag ``--ext-types``. We will go through the compiler flags shortly.

On the contrary, |cogent|-generated C code can be parsed and should be included by ``cpp``.
That's the code on line 3. The name ``generated.c`` is specified by another
command-line argument to the compiler, which will be covered later. The |cogent| compiler
compiles |cogent| source code to C; it will generate a ``.h`` header file and a ``.c`` file.
Note that it should be the ``.c`` file that's included, instead of the header file as normal.

We name this antiquoted C file ``main.ac`` (``ac`` for "antiquoted C"). 

At this point we have all the source code that we need. As you should already know, |cogent| is
a code and proof co-generating compiler. As verification is more involved, we first only focus
on the C code generation part.

.. code-block:: bash

  cogent -g Adder.cogent -o generated \
    --infer-c-funcs="main.ac" \
    --cpp-args="\$CPPIN -o \$CPPOUT -P $CFLAGS" \
    --ext-types=types.cfg \
    --entry-funcs=entrypoints.cfg

The |cogent| compiler comes with hundreds of flags, here we only mention the most important ones.
To see the help message, you can run ``cogent -h<LEVEL>``. ``<LEVEL>`` ranges from ``0`` to ``4``.
``<LEVEL>`` is optional, default to ``1``. The higher the help level, the more options and flags
the help message is displayed. In general, the flags that only appear in higher help levels are less
important, **less stable**, or changing the compiler behaviours less significantly. 

The compiler has to be called with at least one *command*. A command indicates *what* the compiler does,
e.g. pretty-prints the core syntax tree, generates C code, generates the Isabelle/HOL embedding of the desugered
core language, etc. The compiler can do many things at once. In the command shown above, the ``-g`` is the
command---it generates C code. What follows is the |cogent| source file, ``Adder.cogent`` in this example.

All the rest are |cogent| *flags*. A flag controls or fine-tunes *how* the compiler behaves. Arbitrary number of flags
can be given.

* ``-o generated`` designates the output file name (only the base name is needed), and that's why we
  ``#included "generated.c"`` earlier in the ``main.ac`` file.

* ``--infer-c-funcs`` passes all the ``.ac`` files. More than one ``.ac`` files can be given, separated by spaces.

* The ``--cpp-args`` line is the command-line
  arguments passed to the C preprocessor, by default (GNU) ``cpp``. In the argument line passed to the preprocessor,
  ``\$CPPIN`` and ``\$CPPOUT`` are placeholders that will be replaced by the |cogent| compiler with the
  actual names of the files, as specified by |cogent| compiler flags such as ``-o``. Note that the ``\$`` is escaped
  in the Shell command as the dollar sign is part of the placeholders' names. ``-P`` inhibits generation of linemarkers
  by the preprocessor, which should always be used as the next stage of the compilation doesn't support
  linemarkers. ``$CFLAGS`` is defined as:

  .. code-block:: bash

      CFLAGS=-I. -I$COGENT_STDLIB -std=gnu99

  It just contains other standard flags that ``gcc`` and ``cpp`` demands. Normally ``-I`` for search paths,
  and ``-std`` for specific C standards. We use GNU C99. ``$COGENT_STDLIB`` points to the directory containing
  the standard |cogent| libraries. The source of the standard library is located in https://github.com/NICTA/cogent/tree/master/cogent/lib,
  but it will be installed (i.e. copied) to a build directory depending on how you installed your |cogent| compiler.
  See more information in :doc:`../reference/installation`. In this example, even no types or functions from the standard library is used,
  the generated program still needs the definition for the primitive types, which are defined in
  `cogent-defns.h <https://github.com/NICTA/cogent/blob/master/cogent/lib/cogent-defns.h>`_ in
  the ``$COGENT_STDLIB`` folder.

* ``--ext-types`` passes in a file named ``types.cfg`` containing a list of externally declared C types. We have explained earlier why
  a list of types are needed in order to parse C file correctly. In this case there's no type that are unknown
  to ``main.ac`` so the file is empty. Alternatively we can omit this flag and the empty file all together. The file name and its
  extension is arbitrarily chosen here.

* ``--entry-funcs`` informs the |cogent| compiler which |cogent| functions are needed by the ``.ac`` files. The |cogent|
  compiler only generates functions designated in the ``entrypoints.cfg`` file and their dependencies. Again the name
  of the file is not of any significance and can be anything. In this example, we have ``add`` in the file. The file
  should be formatted to have one function name per line.

Running this command, you should get a C file called ``main_pp_inferred.c``. The |cogent| compiler will first run the C
preprocessor and write to a file called ``main_pp.ac``. It then starts from there, compiling the antiquotes substituting
them with appropriate C code snippets, and writing to the final ``main_pp_inferred.c``. To debug antiquotes, it might be worth
looking at the ``main_pp.ac`` file as that's the one that the |cogent| compiler sees and on which it reports line numbers.

At this point, you have a C file (``main_pp_inferred.c``) which should be compiled by ``gcc``. Although the C code should
generally work with other compilers as well (e.g. `Clang <https://clang.llvm.org/>`_ or `CompCert <http://compcert.inria.fr/>`_), we only
officially support recent versions of `GCC <https://gcc.gnu.org/>`_.

You can find the complete code for this example in our `repository <https://github.com/NICTA/cogent/tree/master/cogent/examples/adder>`__.


