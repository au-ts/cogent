************************************************************************
			    A First Program
************************************************************************


The program we are going to walk through is
a simple program which adds two natural numbers up,
and prints out the result, or reports an overflow error.


The Business End: ``add``
========================================================

|cogent| is a restricted, pure, functional language.
For example, |cogent| is unable to express
input/output operations, memory management, and loops.
For this reason, we will only write
the core functionality in |cogent|,
which adds up two natural numbers,
and check if overflow has happened.

To do that,
we'll build up an ``add`` function in stages,
and we'll point out language features
as we encounter them.


``add``, version 1: Hello, Cogent!
------------------------------------

Let's start with a very simple function, ``add``,
which cannot yet handle overflow detection.
As with many other functional languages,
we do so by first giving its type signature::

  add : (U32, U32) -> U32

Now, similar to Haskell,
we give a function's definition
by declaring the computation it does.
Our first attempt at writing ``add`` might look like::

  add : (U32, U32) -> U32
  add (x, y) = x + y

``add (x, y)`` becomes ``x + y``.
Thanks to *pattern matching*,
the names ``x`` and ``y`` bind to
the values passed in.
Unlike many other functional languages,
|cogent| functions can only take one argument.
When we wish to pass two ``U32``\ s,
we must glue them together
so they appear as one value ---
more generally, we form a tuple.


``add``, version 2: Let's Consider...
------------------------------------

If we want to consider the result,
we can bind it to a name ourselves,
using a ``let`` expression:
names bound by the ``let``
are usable in the ``in`` that follows::

  add : (U32, U32) -> U32
  add (x, y) = let sum = x + y in sum

For those familiar with
other functional languages,
a word of warning:
``let`` in |cogent|
is not *quite* what you will expect.
More on that in the reference manual.

|cogent| is a layout-sensitive language,
like Python or Haskell,
so we may rearrange our expression
to make it more readable.
You may prefer::

  add : (U32, U32) -> U32
  add (x, y) = let sum = x + y
               in sum

Or, alternatively::

  add : (U32, U32) -> U32
  add (x, y)
    = let sum = x + y
      in sum

But all three forms here are equivalent.


``add``, version 3: An Iffy Question
------------------------------------

Now, let's consider
the result of the addition
and, if it is less than
either of its two operands ---
that is, ``sum < x || sum < y`` ---
we'll consider that an overflow occurred.
We can use
an ``if`` expression
to check its value::

  add : (U32, U32) -> U32
  add (x, y) = let sum = x + y
               in if sum < x || sum < y
                  then {- ??? -}
                  else sum

We need to return *something*
in the hole above,
denoted by the block comment ---
``{-`` and ``-}`` delimit
a (nestable) block comment in |cogent|;
similarly, ``--`` introduces
a comment to the end of the line ---
so what *is* our error value?

We need to return
two different values
from this function:
one, to denote an error,
and one to denote success.
We could use a tuple here::

  add : (U32, U32) -> (U32, Bool)
  add (x, y) = let sum = x + y
               in (sum, sum < x || sum < y)

But that's awful.
We need to explicitly check the Boolean value
(for that is what the ``Bool`` type denotes)
every time we use this function.

So, how do we do better?


``add``, version 4: A New Type of Trouble
-----------------------------------------

To carry the result of the check,
we need a result type indicates
either a successful addition or an error occurred.
We will define a *sum type*,
somewhat akin to a tagged-union in C,
with two *tags* or *variants*:
``Success`` and ``Error``::

  type R = < Success | Error >

This now means our ``add`` function can become::

  add : (U32, U32) -> (U32, R)
  add (x, y)
    = let sum = x + y
      in if sum < x || sum < y
         then (sum, Error)
         then (sum, Success)

But this highlights the *other* problem:
when we return ``Error``,
the value in ``sum`` is notionally meaningless.

What we *need* is a way to
attach the value to the sum type.
And we're in luck:


``add``, version 5: Tag! You're It
------------------------------------

For any particular tag,
a sum type can have
associated values::

  type R = < Success U32 | Error >

Now, ``Success`` has an associated ``U32``,
which means we can improve
our ``add`` function again::

  add : (U32, U32) -> R
  add (x, y)
    = let sum = x + y
      in if sum < x || sum < y
         then Error
         then Success sum

That's more like it!
But we can do better.


``add``, version 6: Polymorphism
------------------------------------

An operation that may be successful or not
is a surprisingly common pattern to program to.
Our ``R`` type could come in handy for other cases;
except we would need to create new types
for all possible successful values.
We might like to make a generic result type::

  type R a = < Success a | Error >

This type is *polymorphic*,
as it has a *type variable*, ``a``:
the value in the ``Success`` variant
has some currently-unknown type ``a``.
Type variables tend to be written in lower-case.

We can't directly use this
without replacing the type variable
with a concrete type in a *type instantiation*:
so, to get the ``< Success U32 | Error >``
we had earlier,
we would instantiate this type as ``R U32``.

Using this redefined ``R``,
the type of the ``add`` function changes slightly,
but its definition remains the same::

  add : (U32, U32) -> R U32


``add``, version 7: But In General...
-------------------------------------

Actually,
we could return something useful
in the event an error occurred.
Let's have a general result type::

  type R a b = < Success a | Error b >

Both ``Success`` and ``Error``
now have associated values of
two different, though not necessarily distinct, types.

This construct has a similar meaning to
Haskell's sum types
(or, indeed, the sum types
in any functional language)::

  -- in Haskell, we might say:
  data R a b = Success a | Error b

However, one notable difference is that,
in Haskell, this would introduce a new type;
but in |cogent|,
the ``type`` keyword only introduces a *type synonym*:
wherever an ``R a b`` is needed,
we may equivalently spell it in full as
``< Success a | Error b >``.

The type of the ``add`` function
changes slightly again::

  add : (U32, U32) -> R U32 {- ??? -}

But now we need a type (and a value)
for the ``Error`` variant;
we cannot leave it empty!
We can use the *unit* type, ``()``,
another |cogent| built-in type
which is similar to the unit type
in many other functional languages.
Think of it as a zero-element tuple
that therefore only has one value:
the empty tuple constructor,
spelled ``()``.

So, if we wanted to write
a very pessimistic version of function,
we could say::

  add : (U32, U32) -> R U32 ()
  add (x, y) = Error ()

So, our ``add`` function,
generalised over our result type,
looks like::

  add : (U32, U32) -> R U32 ()
  add (x, y)
    = let sum = x + y
      in if sum < x || sum < y
         then Error ()
         then Success sum


``add``, version 8: A Pattern Emerges
-------------------------------------

But there's just enough time
for one more version.
A much more common way to do it
is to use *pattern matching* again ---
if you recall,
we're already using it
to extract the values of
``x`` and ``y``
from the tuple of arguments.
Pattern-matching is much more powerful, though.

Dealing with sum types is very common,
so |cogent| has specialised syntax for
considering each possibility of a sum type:
we list each variant after a vertical bar,
optionally with some bindings,
and give the expression to resolve to::

  add : (U32, U32) -> R U32 ()
  add (x, y)
    = let sum = x + y
      in sum < x || sum < y
	 | True  -> Error ()
	 | False -> Success sum

For our ``R`` type, we can do something similar.
Here's a contrived example using it::

  fn () = add (7, 6)
        | Success x -> x
        | Error   y -> 42

That's pretty much all that we can do in |cogent|.
We can save our favourite definition of ``add``,
along with the type ``R``,
into a file called ``Adder.cogent``.
For more information about the |cogent| language,
its syntax and semantics,
you can read :doc:`../reference/surface-syntax`.

.. todo:: Part of the language reference will become a section in this doc later.



Gum, Glue, and Antiquoted C
======================================================

At this point,
we could run the |cogent| compiler,
and we'd get some code out::

  $ cogent -g Adder.cogent
  Parsing...
  Resolving dependencies...
  Typechecking...
  Desugaring and typing...
  Normalising...ANF
  Re-typing NF...
  Simplifying...
  Skipped
  Monomorphising...
  Re-typing monomorphic ASST...
  Generating C code...
    > Writing to file: ./Adder.h
    > Writing to file: ./Adder.c
  Compilation finished!

|cogent| code is compiled to C code,
and is always invoked as a subroutine by a C program:
remember that, from |cogent| code,
many operations aren't possible,
but within the framework of a larger program,
we can build quite powerful systems.

The compiled result is not at all pleasant to read,
nor is it especially easy to interact with.
So while we *could* pick through
the generated ``Adder.c`` and ``Adder.h``,
and work out the exact construct we need,
it's much easier to have the |cogent| compiler
help us out by generating much of
the glue needed to run our functions.

We'll write in C --- but not *plain* C.
We write in a syntax called
`*Antiquoted C* <:doc:../reference/antiquoted-c>`_,
which lets us interface regular C constructs
with |cogent| types and functions.

An Antiquoted C file is
very similar to a regular C file ---
indeed, it's very nearly a superset of C.
The only difference is
you may introduce *antiquotes* into the C code.
An antiquote is comprised of a name
(e.g., ``$ty``, ``$exp``, ``$esc``),
a colon, and a |cogent| snippet
enclosed by a pair of parentheses.
These allow us to refer to
types and expressions in our programs
without needing to know
exactly what they were compiled to.
This is especially important
as the current |cogent| compiler
does not generate predictable C names;
see `issue #322 <https://github.com/NICTA/cogent/issues/322>`_.

With that in mind,
let's write some Antiquoted C.

.. code-block:: c

   int main (void)
   {
       return 0;
   }


.. code-block:: c
   :linenos:
   :emphasize-lines: 1,3,6,9,13

   $esc:(#include <stdio.h>)
   $esc:(#include <stdlib.h>)
   #include "generated.c"

   int main (void)
   {
       $ty:(U32) first_num = 19;
       $ty:(U32) second_num = 2;

       $ty:((U32, U32)) args;
       args.p1 = first_num;
       args.p2 = second_num;

       $ty:(R U32 ()) ret = $exp:add(args);
       if (ret.tag == TAG_ENUM_Success) {
           $ty:(U32) sum = ret.Success;
           printf("Sum is %u\n", sum);
           return 0;
       } else {
           printf("Error: Overflow detected.\n");
           return 1;
       }
   }


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


