========================
Cogent Quick-Start Guide
========================


Environment
===========

The development is primarily done on recent versions of Debian GNU/Linux. Similar Linux
system should also work, but may require minor tweaks. MacOS generally works for the
Cogent compiler and its generated Isabelle/HOL proofs, but normally doesn't work natively
with the systems software that we developed. If you are on Linux, then just follow this
guide; if you are on MacOS, you'll additionally need ``gcc`` and some other GNU-compliant
packages. Keep an eye on some MacOS hints in :ref:`install-macos-hints` as you follow this
guide.


Installation
============

See `README.md <https://github.com/NICTA/cogent/blob/master/README.md>`_ for instructions.

.. _first-program:

Your first program
==================

The program we are going to walk through is a simple program which adds two
natural numbers up, and prints out the result, or reports an overflow
error.

Cogent is a restricted, pure, functional language. For example, Cogent is
unable to express I/O, memory management, loops or recursions. For this reason,
we only write the core functionality in Cogent, which adds up two natural numbers,
and check if overflow has happened. To carry the result of the check, we need
a result type::

  type R a b = < Success a | Error b >

It has similar meaning to a sum type in Haskell (or in any functional language)::

  data R a b = Success a | Error b

It says that, the result can be either a ``Success`` or ``Error``, and in each case
you also return the result associated with these tags, namely ``a`` and ``b`` respectively.
Note that ``R a b`` is polymorphic on ``a`` and ``b``. They can be instantiated to any
concrete types.

The difference to the Haskell version is that, the ``type`` keyword only introduces a
type synonym, which is to say, wherever an ``R a b`` is needed, it can be alternatively
spelt as ``< Success a | Error b >``, which of course is more verbose in many cases.

Next we define a function ``add``, which has the following type signature::

  add : (U32, U32) -> R U32 ()

``U32`` is an unsigned 32-bit integer; we use it to model natural numbers here. Cogent
also has built-in ``U8``, ``U16`` and ``U64`` for other sizes of unsigned integers.
A Cogent function only takes **one argument**. When we want to pass in two ``U32``\ s,
we make them into a pair (or a tuple, more generally).

The full definition of the ``add`` function is given below (also includes the previously
given type signature):

.. code-block:: none

  add : (U32, U32) -> R U32 ()
  add (x, y) = let sum = x + y
                in sum < x || sum < y
                   | True -> Error ()
                   | False -> Success sum

Cogent is a layout sensitive language, like Python or Haskell. In this function,
it binds the value of ``x + y`` to binder ``sum``. In the body of the ``let-in``
expression, a pattern match is done on the condition ``sum < x || sum < y`` (if
``sum`` is less than ``x`` or it's less than ``y``). If this condition is ``True``,
then we return an ``Error ()``. ``()`` is "unit", the single value of type ``()``
(also reads "unit"). If the condition is ``False``, which means that overflow didn't
happen, then we return ``Success sum``, which carries the summation.

That's pretty much all that we can do in Cogent. We can save the above program in
a file called ``Adder.cogent``. For more information about the Cogent language,
its syntax and semantics, you can read :doc:`surface`, the `Cogent language manual`_,
and a more technical `Cogent language reference`_.

.. _Cogent language manual: https://github.com/NICTA/cogent/tree/master/cogent/manual

.. _Cogent language reference: https://github.com/NICTA/cogent/blob/master/cogent/doc/doc.tex

.. todo:: Part of the language reference will become a section in this doc later.

Next we will have to write the C code, which does
the things that Cogent cannot do. Cogent code will be compiled to C code, and is
always invoked as a subroutine, by a C program. The C programs we write for Cogent
are not plain C; they are called *antiquoted C* (c.f. :doc:`antiquote`).

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
``$esc``, ``$spec``), a colon, and a Cogent snippet enclosed by a pair of parentheses.
The purpose of having antiquotes is that you can refer to Cogent types, expressions, etc.
without knowing what they get compiled to. In particular, with the current implementation of
the Cogent compiler, it's very difficult to know what C names will be generated. See
`ticket #322 <https://github.com/NICTA/cogent/issues/322>`_ on GitHub.

Let's first look at the ``main`` function. In line 6, the antiquote ``$ty:(U32)``
means that we want to use a ``U32`` (a primitive type in Cogent) equivalent in C. On line 9,
it's similar that we want a pair of two ``U32``\ s. Note the two pairs of
parentheses---the inner one is for the tuple, and the outer one is the antiquotation syntax.
Both of them are necessary. The ``$exp:add`` antiquote on line 13 is for
Cogent expressions, in this case a function name. Strictly speaking, this antiquote
is not necessary, as we know that the C name of the Cogent ``add`` function is ``add``.
However for polymorphic functions, the names of the generated C functions will be slightly
different than the Cogent function name, in which case the antiquote is necessary.
Another minor syntactic flexibility that can be seen is that, if the antiquoted string is a single
identifier starting with a lowercase character, the enclosing parentheses can be omitted.

For more details about antiquoted C in Cogent, see :doc:`antiquote`.

Finally on line 1 of the antiquoted C program, the ``$esc`` tells the Cogent compiler
not to preprocess the ``#include``. To understand the reason behind it, we need to briefly
talk about how antiquoted C is compiled by the Cogent compiler: The compiler tries to parse
the antiquoted C files; however, because the syntax of C (or antiquoted C) is context-sensitive,
it needs to know what types have already been declared in the program. This requires
the antiquoted C files to be preprocessed by ``cpp``, inlining the included files.
The C parser that the Cogent compiler uses does not support full GNU extensions, which means
if in your included files, unsupported syntax is used (which is very likely to be the case 
if you include Linux kernel headers, or ``glibc`` for example), then the parser will fail.
To work around this limitation, the files that contains unsupported features need to be
included, but enclosed by a ``$esc`` antiquote, so that they won't be expanded before parsing.
A file that includes all the type names declared in these excluded files will be passed
to the compiler via a flag ``--ext-types``. We will go through the compiler flags shortly.

On the contrary, Cogent-generated C code can be parsed and should be included by ``cpp``.
That's the code on line 3. The name ``generated.c`` is specified by another
command-line argument to the compiler, which will be covered later. The Cogent compiler
compiles Cogent source code to C; it will generate a ``.h`` header file and a ``.c`` file.
Note that it should be the ``.c`` file that's included, instead of the header file as normal.

We name this antiquoted C file ``main.ac`` (``ac`` for "antiquoted C"). 

At this point we have all the source code that we need. As you should already know, Cogent is
a code and proof co-generating compiler. As verification is more involved, we first only focus
on the C code generation part.

.. code-block:: bash

  cogent -g Adder.cogent -o generated \
    --infer-c-funcs="main.ac" \
    --cpp-args="\$CPPIN -o \$CPPOUT -P $CFLAGS" \
    --ext-types=types.cfg \
    --entry-funcs=entrypoints.cfg

The Cogent compiler comes with hundreds of flags, here we only mention the most important ones.
To see the help message, you can run ``cogent -h<LEVEL>``. ``<LEVEL>`` ranges from ``0`` to ``4``.
``<LEVEL>`` is optional, default to ``1``. The higher the help level, the more options and flags
the help message is displayed. In general, the flags that only appear in higher help levels are less
important, **less stable**, or changing the compiler behaviours less significantly. 

The compiler has to be called with at least one *command*. A command indicates *what* the compiler does,
e.g. pretty-prints the core syntax tree, generates C code, generates the Isabelle/HOL embedding of the desugered
core language, etc. The compiler can do many things at once. In the command shown above, the ``-g`` is the
command---it generates C code. What follows is the Cogent source file, ``Adder.cogent`` in this example.

All the rest are Cogent *flags*. A flag controls or fine-tunes *how* the compiler behaves. Arbitrary number of flags
can be given.

* ``-o generated`` designates the output file name (only the base name is needed), and that's why we
  ``#included "generated.c"`` earlier in the ``main.ac`` file.

* ``--infer-c-funcs`` passes all the ``.ac`` files. More than one ``.ac`` files can be given, separated by spaces.

* The ``--cpp-args`` line is the command-line
  arguments passed to the C preprocessor, by default (GNU) ``cpp``. In the argument line passed to the preprocessor,
  ``\$CPPIN`` and ``\$CPPOUT`` are placeholders that will be replaced by the Cogent compiler with the
  actual names of the files, as specified by Cogent compiler flags such as ``-o``. Note that the ``\$`` is escaped
  in the Shell command as the dollar sign is part of the placeholders' names. ``-P`` inhibits generation of linemarkers
  by the preprocessor, which should always be used as the next stage of the compilation doesn't support
  linemarkers. ``$CFLAGS`` is defined as:

.. code-block:: bash

    CFLAGS=-I. -I$COGENT_STDLIB -std=gnu99

  It just contains other standard flags that ``gcc`` and ``cpp`` demands. Normally ``-I`` for search paths,
  and ``-std`` for specific C standards. We use GNU C99. ``$COGENT_STDLIB`` points to the directory containing
  the standard Cogent libraries. The source of the standard library is located in https://github.com/NICTA/cogent/tree/master/cogent/lib,
  but it will be installed (i.e. copied) to a build directory depending on how you installed your Cogent compiler.
  See more information in :doc:`install`.

* ``--ext-types`` passes in a file named ``types.cfg`` containing a list of externally declared C types. We have explained earlier why
  a list of types are needed in order to parse C file correctly. In this case there's no type that are unknown
  to ``main.ac`` so the file is empty. Alternatively we can omit this flag and the empty file all together. The file name and its
  extension is arbitrarily chosen here.

* ``--entry-funcs`` informs the Cogent compiler which Cogent functions are needed by the ``.ac`` files. The Cogent
  compiler only generates functions designated in the ``entrypoints.cfg`` file and their dependencies. Again the name
  of the file is not of any significance and can be anything. In this example, we have ``add`` in the file. The file
  should be formatted to have one function name per line.

Running this command, you should get a C file called ``main_pp_inferred.c``. The Cogent compiler will first run the C
preprocessor and write to a file called ``main_pp.ac``. It then starts from there, compiling the antiquotes substituting
them with appropriate C code snippets, and writing to the final ``main_pp_inferred.c``. To debug antiquotes, it might be worth
looking at the ``main_pp.ac`` file as that's the one that the Cogent compiler sees and on which it reports line numbers.

At this point, you have a C file (``main_pp_inferred.c``) which should be compiled by ``gcc``. Although the C code should
generally work with other compilers as well (e.g. `Clang <https://clang.llvm.org/>`_ or `CompCert <http://compcert.inria.fr/>`_), we only
officially support recent versions of `GCC <https://gcc.gnu.org/>`_.

You can find the complete code for this example in our `repository <https://github.com/NICTA/cogent/tree/master/cogent/examples/adder>`__.


A more complicated example
==========================

In this example, we will focus on using abstract functions from the standard Cogent library, called ``libgum``.
The program generates the ``n``-th Fibonacci number using the generic iterator from ``libgum``.

.. code-block:: haskell
  :linenos:
  :emphasize-lines: 1,3,6,7,8,9,10

  include  <gum/common/iterator.cogent>
   
  @ fibonacci returns the n-th Fibonacci number.
  fibonacci : U32 -> U32
  fibonacci n =
     let ((_, fibn, _), _) = iterate #{
         gen = fib_gen,
         cons = fib_consume,
         acc = (0, 1, 1),
         obsv = n
         }
     in fibn

  @ fib_gen --- calculate the next Fibonacci number, unless we're finished.
  @ Accumulator contains (n-1)th and nth Fibonacci numbers, and n in third place.
  @ The accumulator returned by GeneratorResult has the same pattern; no value is returned for Stop / Yield etc.
  fib_gen : #{acc : (U32, U32, U32), obsv : U32} -> GeneratorResult () () () (U32, U32, U32)
  fib_gen #{acc = (n1, n2, n), obsv} =
    if | n == obsv -> ((n1, n2, n), Stop ())
       | else      -> ((n2, n1+n2, n+1), Yield ())
   
  @ fib_consume is a verbose no-op.
  fib_consume : #{obj : (), acc : (U32, U32, U32), obsv : U32} -> ConsumerResult () () (U32, U32, U32)
  fib_consume #{obj, acc, obsv} = (acc, Next)
   

On line 1, the ``include`` command imports the ``iterator.cogent`` file. There are two forms of ``include``
command in Cogent, either ``include "something.cogent"`` or ``include <somelib.cogent>``. They work in the
same way as their ``#include`` counterparts in C.

The comment after the ``@`` symbol on line 3 (and the other two functions) 
is for documentation generation, especially for
documenting libraries and APIs. They can be generated by Docgent, which can be run by
``cogent --docgent <COGENT_SRC>``, if your Cogent compiler is built with ``docgent`` flag
enabled. See :ref:`optional-features` on how to enable the flags.

On line 6, a function ``iterate`` is invoked. This is a very general iterator that Cogent's standard
library provides. Let's have a look at its type signature and some relevant type synonyms:

.. code-block:: haskell

  iterate : all (y, r, s, acc, obsv).
    #{ gen  : Generator y r s acc obsv!
     , cons : Consumer  y r s acc obsv!
     , acc  : acc
     , obsv : obsv!
     } -> IterationResult acc r s

  type GeneratorResult y r s acc = (acc, <Return r | Yield y | Stop s>)
  type Generator y r s acc obsv = #{acc : acc, obsv : obsv!} -> GeneratorResult y r s acc
  
  type ConsumerResult r s acc = (acc, <Return r | Stop s | Next >)
  type Consumer y r s acc obsv = #{obj : y, acc : acc, obsv : obsv!} -> ConsumerResult r s acc
  
  -- Return if the body (enumerator) returned a value, or Stop if generator had no more
  type IterationResult acc r s = (acc, <Return r | Stop s>)

The ``iterate`` function is polymorphic over type variables ``y``, ``r``, ``s``, ``acc`` and ``obsv``.
Because in this example, they will be instantiated to ``()``, ``()``, ``()``, ``(U32, U32, U32)`` and ``U32``
respectively, all of which are simple, the type inference engine is capable of knowing what they are.
In this case, type application to ``iterate`` is not necessary. You can nevertheless write them out as
``iterate [(), (), (), (U32, U32, U32), U32]`` if you think its more informative or clearer.

The function's argument is an unboxed record of four fields. In Cogent, each function can only
take exactly one argument. If more arguments are required, they can always be packed in a (usually unboxed)
record or a tuple. In the argument record, ``gen`` and ``cons`` are the
generator function and the consumer function respectively, which we will come back to shortly.
``acc`` is the accumulator, which is a read/write object that gets threaded through all the iterations.
``obsv`` is the observable object, which is a readonly (indicated by the ``!`` operator on its type)
object that the generator and/or the consumer can observe. As Cogent doesn't 
have closures, the ``gen`` and ``cons`` functions cannot directly access variables in
``iterate``'s scope; they have to be passed in explicitly as arguments. E.g. (in Haskell's syntax),
instead of

.. code-block:: haskell
 
  $> let v = 3
      in map (\a -> v + a) as
  
we have to write

.. code-block:: haskell

  g :: Int -> Int -> Int
  g a b = a + b

  $> let v = 3
      in map (g v) as

In each iteration, the generator is first called. The generator takes the accumulator (initial value)
and the observable, and generates a result of either ``Return``, ``Yield`` or ``Stop``, updating
the accumulator. If ``Return r`` or ``Stop s`` is returned, then the iteration will terminate immediately. 
The difference between them is that ``Return`` indicates that an early exit has happened, whereas
``Stop`` means the iterator has exhausted itself, terminating normally. If ``Yield y`` is returned,
the result ``y`` will be further processed (or consumed) by the consumer. The consumer ``cons``, takes
the result ``y`` of the generator, the accumulator and the observable as usual, returns a pair of the
updated accumulator, and either ``Return``, ``Stop`` or ``Next``. ``Return`` and ``Stop`` have the same
meaning as mentioned above; ``Next`` means it will enter the next iteration. The overall ``iterate`` function
will return the final accumulator, paired with the payload of either ``Return`` or ``Stop``, of different
types. As we can see, this iterator is very general, and there are more specific looping or recursion functions
defined in other files in the ``libgum``.

In the code snippet above, all the work is done in the generator function; the consumer function
just returns the accumulator unchanged, together with a ``Next`` tag to keep looping.
As you can see, iteration is verbose.

The accumulator is a triple. Its first two terms are the ``n-1``-th and ``n``-th Fibonnaci numbers.
Its third term is ``n``. Each time ``fib_gen`` is invoked, it adds the first two terms
together, increments ``n`` and creates a new accumulator:

.. table::
  :align: center
  :widths: auto

  ====  ==============
  Step    Accumulator
  ----  --------------
  1       (0,1,1)
  2       (1,1,2)
  3       (1,2,3)
  4       (2,3,4)
  5       (3,5,5)
  6       (5,8,6)
  ====  ==============

When the third term reaches the observer (here just a ``U32``), the generator
returns ``Stop`` to end the loop; the pattern in the main function picks
out the second term in the triple as the return value for the Fibonacci function.

In the antiquoted C file, the ``main`` function invokes the ``fibonacci`` function
and prints the tenth such value::

  $esc:(#include <stdio.h>)
  #include "fib.c"
  #include <gum/anti/iterator.ac>
   
  int main(void)
  {
     u32 n;
     n = $exp:fibonacci(10);
     printf("10th Fibonacci is %u\n", n);
     return 0;
  }

The building process is very similar to the previous example (c.f. :ref:`first-program`).
The complete code and Makefile for this example can be found
`here <https://github.com/NICTA/cogent/tree/master/cogent/examples/fib>`__.

Example: polymorphic abstract types
===================================


Example: building Isabelle proofs
=================================

.. todo:: An example doing verification.

