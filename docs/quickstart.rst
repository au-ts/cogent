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

See :doc:`install` for instructions.

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
  See more information in :doc:`install`. In this example, even no types or functions from the standard library is used,
  the generated program still needs the definition for the primitive types, which are defined in
  `cogent-defns.h <https://github.com/NICTA/cogent/blob/master/cogent/lib/cogent-defns.h>`_ in
  the ``$COGENT_STDLIB`` folder.

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
defined in other files in the ``libgum``. The Cogent FFI of these types and functions can be found
in `cogent/lib/gum/common/iterator.cogent <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/common/iterator.cogent>`__
and the underlying C definitions in
`cogent/lib/gum/anti/iterator.ac <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/anti/iterator.ac>`__.

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

.. _poly-function-example:

Example: abstract types and polymorphic functions
=================================================

In the previous example, we have shown some of the ``libgum`` functions---they are
*abstract functions*, in the sense that we only declare them in Cogent, and defer
their definitions to C. Cogent also offers *abstract types*. An abstract type is a 
type that only gets declared in Cogent, but is defined in C.

If we want to declare two abstract types ``A`` and ``B``, we write in Cogent:

.. code-block:: haskell

  type A
  type B

Cogent assumes nothing but that they are boxed types, allocated on the heap and is access by a pointer.
Boxed abstract types are by definition linear in Cogent's type system. Whenever you use a value of type
``A`` in Cogent, it will always be a pointer to type ``A`` in the generated C code.

In C, we can give concrete definitions for these types, for example:

.. code-block:: c

  typedef char A;
  typedef struct { int b; } B;

.. note:: If in your Cogent source file, there're only type definitions and no function definitions, then
          Cogent will not generate any types in the C file. And Cogent will only generate types that
          get used by at least one function.

Now we need to add some Cogent functions to work on these types.
For example, we define a very simple Cogent function::

  swapDrop : all (a, b, c :< DS). (a, b, c) -> (b, a)
  swapDrop (a, b, c) = (b, a)

``swapDrop``, as its name suggests, it swaps the first two components in the argument tuple,
and drops the last element. ``all (a, b, c :< DS)`` universally quantifies type variables
``a``, ``b`` and ``c``. Additionally, it says that ``c`` is constrained to have ``DS`` permissions
(see more details in :ref:`permissions`). ``D`` and ``S`` mean that the type ``c`` has to be
``D``\ iscardable and ``S``\ hareable respectively, i.e. non-linear, and that's why the third component in the tuple
can be dropped (or, discarded). Strictly speaking, ``S`` is not needed here, as we don't share it.
But it's more conventional to use ``DS`` together, as ``D`` and ``S`` together denote linearity.

The ``main.ac`` file has some trickiness:

.. code-block:: c
  :linenos:
  :emphasize-lines: 4,5,7,17

  $esc:(#include <stdlib.h>)
  $esc:(#include <stdio.h>)
  
  typedef char A;
  typedef struct { int b; } B;
  
  #include "swap-drop.c"
  
  int main() {
    A *a = (A*)malloc(2 * sizeof(char));
    B *b = (B*)malloc(sizeof(B));
    a[0] = '!';
    a[1] = '\0';
    b->b = 42;
  
    $ty:((A,B,U32)) arg = { .p1 = a, .p2 = b, .p3 = 12 };
    $ty:((B,A)) ret = $exp:(swapDrop[A,B,U32])(arg);
    
    printf("fst = %u\n", ret.p1->b);
    printf("snd = %s\n", ret.p2);
    return 0;
  }

On line 4 and 5, we give definitions for types ``A`` and ``B``, as we have discussed above.
It's worthy noting that on line 7, we include the generated C file. It has to come after
the definitions of ``A`` and ``B``, as the generated C code rely on the definition of them.
Finally on line 17, we use an antiquote ``$exp`` to refer to the Cogent function ``swapDrop``.
The type arguments of this function have to be fully applied, as in this ``main.ac`` file,
the Cogent compiler doesn't know what instantiation it has, thus unable to infer.

As before, we need an ``entrypoints.cfg`` file to pass to the ``--entry-funcs`` argument. In this
file, the only function needs to be included is ``swapDrop[A,B,U32]``. Again, for the same reason,
the type arguments have to be fully applied. As the programmer, you are responsible for ensuring
that the ones passed to ``--entry-funcs`` are consistent with what get used in the antiquoted C files.
The Cogent compiler doesn't perform any sanity checks.


Example: polymorphic abstract types
===================================

Now let's explore some more advanced features of Cogent. Cogent allows types to be parametric, including
abstract types. Typical examples include containers: arrays, lists, trees, etc.
Functions operating on these parametric abstract types are polymorphic, and share the same interface.
These functions are normally parametrically polymorphic, meaning that they are generic over types.

.. note:: Cogent allows for ad hoc definitions of some instances of a polymorphic function,
          but we won't go into it in this example. We only consider parametric polymorphism here.

.. code-block:: haskell

  include <gum/common/wordarray.cogent>
  
  map : WordArray U32 -> WordArray U32
  map arr = let view = wordarray_view (arr, 3, 6, 1)
            and view' = wordarray_map_view (view, triple)
             in wordarray_unview view'
  
  triple : U32 -> U32
  triple x = 3 * x

In this example, we write a small Cogent function ``map`` which maps a slice
of a wordarray. A wordarray is a dynamically allocated array in C, with
unsigned integers (of the same type) as its elements. ``WordArray a`` is an abstract
type defined in `cogent/lib/gum/common/wordarray.cogent <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/common/wordarray.cogent>`__, where ``a`` is the element type of that array.
``wordarray_view (arr, fr, to, st)`` is a polymorphic function over the element type ``a``, creating a
writable *view* into a slice of an array ``arr``, starting from the ``fr``-th element (inclusive), with step
``st``, and ending at the ``to``-th element (exclusive).
``wordarray_map_view`` maps over every element in the view, and returns the updated slice. The updates
are performed in-place, resulting in more performant C code. Finally ``wordarray_unview`` converts a view
back to a regular array. This piece of Cogent program is relatively simple. 

In the companion ``main.ac`` file, the ``main`` function is straightforward: we call the Cogent ``map``
function as ``map (arr)``. Here we don't even need to use the ``$exp`` antiquote, as we can already
know that the generated C function name of ``map`` is identical to its Cogent name, given that
this function is monomorphic. 

The antiquoted C file giving the definitions of the abstract functions for wordarray can be found
in `cogent/lib/gum/anti/wordarray.ac <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/anti/wordarray.ac>`__
and is standard. What's not so obvious is how to define the abstract type of wordarray.

Unlike the previous example that we could define the (monomorphic) abstract types in the ``main.ac`` file,
here we need to create another type of antiquoted file---a ``.ah`` file---antiquoted header file.
The antiquoted header files are passed to the ``--infer-c-types`` argument, contrary to the ``--infer-c-funcs`` argument.
The reason why ``.ah`` files are different from ``.ac`` files is that, we know what
types a polymorphic function should be instantiated to according to the explicit type applications in the ``.ac`` file,
as in ``$exp:(swapDrop[A,B,U32])`` in the previous example. For types, however, we
work out the instantiations depending on what instances are **used** in your Cogent functions.

.. note:: It's only used if it's a dependency of at least one function specified in ``--entry-funcs``.

The definition of ``WordArray a`` is given below (also in the repository in
`cogent/lib/gum/anti/abstract/WordArray.ah <https://github.com/NICTA/cogent/blob/master/cogent/lib/gum/anti/abstract/WordArray.ah>`__):

.. code-block:: c

  struct $id:(WordArray a) {
  	int len;
  	$ty:a* values;
  };
  
  typedef struct $id:(WordArray a) $id:(WordArray a);

In the Cogent standard library, a wordarray is defined to be a struct, consisting of two fields:
``len`` stores the length of the wordarray, and ``values`` is a C array holding the contents.

Let's come back to the ``main.ac`` file. The first few lines look like:

.. code-block:: c

  $esc:(#include <stdio.h>)
  $esc:(#include <stdlib.h>)
  $esc:(#include <string.h>)
  
  #include "mapper.c"
  #include <wordarray.ac>

We only need to include the ``.ac`` files, as the ``.ah`` files will be automatically
included in the generated ``mapper.h`` file. After all, the function declarations and definitions
there rely on the definitions of the abstract types.

We can have a brief look at how they are included:

.. code-block:: c

  #include <abstract/WordArray_u32.h>
  #include <abstract/View_WordArray_u32.h>
  struct t2 {
      View_WordArray_u32 p1;
      t1 p2;
  } ;

Once the parametric abstract type is needed, the Cogent compiler will generate lines
to include the monomorphised definitions of the parametric types. 

The build command (in a Makefile) is:

.. code-block:: make

	cogent $(SRC) -g -o$(OUTPUT) \
		--abs-type-dir="$(ABSDIR)" \
		--infer-c-types="$(AHFILES)" \
		--infer-c-funcs="$(ACFILES)" \
		--cpp-args="\$$CPPIN -o \$$CPPOUT -E -P $(CFLAGS)" \
		--entry-funcs=entrypoints.cfg

``$(ABSDIR)`` is the directory containing the generated definitions of parametric types.
All the generated header files will be placed in ``$(ABSDIR)/abstract``, which
must already exist before this command is run. ``$(AHFILES)`` needs to include all the
needed ``.ah`` files, and ``$(ACFILES)`` here is only the ``main.ac``, since the other ``.ac`` files
are already included in ``main.ac``.

The code for this example can be found in the `repository <https://github.com/NICTA/cogent/tree/master/cogent/examples/mapper>`__.


Example: building Isabelle proofs
=================================

.. todo:: An example doing verification. Maybe focus on how to write the Makefile
          for verification and code generation, rather on the Isabelle proofs themselves.

