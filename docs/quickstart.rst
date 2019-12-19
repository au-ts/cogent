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

See https://github.com/NICTA/cogent/blob/master/README.md for instructions.


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
given type signature)::

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
are not plain C; they are called *antiquoted C* (c.f. :doc:`antiquote`).::

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
      u32 sum = ret.Success; // $ty:(U32) <=> u32
      printf("Sum is %u\n", sum);
      return 0;
    } else {
      printf("Error: Overflow detected.\n");
      return 1;
    }
  }

.. todo:: Finish this example.

