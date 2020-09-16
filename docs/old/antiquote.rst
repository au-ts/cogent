============
Antiquoted C
============


**WARNING:** Cogent antiquotation currently does **not** have any sanity
checks. So please follow the guide closely otherwise debugging could be
a huge pain.

Cheatsheet
==========

.. note::  New users: please skip this section.

==========      =====================
Antiquotes      Explanation
----------      ---------------------
``$id``         for function identifiers or type identifiers when defining them
``$ty``         refer to a Cogent type
``$exp``        call a Cogent function, which has to have exactly one
                argument, as in Cogent; any Cogent expressions
``$spec``       specify the Cogent type of a C function (using typecast
                syntax), which is applied to exactly one argument
``$esc``        macros that should not be preprocessed before antiquoted C is compiled
==========      =====================


Overview
========

Cogent is a restricted language; there are many things that Cogent
cannot express and should be deferred to native C code. In the foreign
function interfaces between Cogent and C, it can be seen that accessing
C code from Cogent and the other direction are not symmetric, as Cogent
will be generated to C code. To access C code from Cogent, programmers
write abstract types (types without definitions) and abstract functions
on the Cogent side , and on the C side define the implementation of the
types and functions. For the compiler to realise which implementation is
for which interface, we need to make sure that the name of both sides
coincide. But there is a problem: Cogent is polymorphic, and is
structurally types, whereas C is monomorphic and nominally typed. What
it means is that the Cogent compiler will generate "random" names for
the generated interfaces (of course they are not truly random, they are
just so random that a programmer can barely guess what they will be; see
`#322 <https://github.com/NICTA/cogent/issues/322>`_ for more details). To make
the names on both sides coincide, Cogent provides a way for programmers
correctly "guess" the generated names—antiquotations. That's why the C
components one write for a Cogent program is generally referred to as
**antiquoted C** (it's because we borrow the syntax of antiquotes; see
G. Mainland, `Why it's nice to be quoted: quasiquoting for
Haskell <https://www.cs.tufts.edu/comp/150FP/archive/geoff-mainland/quasiquoting.pdf>`_).
And for accessing Cogent code from C, programmers also need a way to
refer to the Cogent names. In a nutshell, in antiquoted C, programmers
can write Cogent snippets (e.g. Cogent types, polymorphic function
names, and many other things) and the Cogent compiler will compile each
snippet in the same way as it compiled the Cogent program, resulting in
a coherent set of names generated.

Modes in the compiler
=====================

We have two different modes for handling antiquotation. One is *type
mode*, with command-line argument ``--infer-c-type``. In this mode,
users can only define abstract parametric Cogent types. The output will
be placed to pre-defined directory, one file per monomorphised type.
Each file is ``#include``\ -d by the generated ``.h`` file. Another mode
is *function mode*, which is enabled by ``--infer-c-func`` flag to the
compiler (note: these two modes are not mutually exclusive). This mode
is for everything else, and the output filename is derived from the
input filename.

Function definitions
====================

We can define an abstract function which has been declared in Cogent.
For example, in Cogent we have:

::

  foo : all (a, b). a -> b

Then in C, we can define function ``foo`` by

.. code-block:: c
    
  $ty:b $id:foo ($ty:a arg) {
    // ...
  }

``$id``, ``$ty`` are antiquotes for identifiers and types respectively.
If the antiquoted code consists of only one single identifier **starting
with a lower-case letter**, then no parenthesis are required (e.g.
``$ty:acc``), otherwise we have to write parentheses around it, like
``$ty:(R a b)`` and ``$ty:(U32)``. Note: If the antiquoted type is unit
or a tuple, then we have to have at least two pairs of parentheses, the inner
one for the tuple, and the outer one for antiquotation.

Functions defined using antiquotation can be parametrically
polymorphic, ad hoc polymorphic or monomorphic.
``$id`` is mostly needed by poly-functions only. [#id-mono]_
The reason behind it is, a mono-function will be generated to a C
function with exactly the same name (modulo unsupported identifier
characters), thus the function name will stay intact. For a
poly-function, as we can see from the example above, the user doesn't
write ``all`` quantification as in Cogent. Type parameters, if any, are
introduced **implicitly** by the corresponding declaration in Cogent,
namely ``a`` and ``b`` in the above instance. Besides, we need to
generate new function names according to the instantiation. For these
reasons, the compiler needs to know what and where the function name is,
in order to establish a connection to the Cogent counterpart and to
generate new function instantiations. Thus ``$id`` is a needed as a
signal to the function name. The compiler then will generate one copy
for each monomorphisation.

In a function definition, other forms of antiquotes are supported. By
``exp:f``, we can invoke Cogent function ``f``. (In fact, ``$exp``
theoretically supports all kinds of Cogent expressions, but this feature
is not well tested and largely experimental. Use with care!) As in
Cogent, if this function ``f`` is polymorphic, then it has to be fully
applied to types. To call higher-order functions, as the function and
its argument are usually not given by Cogent antiquotes (i.e. they are C
expressions), we cannot directly call it using the ``$exp``
antiquotation as above. E.g. we have the following scenario:

.. code-block:: c

  void foo ($ty:((A -> B, A)) arg) {
    // ...
  }

To apply the first component of the pair ``arg.p1`` to the second
``arg.p2``, in order to generate the dispatch function, we have to give
the type of the function – ``arg.p1`` – to the compiler. We write

.. code-block:: c

  (($spec:(A -> B)) arg.p1) (arg.p2);  // the parens around type specifier and function is necessary!

The syntax is actually for typecasting in C, we hijack (or better,
embed) our semantics in it. This satisfies our principle that everything
inside an antiquote is valid Cogent code.

One thing also worth mentioning here is that, antiquoted functions (no
matter first order or higher order) can only be applied to exactly one
argument, as in Cogent. Otherwise it will generate totally nonsensical
code and the error message from the C compiler will not help in general.
We are trying to implement some sanity checks in the antiquotation part.

Type declarations / Typedef's
=============================

Similarly, we can define **abstract** Cogent types using antiquotation.
For example,

::

  -- Cogent
  type R a b
  type T a b c

.. code-block:: c
  
  // Antiquoted-C
  struct $id:(R a b) {
    // ...
  };

  typedef struct $id:(T x y z) {
    // ...
  } $id:(T x y z);

  typedef struct $id:(R a b) $id:(R a b);

Most of the knowledge about it can be deduced from previous section,
which will not be repeated here. One difference is that users need to
write fully applied type constructors, namely with type arguments, and
they have to be identical to those given in Cogent. When using
``typedef``, only one synonym can be given, if it's antiquoted. And it
has to be the same as the type it is defined to. Something like
``typedef struct $id:(X a) $id:(Y a)`` is invalid.

Non-parametric abstract types cannot be used in this way, otherwise they
will be put to the wrong output file. In order to refer to any Cogent
types in the definition, what the users can do is to **NOT** antiquote
the type name, and use it in the function mode, as the type name in C
will be exactly the same as that in Cogent (modulo namespace renaming).
E.g.,

::

    -- Cogent
    type R

.. code-block:: c
    
    // Antiquoted-C
    struct $id:(C) { ... };  // wrong!
    struct C { ... };        // correct!

Escape sequences
================

Any C code which is beyond the reach of the Haskell C parser
(http://hackage.haskell.org/package/language-c-quote) should be wrapped
by a ``$esc``. In particular, if you have any ``#include``'ed files that
don't want to be preprocessed (usually for the reason that they contain
some language extensions which our C parser does not support), use
``$esc`` antiquote to escape.

Cogent also supports conditional compilation in the style of cpp (C
preprocessor). Directives (e.g. ``#define``, ``#if``, etc.) should also
be wrapped in ``$esc`` so that they are left to the C compiler, instead
of (mistakenly) being processed by Cogent's C preprocessor. For
statement level directives, you need the alternative ``$escstm``
antiquote specifier rather than ``$esc``.

Expressions
===========

We can antiquote any valid Cogent expressions, using ``$exp`` antiquote.
They will be turned to **statement-expression** in C.

.. rubric:: Footnotes

.. [#id-mono] One special case is that, if you have an abstract monomorphic function which
              uses a parametric abstract type (but instantiated, of course) that is not used anywhere else in
              your Cogent program, and if ``$id`` is not used on the function name, 
              then this function will not be processed by the monomorphiser, thus always
              dumped to the final artifact. But the parametric type, because no Cogent
              function uses it (or no Cogent function specified in the ``--entry-funcs`` flag uses it),
              it will not be generated in the C code, leading to a used-but-not-defined type.
              It happens when you import such a library, which contains functions that you
              never use.
              In this case, use the ``$id`` antiquote on the function name. It will treat the
              function as a poly-function, thus processed by the monomorphiser. The compiler can then know
              that you indeed don't use this function and won't produce it in the final C program.

