************************************************************************
                              Antiquoted C
************************************************************************

.. warning::
   Cogent antiquotation has almost no checking.
   Be very, very careful,
   as it is easy to write invalid constructs
   that won't parse or won't compile,
   and which are extremely hard to debug.

|cogent| is a substantially restricted language:
many operations cannot be expressed,
and those must instead be implemented in C.
To access functions written in C from |cogent|,
one writes abstract types and abstract functions.
To access functions written in |cogent| from C,
more capability is required.

*Antiquoted C* is the mechanism by which
we can invoke |cogent| from C.
For the most part,
Antiquoted C is syntactically identical to C.
However, there are certain constructs
where the underlying C parser
will incorrectly reject otherwise-valid constructs.
But Antiquoted C also behaves
a little like a template language,
and this is what we're interested in.


Antiquotes
====================================

Antiquoted C introduces an *antiquote*,
which takes the form
``$``, quotation type, ``:``, and a (usually parenthesised) term;
and it denotes an item in C that
the |cogent| compiler must understand
and potentially transform.
It is wise to parenthesise the term,
to make it visually evident
it is distinct from the C around it.
Quotation types influence this transformation,
and there are several quotation types:

- ``$id:(IDENT)`` introduces ``IDENT`` as an identifier;
- ``$ty:(TYPE-NAME)`` refers to the type ``TYPE-NAME``;
- ``$exp:(EXPRESSION)`` inserts code to execute ``EXPRESSION``;
- ``$spec:(TYPE-NAME)`` injects an appropriate C typecast; and
- ``$esc:(PREPROCESSOR-DIRECTIVE)`` and
  ``$escstm:(PREPROCESSOR-DIRECTIVE)``
  allow insertion of a literal C preprocessor directive.

We'll look at each of these in detail.


``$id``: Introducing Identifiers
------------------------------------

``$id:(IDENT)`` introduces ``IDENT`` as an identifier
at the point of declaration, either of a function or a type::

  void $id:(stare_into_abyss) (void) { /* ... */ }

  struct $id:(by_lightning) { /* ... */ }

Often, these aren't required:
if there are no type parameters,
as might be the case with ``stare_into_abyss`` above,
this declaration can occur without antiquotes.


``$ty``: Talking Types
------------------------------------

``$ty:(TYPE-NAME)`` refers to the type ``TYPE-NAME``,
which may be any type known to |cogent|,
especially those that include a type parameter
and which C cannot itself express.

For example, we could declare a function
that uses C's coercion of U8 to U32::

  $ty:(U32) u32_from_u8 ($ty:(U8) x) { return x; }

At compilation,
|cogent| will replace the ``$ty`` term with
a corresponding C type,
so the generated result would be::

  u32 u32_from_u8(u8 x) { return x; }


This works for less-trivial types as well.
In |cogent|,
if we declare the types ``Result``, ``FileDesc``, ``Errno``,
and a function of them, ``openf``::

  type Result t e = < Ok t | Err e >
  type FileDesc   = U32
  type Errno      = U32
  openf: U32 -> Result FileDesc Errno

We can then implement this function in C::

  $ty:(Result FileDesc Errno)
  openf ($ty:(U32) arg)
  {
      /* ... */
  }

The compiler will transform this into something like::

  t1 openf(u32 arg) { /* ... */ }

where the type definition ``t1`` was previously generated.
Beware that the |cogent| compiler
may not always emit the type's definition,
even if it emits a reference to it.


``$exp``: Embedding Expressions
------------------------------------

``$exp:(EXPRESSION)`` inserts code to execute ``EXPRESSION``.
The most common case for this is to call |cogent| functions,
or to access top-level bindings.

For example,
if we have a |cogent| function::

  within_bounds: U32 -> Bool
  within_bounds x = {- ... -}

Then, if we wish to invoke it from in C,
we might say::

  if ($exp:(within_bounds)(value)) { /* ... */ }


``$spec``: Specifying Casts
------------------------------------

``$spec:(TYPE-NAME)`` will,
if ``TYPE-NAME`` is the type of a function,
insert an appropriate C typecast.
Its most common use is
when type-casting function pointers,
as is necessary when invoking
a function reference passed from |cogent| to C.

As an example,
let's consider a function whose type is


  type ArrayModifyF a acc = OptElemA a acc -> OptElemA a acc



``$esc`` and ``$escstm``: No Escape In Sight
--------------------------------------------

``$esc:(PREPROCESSOR-DIRECTIVE)`` and
``$escstm:(PREPROCESSOR-DIRECTIVE)``
allow the insertion of a literal C preprocessor directive.

The most common uses of ``$esc``
are to introduce ``#define``s,
and to work around header files
which use any features
the underlying C parser cannot deal with ---
GNU libc's headers, for example,
are a common case::

  $esc:(#include <stdio.h>)
  $esc:(#include <stdlib.h>)


``$escstm`` occurs in a statement context;
this is useful, for example,
in combination with
the C preprocessor's conditional construct
to choose between two different implementations
depending on some other influence::

  $escstm:(#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0))
      page_cache_release(page);
  $escstm:(#else)
      put_page(page);
  $escstm:(#endif)
