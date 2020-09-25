************************************************************************
                              Antiquoted C
************************************************************************

.. warning::
   Cogent antiquotation has almost no checking.
   Be very, very careful, as the result may break.

|cogent| is a substantially restricted language:
many operations cannot be expressed,
and those must instead be implemented in C.
To access functions written in C from |cogent|,
one writes abstract types and abstract functions.
To access functions written in |cogent| from C,
more capability is required.

*Antiquoted C* is the mechanism by which
we can invoke |cogent| from C.
Antiquoted C behaves
something like a template language:
an *antiquote* take the form
``$``, quotation type, ``:``, and (usually parenthesised) term;
and denotes an item in C that must
be understood, and potentially transformed,
by the |cogent| compiler.
Quotation types influence the way the term is transformed:

- ``$id:(IDENT)`` introduces ``IDENT`` as an identifier
  at the point of declaration, either of a function or a type::

    void $id:(stare_into_abyss) (void) { /* ... */ }

    struct $id:(by_lightning) { /* ... */ }

  Often, these aren't required:
  if no type parameters are involved,
  as might be the case with ``stare_into_abyss`` above,
  this could be declared without antiquotes.


- ``$ty:(TYPE-NAME)`` refers to the type ``TYPE-NAME``,
  which may be any type known to |cogent|.
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

  This will be transformed into::

    t1 openf(u32 arg) { /* ... */ }

  where the type definition ``t1`` has already been generated.
  Beware that the |cogent| compiler
  may not always emit the type's definition,
  even if it emits a reference to it.


- ``$exp:(EXPRESSION)`` inserts code to execute ``EXPRESSION``.
  The most common case for this is to call |cogent| functions,
  or to access top-level bindings.

  For example,
  if we have a |cogent| function::

    within_bounds: U32 -> Bool
    within_bounds x = {- ... -}

  Then, if we wish to invoke it from in C,
  we might say::

    if ($exp:(within_bounds)(value)) { /* ... */ }


- ``$spec:(TYPE-NAME)`` will,
  if ``TYPE-NAME`` is a function,
  insert an appropriate C type;
  this is intended for use
  when type-casting function pointers,
  as is necessary when invoking a lambda.


- ``$esc:(PREPROCESSOR-DIRECTIVE)`` and
  ``$escstm:(PREPROCESSOR-DIRECTIVE)``
  allow insertion of a literal C preprocessor directive.

  The most common uses of ``$esc``
  are to introduce ``#define``s,
  and to work around header files
  which use any features
  the underlying C parser cannot deal with ---
  GNU libc's headers, for example,
  are a common case::

    $esc:(#include <stdio.h>)
    $esc:(#include <stdlib.h>)

  ``$escstm`` is expected to be in a statement context;
  so, for example::

    $escstm:(#if LINUX_VERSION_CODE < KERNEL_VERSION(4,4,0))
        page_cache_release(page);
    $escstm:(#else)
        put_page(page);
    $escstm:(#endif)
