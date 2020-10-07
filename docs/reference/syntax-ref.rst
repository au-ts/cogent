************************************************************************
			     Surface Syntax
************************************************************************

.. note:: For new users of this language, this section is not intended to be a
          tutorial for the language. It merely introduces its surface syntax and
          should be used as a reference while using the language.

.. note:: As described in `#324 <https://github.com/NICTA/cogent/issues/324>`_,
          we are in the progress of revising the surface sytnax. So it's subject
          to change in near future.


Types
=====

All type names must begin with an uppercase letter. Tuple, Function,
Record and Variant types have special syntax.

Record types
------------

Now indicated by a series of typing declarations inside braces, e.g

::

    {x : A, y : B}

If a field ``f`` is removed by ``take``, the postfix type operator
``take f`` may be used:

::

    {x : A, y : B} take x

This works, even if the type on the LHS is a type synonym (c.f. :ref:`typedefs`).

Sugar: Taking multiple fields:

::

    {x : A, y : B} take (x,y) -- parens mandatory

::

    {x : A, y : B} take (..)  -- parens mandatory

This ``(..)`` sugar means to take all currently untaken fields (if any).

Similarly, we can write ``put`` instead of ``take`` with the same
syntax. ``put`` is dual to ``take``. One common usage would be

::

    ({x : A, y : B, z : C, u : D, w : E} take (..)) put x

Note that the parentheses around the record and first ``take`` is mandatory.
Arbitrary many levels of nestings is possible.

Unboxed records
---------------

Unboxed records are pretty much like regular records, except that their
wrappers (i.e. the unboxed container) are lightweight that no allocation
is required.

The syntax is simple, just a prefixing ``#`` on its counterpart record
type. ``take``, ``put`` operations (and punning) and member extraction
are of exactly the same syntax as regular records. As a consequence of
its lightweightness, we can construct and deconstruct (by means of
pattern matching) unboxed records, just as what we do on tuples (see
:ref:`product-types` for tuples).

E.g.,

::

    #{x : A, y : B}    -- type
    #{x = e1, y = e2}  -- expression or pattern
    a.x                -- member
    a {x = f}          -- take and put, same as regular records

About its *permission* rules (see :ref:`permissions`):
the wrapper per se is non-linear (i.e. shareable
and discardable). If
any linear fields are present (untaken), then the unboxed record becomes
linear. Member operation can only be used if there're no linear
fields inside, or the unboxed record is banged (``!``).

Unboxed abstract types
----------------------

The ``#`` sigil is not used in the declaration of an unboxed abstract
type. Instead, we attach the ``#`` sigil when the type is used. E.g.:

::

    type A
    type T = {a : #A, b : A}

In the above case, field ``a`` is unboxed, whereas ``b`` is not. When
generating C code, boxed abstract types will be pointers, unboxed are
not. It's the users' responsibility to keep the C code consistent, as
these types are abstract.

Bang (``!``)
------------

Record types and abstract types have *sigils*, but outwardly, a *Write*
sigil is just a plain record type / abstract type, and an *Observe* (or *Readonly*) sigil
would be indicated with a postfix bang, for example: ``{x : A, y : B}!``, ``C!``.

The postfix bang operator can be applied to any type, which converts all
write sigils to readonly sigils internally (and any type variables to
readonly type variables).

To bang a parametric type, the type must be surrounded by parentheses,
otherwise ``!`` will be applied to the type parameter right before the
``!`` symbol.

.. _product-types:

Product Types
-------------

Nameless, unboxed tuples may be used everywhere you like. Their syntax
is identical to Haskell. A unit type (which is freely discardable and
not linear) also exists, ``()`` with a value ``()``. Tuples are not
associative, namely ``(a, b, c, d) /= (a, (b, (c, d)))`` and
``(a, b, c, d) /= (((a, b), c), d)``, just as in Haskell.

Variant Types
-------------

Variant types look like this.

::

    < Ok (Obj, Heap) | Fail Heap >

They can be constructed using ``Ok (obj,h)``, or ``Fail e``.

We can determine from context if ``Identifier`` (``Ok`` and ``Fail`` in
the example above) is a type or a data constructor, much like Haskell.
We will have to do a little bit of inference to determine which variant
type the thing actually belongs to.

They can have as many alternatives as you like, and there is no
restriction on what goes inside a variant type. Each alternative can
take any number of arguments (0 or more). They will be desugared to
tuples of all the arguments. E.g.:

::

    <Ok Obj U8 | Fail >  -- equiv to <Ok (Obj, U8) | Fail ()>

Polymorphic types
-----------------

Types can contain variables. Functions may be declared as having
polymorphic type.

::

    size : all (k, v). Map k v -> U32

Monomorphic functions are first class, but to get a monomorphic function
from a polymorphic function requires instantiation, e.g ``length[Int]``.
Since Cogent-2.0.9, explicit type applications are not mandatory,
although in some cases they must be supplied to guide the type inference
engine. Type applications can be partial, or with type holes. For
example, ``foo [_, A, B]``; ``foo [S, T, _]`` is equivalent to ``foo [S,T]``.

A type variable under observation (i.e ``let!``-ed) is annotated with a
prefix bang (e.g ``!a``)

.. _permissions:

Permissions
~~~~~~~~~~~

*Permissions* (they used to be called "kinds") are provided for
polymorphic signatures as follows:

::

    length : all (a :< k). Array a -> U32

Permissions are internally a set of three booleans: whether or not the
type can be:

-  ``D`` for Discard (i.e by weakening)
-  ``S`` for Share   (i.e by contraction)
-  ``E`` for Escape  (i.e returned from ``let!``)

The permission signature on a type variable is more like a constraint.
They are some combination of those three letters. If no permission
is provided, it is assumed that none of those permissions are required,
and the value will be linear and cannot escape a ``let!``.

.. _typedefs:

Type synonyms
=============

Type synonyms may be provided using the ``type`` keyword as follows:

::

    type X a b = { foo : a, bar : b, baz : Int }

The type synonym ``X`` must always be fully saturated with its two
arguments wherever it is used, however.

Abstract types (defined in C) may also be declared, and they also may
take parameters. This corresponds to a family of types in C.

::

    type Buffer
    type Array a

Constants and top-level definitions
===================================

Constants are mono-typed.

::

    abc : U8
    abc = 3

But the right hand side can be much more expressive now, with let
bindings and whatnot. We must be able to prevent users from doing
side-effects like allocation in the top-level---see :ref:`effects`.

To make the syntax easier to parse, a function or constant's body must
be indented by at least one space. This means that any non-indented
bareword is the start of a new definition or signature.

.. _effects:

Effects
=======

Most effects are currently (successfully) modelled via linear types. For
allocation, |cogent| does not know anything about it. Memory management
involves the heap. I propose modelling the heap as an explicit linear
value, just as with any other state.

Allocation functions must take and return a linear heap, as they
modify it:

::

    allocateObj : Heap -> < Ok Obj Heap | Fail Heap >

Special syntax for allocation functions and automating heap-threading
are nice to have, so I welcome proposals.


Expression language
===================

Matching and Error Handling
---------------------------

Matching may be accomplished by the following syntax:

::

    f : Heap -> < Ok Obj Heap | Fail Heap >
    f h = allocateobj h 
        | Ok obj h => allocateobj h
            | Ok obj' h => Ok (mergeObj (obj, obj')) h
            | Fail h -> let () = free obj in Fail h 
        | Fail h -> Fail h

This is an alignment-based syntax, grouping determined based on the
alignment of the bars.

The rightward arrows for each case can either be ``=>`` or ``->``.
``=>`` indicates that that branch is likely, to enable compiler
optimisations. ``~>`` can also be used to indicate an unlikely branch.

A pattern may be ``_`` but only if the kind of the value allows it to be
discarded.

Biased pattern matching
-----------------------

The syntax above poses a problem if many levels of nestings occur---you
will end up with cascading matches which indent a lot. To solve this
problem, we allow a syntax for early exit, which is inspired by `Idris <https://www.idris-lang.org/>`_.
The syntax looks like:

::

    f : Heap -> <Ok Obj Heap | Fail Heap>
    f h = let Ok obj  h <= allocateobj h |> Fail h -> Fail h
          and Ok obj' h <= allocateobj h |> Fail h -> let _ = free obj in Fail h
           in Ok (mergeObj (obj, obj')) h

This piece of code is semantically identical to the one above. ``<=``
matches the major case, and ``|>`` bails out with the minor case.

Patterns
--------

Patterns may be refutable (could fail, e.g ``Ok a`` or ``43``) or
irrefutable (always match, e.g ``(a,b)`` or ``_``). Refutable patterns
can be used in a matching block only, but they can only nest irrefutable
patterns. So, unlike in Haskell, you can't go:

::

    f x = foo x
      | Ok (Alt1 3) -> bar 
      | _ -> baz                   

As this nests a refutable pattern (``3``) inside another refutable
pattern (``Alt1 3``) inside another refutable pattern (``Ok (Alt1 3)``).

This is forbidden to make compilation much more straightforward in the
presence of linear types.

Let-binding
-----------

Let expressions take the form of ML. They are not ever recursive.
Multiple let-bindings can be introduced by separating them with ``and``:

::

    f () = let x = 3
           and y = 4 
            in foo (x,y)

Is equivalent to:

::

    f () = let x = 3
            in let y = 4 
                in foo (x,y)

Irrefutable single patterns may occur on the left hand side of let-binding, but
refutable patterns must use regular pattern matching.

To force inference to go the way you want, a type signature can be
provided for a let binding:

::

    f () = let x : U8 = 3
            in let y : U16 = 4 
                in foo (x,y)

Observation and ``let!``
------------------------

Variables may be observed using ``!``:

::

    f (x, y) = let (a,b) = foo (x, y) !x !y
                in bar (a, b)

Prefix ``!`` annotations can be used inline with pattern matching also:

::

    f (x,y) = foo(x,y) !x !y
              | Blah x  => bar x
              | Blorp z -> baz z

If
--

Conditionals can be expressed in the form of if-expressions. They are in
the form of ``if c !v1 !v2 ... then e1 else e2``. The ``!v``\ s are
similar to the ``!`` syntax introduced above, allowing for temporary
access to linear objects in the condition.

Apart from the normal if-then-else syntax, |cogent| offers a multi-way if
syntax, inspired by GHC/Haskell. For example,

::

    if | cond_1 -> expr_1
       | cond_2 -> expr_2
       | ...
       | else   -> expr_n

In the code snippet above, the conditions are Boolean **expressions**,
instead of patterns as one might think. The final ``else`` is part of
the syntax. The pipes have to be aligned. The arrows, as usual, can be
any of ``=>``, ``->`` or ``~>``, which have the same semantics as used
in alternatives. Prefix ``!``\ s can be added after each condition (but
not after the ``else`` keyword), like ``| cond_1 !v1 !v2 => e``.

Sequencing
----------

Occasionally, it is useful to free a bunch of things, and using ``let`` for
this purpose can be somewhat annoying:

::

    f : (Obj, Obj) -> Int
    f (a, b) = let _ = free a
               and _ = free b
                in 42 

So, a little sugar is added for a series of discarding let bindings:

::

    f : (Obj, Obj) -> Int
    f (a, b) = free a; free b; 42

These two expressions are equivalent.

Take/put
--------

There is pattern syntax for ``take``, and a similar expression syntax
for ``put``:

::

    f : {a : Foo, b : Bar} -> {a : Foo, b : Bar}
    f (r {a = ra, b = rb}) = r {a = ra, b = rb}

.. note:: ``take`` is always in patterns (i.e. LHS of ``=``), whereas
          ``put`` is always in expressions (i.e. RHS of ``=``).

Punning is also allowed:

::

    f : {a : Foo, b : Bar} -> {a : Foo, b : Bar}
    f (r {a, b}) = r {a, b}

(where just ``a`` is equivalent to ``a = a``)

Arithmetic and comparison operators
-----------------------------------

Currently |cogent| will use the smallest type possible for integer
literals and generate upcasts (but not downcasts) automatically when
used in a context where they are required. For non-literals, an explicit
``upcast`` primitive may be needed.

Type annotations
----------------

To guide the type inference engine, the user can give type annotations
to any expressions. The syntax is ``e : t``.


Experimental features
=====================

.. warning:: Experimental features, as they are called, are indeed experimental,
             which means they are not stable, and may fail, terribly. Don't rely on them
             until they become stable.

.. _static-arrays:

Static arrays
-------------

.. note:: This feature is not implemented on the ``master`` branch. It's implemented
          on the ``array`` branch and needs to be enabled by the ``--builtin-arrays`` flag 
          (see :ref:`optional-features` for more information on how to do that).

Array literals can be introduced using square brackets, like
``[a, b, c]``. This syntax can also be used as patterns. Array types can
be defined like ``U8[3]``, similar to C. Indexing can be made with the
``@`` operator. E.g.: ``arr @ 3``. Arrays can also be ``take``\ n and ``put``.
The type-level ``take`` and ``put`` operators are spelt as ``@take`` and ``@put``
respectively. On the term level, it's written as ``arr @{ @idx = val }``---
just prefix the open bracket and the indices with ``@`` symbols, and the rest
are the same as those for records.


Lambda expressions
------------------

We only allow for a very limited form of lambda expressions. A lambda
expression has the syntax ``\irref => exp``, where ``irref`` is an
irrefutable pattern, and ``exp`` is an expression which does not refer
to any variables outside the lambda binding (no free variables). The
bound variables have to be non-linear.

