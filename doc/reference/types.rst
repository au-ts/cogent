************************************************************************
                                 Types
************************************************************************

The |cogent| language is a strongly typed language, where every term and variable in a program has a 
specific type. Like some other strongly typed languages, such as Scala and several functional languages
types are often automatically inferred and need not be specified explicitly.  Although possible
in many cases, |cogent| never infers types for toplevel definitions (see Section~\ref{toplevel-def}), they
must always be specified explicitly.

In most typed programming languages a type only determines a set of values and the operations which 
can be applied to these values. As a main feature of |cogent|, types are extended to also represent 
the way how values can be used in a program.


Type Basics
====================================

We will first look at the basic features of the |cogent| type system, which are similar to those of types
in most other programming languages. There are some predefined *primitive* types and there
are ways to construct *composite* types from existing types.

Note that in |cogent| types can always be specified (e.g.~for variables or function arguments) by 
arbitrarily complex *type expressions*. It is possible to use a *type definition* 
to give a type a name, but it is not necessary to do so. In particular, types are matched by structural 
equality, hence if the same type expression is specified in different places it means the same type.

The general syntactical levels of type expressions are as follows:

  *MonoType*:
    | *TypeA1*
    | ...

  *TypeA1*:
    | *TypeA2*
    | ...

  *TypeA2*:
    | *AtomType*
    | ...

  *AtomType*:
    | ``(`` *MonoType* ``)``
    | ...

By putting an arbitrary *MonoType* expression in parentheses it can be used wherever an *AtomType* is 
allowed in a type expression.


Primitive Types
------------------------------

Since |cogent| is intended as a system programming language, the predefined primitive types are mainly bitstring types.
Additionally, there is a type for boolean values and an auxiliary string type.

Syntactically, a primitive type is specified as a nullary type constructor:

  *AtomType*:
    | ``(`` *MonoType* ``)``
    | *TypeConstructor*
    | ...

  *TypeConstructor*:
    | *CapitalizedID*


Bitstring Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The bitstring types are named ``U8``, ``U16``, ``U32``, and ``U64``.
They denote strings of 8, 16, 32, or 64 bits, respectively.

.. ::
   % , and ``Char``.
   % , the type ``Char`` is a synonym for ``U8``.

The usual bitstring operations can be applied to values of the bitstring types, such as bitwise boolean 
operations and shifting. Alternatively, bitstring values can be interpreted as unsigned binary represented
numbers and the corresponding numerical operations can be applied. All numerical operations are done modulo the
first value that is no more included in the corresponding type. E.g., numerical operations for values of
type ``U8`` are done modulo :math:`2^8 = 256`.

.. todo:: application of ``&&`` and ``||``?


Other Primitive Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The other primitive types are ``Bool`` and ``String``. Type ``Bool`` has the two values ``True``
and ``False`` with the boolean operations. Type ``String`` can only be used for specifying string literals,
it supports no operations.


Composite Types
------------------------------

There are the following possibilities to construct composite types: records, tuples, variants, and functions. 


Tuple Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A tuple type represents mathematical tuples, i.e., values with a fixed number of fields specified in a certain order. Every field may have a different type.
A tuple type expression has the syntax:

  *AtomType*:
    | ``(`` *MonoType* ``)``
    | *TypeConstructor*
    | *TupleType*
    | ...

  *TupleType*
    | ``()``
    | ``(`` *MonoType* ``,`` *MonoType* { ``,`` *MonoType* } ``)``

The empty tuple type ``()`` is also called the *unit* type. It has the empty tuple as its only value.

Note that there is no 1-tuple type, a tuple type must either be the unit type or have at least two fields. Conceptually,
a 1-tuple is equivalent to its single field. Syntactically the form ``(`` *MonoType* ``)`` is used for
grouping. 

The type expression ``(U8, U16, U16)`` is an example for a tuple type with three fields.

.. ::
   Tuple types in |cogent| are right associative: If the rightmost field in a tuple type T again has a tuple type, the type T is equivalent 
   to the flattened type where the rightmost field is replaced by the fields according to its type. As an example, all the following types are equivalent::

     (U8, (U16, U16), (U8, Bool, U32))
     (U8, (U16, U16), U8, (Bool, U32))
     (U8, (U16, U16), U8, Bool, U32)
     (U8, (U16, U16), (U8, (Bool, U32)))
     (U8, ((U16, U16), U8, Bool, U32))

Record Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A record type is similar to a C struct, or a Haskell data type in record syntax. It consist of
arbitrary many *fields*, where each field has a name and a type. Accordingly, a record type expression
has the following syntax:

  *AtomType*:
    | ``(`` *MonoType* ``)``
    | *TypeConstructor*
    | *TupleType*
    | *RecordType*
    | ...

  *RecordType*:
    | ``{`` *FieldName* ``:`` *MonoType* { ``,`` *FieldName* ``:`` *MonoType* }  ``}``

  *FieldName*:
    | *LowercaseID*

The fields in a record type are order-sensitive. Therefore, the type expressions ``{a: U8, b: U16}`` and
``{b: U16, a: U8}`` denote different types.  A record type must always have at least one field. 
Other than for tuples, a record type may have a single field.
Therefore, the type expressions ``{a: U8}`` and ``U8`` denote different types.


Variant Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A variant type is similar to a union in C, or an algebraic data type in Haskell. As in Haskell, and
unlike in C, a variant type is a *discriminated* union:  each value is tagged with 
the alternative it belongs to. 

Depending on the tag, every value may have a "payload" which is a sequence of values, as in a tuple.
A variant type specifies for every alternative the tag and the types of the payload values,  hence it has the syntax:

  *AtomType*:
    | ``(`` *MonoType* ``)``
    | *TypeConstructor*
    | *TupleType*
    | *RecordType*
    | *VariantType*
    | ...

  *VariantType*:
    | ``<`` *DataConstructor* { *TypeA2* } { ``|`` *DataConstructor* { *TypeA2* } } ``>``

  *DataConstructor*:
    | *CapitalizedID*

The tags are given by the *DataConstructor* elements.  Since the payload is a sequence of values the 
ordering of the *TypeA2* matters. 

The type expression ``<Small U8 | Large U32>`` is an example for a variant type with two alternatives, where the 
payloads are single values of type \code{U8} and \code{U32}, respectively. Typical applications
of variant types are for modelling error cases, such as in::

  <Ok U16 U32 U8 | Error U8>

or for modelling optional values, such as in::

  <Some U16 | None>

Although *DataConstructor*\ s and *TypeConstructor*\ s have the same syntax, they constitute different namespaces.
A *CapitalizedID* can be used to denote a *DataConstructor* and a *TypeConstructor* in the same
context. In the example::

  <Int U32 | Bool U8>

the name of the predefined primitive type ``Bool`` is also used as a tag in a variant type.


Function Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A function type corresponds to the usual concept of function types in functional programming languages, as it is even 
available in C. A function type has the syntax:

  *MonoType*:
    | *TypeA1*
    | *FunctionType*

  *FunctionType*:
    | *TypeA1* ``->`` *TypeA1*

A function with type ``U8 -> U16`` maps values of type ``U8`` to values of type ``U16``.

Note, that a *TypeA1*  cannot be a function type. Hence, to specify a higher order function type in |cogent|, which 
takes a function as argument or returns a functions as result, the argument or result type must be put in parentheses.

In particular, the type expression ``U8 -> U8 -> U16``, which is the usual way of specifying the type of a binary function in Haskell through
currying, is illegal in |cogent|. Strictly speaking, function types always describe unary functions. To specify the corresponding type 
in |cogent| use ``U8 -> (U8 -> U16)``. Alternatively, a type expression for a binary function can
be specified as ``(U8,U8) -> U16`` in |cogent|, which is a different type.


Type Definitions
------------------------------
.. label: def-type

Although all types in |cogent| could be denoted by type expressions, types can be named by specifying a 
*type definition*. In the simplest case, a type definition introduces a name for a type expression,
such as in the following example::

  type Fract = { num: U32, denom: U32 }

Syntactically a type name is a *TypeConstructor* in the same way as the primitive types. Hence, the 
primitive types can be considered to be specific "predefined" type names.

A type name defined in a type definition may be used in type expressions after the definition but also in type
expressions occurring *before* the type definition. In this way type definitions are "global", the 
defined type names can be used everywhere in the |cogent| program,  also in and from included files.

An important restriction of |cogent| is that type definitions may not be recursive, i.e., the type name may
not occur in the type expression on the right-hand side. Thus the following type definition is illegal::

  type Numbers = <Single U32 | Sequ (U32, Numbers)>

because the defined type name ``Numbers`` occurs in the type expression. Also there may not be an indirect
recursion, where type definitions refer to each other cyclically.

.. todo:: (jashankj) mention Emmet's work


Generic Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In a type definition it is also possible to define a *TypeConstructor* which takes one or more
*type parameters*. Such a *TypeConstructor* is called a *generic* type. 
An example would be::

  type Pair a = (a,a)

Here, the *TypeConstructor* ``Pair`` is generic, it has the single type parameter ``a``.

In fact, a generic type like ``Pair`` is not really a type, it is a type *constructor*. Only when it
is applied to type *arguments*, such as in ``Pair U32``, it yields a type. Such a type is called
a *parameterized type*. Every generic type has a fixed *arity*, which is its number of type
parameters and specifies the number of arguments required in parameterized types constructed from it.

A *TypeConstructor* is non-generic, if it has arity 0. In this special case, the *TypeConstructor*
itself already denotes a type.

Generic types in |cogent| are known in Haskell as "polymorphic types" and similar concepts can be found in 
several other programming languages. In Java, a generic class definition has the form ``class Pair<A> { ... }``, 
it defines the generic class ``Pair`` with its type parameter ``A``. In C++ a similar concept is
supported by "templates".

The syntax for a type definition in |cogent| supports both generic and non-generic types:

  *TypeDefinition*
    | ``type`` *TypeConstructor* { *TypeVariable* } ``=`` *MonoType*
    | ...

  *TypeVariable*:
    | *LowercaseId*

A *TypeConstructor* defined this way is also called a *type synonym*, since as a type expression
it is strictly equivalent to the expression on the right-hand side in the definition. A type synonym with
arity 0 is called a *type name*.

In the definition of a generic type, the type parameters may occur in the *MonoType* on the right-hand side.
There they are called *type variables* and a type expression containing type variables is 
called a *polymorphic type*. To support polymorphic type expressions, the syntax allows type variables as
*AtomType*:

  *AtomType*:
    | ``(`` *MonoType* ``)``
    | *TypeConstructor*
    | *TupleType*
    | *RecordType*
    | *VariantType*
    | *TypeVariable*

As in Haskell there is no syntactic difference between type variables and normal (term) variables. 
However, type variables are syntactically different from type constructors, since the latter are capitalised identifiers,
whereas variables begin with a lowercase letter.

Since type variables are allowed as *AtomType*, they can occur in a polymorphic type expression in all places
where a type is allowed. 

Note that in the definition of a generic type, all type variables occurring in the type expression on the right-hand
side must be type parameters, declared on the left-hand side, i.e., they must all be bound in the type definition. 
The other way round, a type parameter need not occur as type variable in the type expression. In Haskell, this
is called a "phantom type". Other than in Haskell in Cogent these types are not checked by the type checker, hence for::

  type A a = U8

the types ``A U16`` and ``A Bool`` are equivalent.


Parameterized types are simply denoted by the generic type constructor followed by the required number of
type expressions as arguments, such as in::

  Pair U32

They can be used in type expressions as *TypeA1*:

  *TypeA1*:
    | *TypeA2*
    | *ParameterizedType*
    | ...

  *ParameterizedType*:
    | *TypeConstructor* { *TypeA2* }

Note that parameterized types must be put in parentheses if they are nested (used as argument of another parameterized type). 


Expanding Type Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We call a parameterized type with a type synonym as *TypeConstructor* a *parameterized type synonym*.

Since type definitions may not be recursive, type synonyms can always be eliminated from type expressions 
by substituting the defining type expression for them, putting it in parentheses if necessary. 

In the case of a parameterized type synonym also the type variables are 
substituted by the actual type arguments. We call the result of eliminating (transitively) all type synonyms
from a type expression the *expansion* of the type expression.


Abstract Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

An *abstract* type is similar to a type synonym without a definition. The idea of abstract types in |cogent| is
to provide the actual definition externally in accompanying C code. Hence abstract types are the |cogent| way of
interfacing C type definitions. However, since abstract types are used in |cogent| in an opaque way, it is not necessary
to know the external C definition for working with an abstract type in |cogent|.  Note that abstract types are not
meant to be used as interfaces to or abstractions of other |cogent| types.

Abstract types can be generic, i.e., they may have type parameters. The names of these type parameters are irrelevant,
since there is no definition where they could occur as type variables. They are only used to specify the arity of
the generic abstract type.

The syntax for defining abstract types is the same as for normal type definitions, with the defining type expression 
omitted:

  *TypeDefinition*:
    | ``type`` *TypeConstructor* { *TypeVariable* } ``=`` *MonoType*
    | *AbstractTypeDefinition*

  *AbstractTypeDefinition*:
    | ``type`` *TypeConstructor* { *TypeVariable* }

The following examples define two abstract types. Type ``Buffer`` is non-generic, type ``Array`` is generic
with arity 1::

  type Buffer
  type Array a

Like generic type synonyms, generic abstract types can be used to construct parameterized types::

  Array U16

We call a parameterized type with an abstract type as its *TypeConstructor* a *parameterized abstract type*.
Note that abstract types cannot be eliminated by expanding a type expression, since they have no definition.


Restricted Types
====================================

A type semantically determines a set of values as its extension. In most other typed programming languages the main
consequence is that the type of a value restricts the functions which can be applied to it. 

A specific feature of |cogent| is that the type may impose additional restrictions on the ways a value can be used 
in the program, in particular, how *often* it may be used. This concept is known as *linear types*,
it is also present in some other special programming languages, e.g., in Rust.

Many types in |cogent| do not impose additional restrictions, they behave like types in other programming languages,
we call them *regular types*. Types with additional restrictions are called *restricted types*.


Linear Types
------------------------------

One kind of restricted types are *linear types*. A linear type has the specific property, that its values must 
be used *exactly once* in the program. What this means is explained in Section~\ref{expr-usage}. Here it is 
only relevant that a type may be linear or not.

Linearity is an inherent property of type expressions. Type expressions as they have been described until now can either
be linear or regular. To determine whether a type expression is linear or regular 
its expansion is inspected using the following rules:

- Primitive types are regular.
- Record types are linear.
- Tuple types are linear if they contain at least one field with a linear type.
- Variant types are linear if they contain at least one alternative with a payload of linear type.
- Function types are regular.
- Parameterised and non-generic abstract types are linear.

Together, a type is linear when, after expanding all type synonyms, it has a component of a record or abstract type
which does not appear as part of a function type.


Boxed and Unboxed Types
------------------------------

In order to decouple the property of linearity somewhat from the way how types are composed, the concept of 
*unboxed types* is used. Record types and abstract types, which may cause a type to be linear, are
called *boxed types*, the other types (primitive, tuple, variant, and function) are called *unboxed types*.

The type system is expanded by introducing the unbox type operator ``#``. For boxed types it produces
an unboxed version. By applying the unbox type operator to all record types and abstract types
in a type expression, the type expression becomes regular. 

The operator ``#`` is applied to a type expression as a prefix. To simplify the syntax it is allowed to
be applied to arbitrary *AtomType* expressions:

  *TypeA2*:
    | *AtomType*
    | ``#`` *AtomType*
    | ...

By putting an arbitrary *MonoType* in parentheses, the unbox operator can be applied to it, as in ``#(Array U8)``.

If the unbox operator is applied to an *AtomType* which is already unboxed, it has no effect. Hence, the type
expressions ``(U8,U16)`` and ``#(U8,U16)`` denote the same type, whereas ``{fld1:U8,fld2:U16}`` and
``#{fld1:U8,fld2:U16}`` denote different types. 

When applied to a record, the unbox operator affects only the record itself, not its fields. Hence, an unboxed
record is still linear, if it has linear fields. The additional linearity rules for types resulting from 
applying the unbox operator are

- Unboxed record types are linear if they contain at least one field with a linear type.
- Unboxed non-generic or parameterised abstract types are regular.
- For all other cases, an unboxed type is linear or regular according to the linearity of the type expression to which
  the unbox operator is applied.

As an example, if ``A`` is a non-generic abstract type, the type expression ``#(U8,A)`` is linear, since
the linear second field makes the type expression ``(U8,A)`` linear.


Partial Record Types
------------------------------

Since record types are linear, their values must be used exactly once, which also uses all their linear fields. 
To support more flexibility, |cogent| allows
using linear record fields independently from the record itself, although each of them must still be used exactly once.
This is done by separating the linear field's value from the rest of the record. The fact that the field value is no more present
in the remaining record is reflected by the remaining record having a different type. These types are called 
*partial record types*. A record field for which the value is not present is called a *taken* field.

A partial record type is denoted by specifying a record type together with the names of the taken fields using the 
following syntax:

  *TypeA1*:
    | *TypeA2*
    | *ParameterizedType*
    | *PartialRecordType*

  *PartialRecordType*
    | *TypeA2* *TakePut* *TakePutFields*

  *TakePut*:
    | ``take``
    | ``put``

  *TakePutFields*:
    | *FieldName*
    | ``(`` [ *FieldName* { ``,`` FieldName } ] ``)``
    | ``( .. )``

Thus ``take`` and ``put`` together with field names constitute type operators. The result of applying these
type operators is usually a partial record type.

When applied to a type R the operator ``take (v,w)`` produces the record type where at least fields
``v`` and ``w`` are taken, in addition to the fields that have already been taken in R.
If the fields ``v`` and ``w`` are already taken in R, the compiler produces a warning. If R has no such fields
then applying the take operator is illegal. 

The operator ``put (v,w)`` is dual to the take operator, it produces the record type where at least the fields 
``v`` and ``w`` are *not* taken, in addition to the fields that have not been taken in R.
If the fields ``v`` and ``w`` are not taken in R, the compiler produces a warning. If R has no such fields
then applying the put operator is illegal.

The operator ``take ( .. )`` produces a record type where all fields are taken, the operator ``put ( .. )`` 
produces the record type where no field is taken. Applying it to a type which is not a (boxed or unboxed) record type
is illegal.

If a take or put operator is applied to a boxed record type the result is again boxed, if applied to an unboxed record type
the result is unboxed.

Consider the following examples::

  type A
  type B
  type C
  type R1 = {fld1: A, fld2: U8, fld3: B, fld4: C}
  type R2 = R1 take fld1
  type R3 = R1 take ( .. )

Types ``R1, R2, R3`` are all boxed and thus linear. The type expressions::

  R1 take (fld1, fld2)
  R2 take (fld1, fld2)
  R2 take fld2
  R3 put (fld3, fld4)

are all equivalent. The type expressions ``R3 put ( .. )`` and ``R2 put ( .. )`` are both equivalent to
type ``R1``.

An unboxed record type without linear fields is regular. The same holds for unboxed partial record types if all
linear fields are taken. Thus the additional linearity rules for partial record types are

- Partial boxed record types are linear.
- Partial unboxed record types are linear if they contain at least one nontaken field with a linear type.


Readonly Types
------------------------------

Since the restrictions for using values of a linear type are rather strong, |cogent| supports an additional kind
of types, the *readonly types*. The use of values of a readonly type is also restricted, however, in a
different way: they can be used any number of times but they may not be modified. Again,
the meaning of this is explained in Section~\ref{expr-usage}.


The bang Operator
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

All type expressions defined until now are not readonly. The only way to construct a readonly type is by applying
the type operator ``!``, which is pronounced "bang". This operator may be applied to an *AtomType* 
in postfix notation:

  *TypeA2*:
    | *AtomType*
    | ``#`` *AtomType*
    | *AtomType* ``!``

By putting an arbitrary *MonoType* in parentheses the bang operator can be applied to it.

Readonly types are considered as an alternative to linear types, hence regular types are never readonly: If the 
bang operator is applied to a regular type A the resulting type is equivalent to A. Only if the bang operator
is applied to a linear type a readonly type may result.

Unlike the unbox operator the bang operator also affects subexpressions such as record fields and abstract types. If in
type A a field has type F then in type A! the same field has type F!. An exception are function types: if a bang
operator is applied to a function type it is not applied to argument and result types. 
As a result of this recursive application of the bang operator, it turns every linear type into a non-linear type. 


Escape-restricted Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A concept related to readonly types are *escape-restricted types*. A type is escape-restricted if it is readonly
or if it has an escape-restricted component. This definition implies, that readonly types are always escape-restricted. The opposite
is not true, there are escape-restricted types which are not readonly. An example is the type::

  #{fld1: U8, fld2: {f1: U16}! }

It is not readonly since the bang operator is not applied to it. However, it has the field ``fld2``
with a readonly type, therefore it is escape-restricted.

We call a type which is not escape-restricted an "escapable" type.

A linear type always is a boxed record or abstract type or it contains a component of such a type. When the bang
operator is applied to the linear type, it will recursively be applied to that component, turning it into a 
component of readonly type. Therefore, the result of applying the bang operator to a linear type will always
be an escape-restricted type which is not linear.

There are even types which are linear and escape-restricted, such as the boxed record type::

  {fld1: U8, fld2: {f1: U16}! }

or the unboxed record with a field of linear type and a field of readonly type::

  #{fld1: {f1: U16}, fld2: {f1: U16}! }

If all escape-restricted fields are taken from a record, the resulting partial record type is escapable.
An example is the type::

  {fld1: U8, fld2: {f1: U16}! } take (fld2)


As the other restricted types, escape-restricted types impose additional restrictions on the use of their values: they 
may not "escape" from certain context. Again, the meaning of this is explained in Section~\ref{expr-usage}.

Together we have the following properties for type expressions: A type expression can be regular or restricted. If it is restricted 
it can be linear, escape-restricted, or both. A readonly type is always escape-restricted but never linear.

