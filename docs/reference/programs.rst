************************************************************************
				Programs
************************************************************************

A |cogent| program is a sequence of toplevel definitions and include staatements.
There is no main program, it must always be implemented externally in C.

  *Program*:
    | *TopLevelUnit* { *TopLevelUnit* }

Including Files
====================================

For modularization purpose a |cogent| program may be distributed among several files
using include statements. Like in many other programming languages, an include statement 
is replaced by the content of the included file.

The syntax for an include statement is:

  *TopLevelUnit*:
    | *Include*
    | ...

  *Include*:
    | ``include`` *StringLiteral*
    | ``include`` *SystemFile*

  *Systemfile*: informally,
    | A file pathname enclosed in ``<`` and ``>``.

The *StringLiteral* specifies the pathname of the file to be included, either as 
an absolute path or as a path relative to the directory where the file containing the include statement
resides.  A *SystemFile*, like in C, specifies a file which is searched at standard places by the
|cogent| compiler.

Include statements are transitive, if an included file contains include statements they are executed as well.

However, every file is included only once. If several include statements specify the same file, it is
only include by the first statement seen when processing the |cogent| source file, all other inclusions
of the file are ignored. This is also true for transitive includes, in particular, circular includes do no harm.
The effect is the same that is usually achieved in C by ``#define``\ ing a flag in an include file and including 
the file body only if the flag is not yet set.

.. _toplevel-def:

Toplevel Definitions
====================================

The only syntactical constructs which may occur as toplevel units in a |cogent| source program are *definitions*.

  *TopLevelUnit*:
    | *Include*
    | *Definition*

  *Definition*:
    | *TypeDefinition*
    | ...

A definition may be a type definition, as described in :ref:`def-type`.


.. _value-def:

Value Definitions
------------------------------

A definition may also be a *value definition*. It has the following syntax:

  *Definition*:
    | *TypeDefinition*
    | *ValueDefinition*
    | ...

  *ValueDefinition*:
    | *Signature* *Variable* ``=`` *Expression*

  *Signature*:
    | *Variable* ``:`` *PolyType*

  *PolyType*:
    | *MonoType*
    | ...

A value definition is conceptually mainly a syntactical variant for a *LetExpression* which binds a single variable.
However, there are the following differences:

- the variable bound by a definition is a *global* variable which can be referenced in 
  *LambdaExpression*\ s (see :ref:`term-lambda`}),
- the scope of the variable consists of the whole |cogent| program after *and before* the definition,
- the type specification is mandatory and  in the case of a function type,  instead of a 
  *MonoType* it may be a more general *PolyType* (see :ref:`def-poly`).

A *ValueDefinition* of the form::

  V ``:`` T V ``=`` E

is conceptually equivalent with

\hspace*{1cm} ``let`` V ``:`` T = E ``in`` F\\
where F is the whole |cogent| program around the definition. This equivalence is only conceptual, syntactically 
it is not correct, since F is not an *Expression* and cannot be expressed as one.

Note that the variable V has to be specified twice. It is an error if two different variables are used in 
a value definition.

Like type definitions, value definitions in |cogent| are restricted to be not recursive: the variable V may not
occur freely in the expression E and there may be no cyclic references between different value definitions.

The *Expression* E may only contain free occurrences of global variables which have been bound in 
other value definitions. The *Expression* E and in the *PolyType* T may contain all
type synonyms which are defined in a type definition before or after the value definition.

An example for a value definition is::

  maxSize: U16
  maxSize = 42

.. todo:: layout rules for value definitions


.. _fun-def:

Function Definitions
------------------------------

A function definition is a special case of a value definition, where the value has a function type.
This could be achieved with a normal value definition using a lambda expression to specify the
value to be bound. However, for function definitions additional syntactical forms are supported in |cogent|:

  *Definition*:
    | *TypeDefinition*
    | *ValueDefinition*
    | *FunctionDefinition*
    | ...

  *FunctionDefinition*:
    | *Signature* *Variable* *IrrefutablePattern* ``=`` *Expression*
    | *Signature* *Variable* *Alternative* { *Alternative* }

A *FunctionDefinition* of the form::

  V : T
  V IP = E

is semantically equivalent with::

  V : T
  V = IP => E

In a function definition the type *T* must of course be a function type.

An example for this kind of function definition is::

  f: (U32, U32) -> #{sum: U32, dif: U32}
  f v = let (x,y) = v in #{sum=x+y, dif=x-y}

where the variable ``v`` is used to reference the function argument. Note that by using a pattern
instead of a single variable, it is possible to directly access the argument components according to the
argument type::

  f: (U32, U32) -> #{sum: U32, dif: U32}
  f (x,y) = #{sum=x+y, dif=x-y}

The second form of a function definition is intended for the case that the argument is not matched against
a single irrefutable pattern but instead against several exhaustive refutable patterns.
Then the *FunctionDefinition* of the form::

  V : T
  V A1 ... An

is semantically equivalent with::

  V : T
  V arg = arg A1 ... An

where ``arg`` is a new variable not occurring elsewhere.

Examples are the function definitions::

  f: <TwoDim U32 U32 | ThreeDim U32 U32 U32 | Error U8> -> (U32, U32)
  f | TwoDim x y -> (y,x) 
    | ThreeDim x y z -> (y,z) 
    | Error _ -> (0,0)

  g: U8 -> U8
  g | 0 -> 'a' 
    | 1 -> 'b' 
    | 2 -> 'c' 
    | _ -> 'd'


\todo{layout rules}


Abstract Definitions
------------------------------

An *abstract* definition only specifies the type of a value bound to a variable but not the value itself.
Abstract definitions are only allowed if the bound value has a function type. 
The syntax is a normal value definition reduced to its signature:

  *Definition*:
    | *TypeDefinition*
    | *ValueDefinition*
    | *FunctionDefinition*
    | *AbstractDefinition*

  *AbstractDefinition*
    | *Signature*

The purpose of abstract definitions is to define functions which are implemented externally as C functions.

A collection of abstract definitions together with corresponding type definitions is often called an "abstract data type" 
("ADT"). Typically an abstract data type consists of one or more abstract type definitions and abstract definitions for
functions working with values of these types, where both types and functions are externally defined in C.


.. _def-poly:

Polymorphic Definitions
------------------------------

Function  values bound by toplevel definitions may be *polymorphic* which means that their
type is not specified uniquely.
This is achieved by allowing free type variables in the value's type as specified in the definition. A type expression which 
may contain free type variables is called a *PolyType* in |cogent|. Syntactically *PolyType*\ s must be closed
by binding the free type variables by an "all-quantification". The syntax is as follows:

  *PolyType*:
    | *MonoType*
    | ``all`` *PermSignatures* ``.`` *MonoType*

  *PermSignatures*:
    | *PermSignature*
    | ``(`` *PermSignature* { ``,`` *PermSignature* } ``)``

  *PermSignature*:
    | *TypeVariable*
    | ...

Here all type variables which occur free in the *MonoType* must be listed in the *PermSignatures*.
An example for a polymorphic value definition is::

  f: all (t, u). (t, u) -> (U32, u, U16, t)
  f (x,y) = (200, y, 100, x)

Since the types  ``t`` and ``u``  are unknown, no expressions can be specified for their values other than 
variables to which the values have been bound. As a consequence, polymorphic values are  always  polymorphic functions
which take the values of the unknown types as (part of) their argument and only pass them around, perhaps placing them
in the function result.

A typical example for a  polymorphic function  works with lists of arbitrary elements.
Therefore no specific type shall be specified for the list elements, which is achieved by using a free type variable
for it. The corresponding list type can be defined as a generic abstract type::

  type List e

Then the usual functions working on lists can be defined by the following abstract polymorphic function definitions::

  first: all e. List e -> Option e
  rest: all e. List e -> List e
  cons: all e. (e, List e) -> List e

Together these definitions constitute an abstract data type for lists. Note, that neither the list type nor the list 
functions can be defined in |cogent| since they would require recursion. 

Even when a value of an unknown type is only carried around, additional information about the type is needed for doing
this correctly: If the type is linear, the value may still be used only once, whereas the value may be freely copied, if
the type is non-linear. Therefore it is possible to specify  "permissions" for a type variable in the
*PermSignatures*  using the following syntax:

  *PermSignature*:
    | *TypeVariable*
    | *TypeVariable* ``:<`` Permissions

  *Permissions*:
    | *Permission* { *Permission* }

  *Permission*: one of
    | ``D``
    | ``S``
    | ``E``

The permissions associated with a type variable specify what must be possible for values of that type. Permission ``D`` means
the values can be *discarded*, permission ``S`` means the values can be *shared*, and permission ``E``
means that values may *escape* from a banged context. If a type variable has kind ``DSE`` the actual type must be regular.
If a type variable has kind ``DS`` the actual type must not be linear, it may be regular or escape-restricted. If it has kind 
``E`` the actual type must not be escape-restricted, it may be regular or linear.

If no  *Permissions* are specified for a type variable the default permissions ``E`` apply.

In the example::

  f: all (t, u :< DSE) . (t, u) -> (U32, u, U16, t, u)
  f (x,y) = (200, y, 100, x, y)

the type ``t`` has default  permissions  ``E`` and is thus required to be escapable. 
Type ``u`` is required to be regular and it is correct to use parameter ``y`` more than once in the body expression.

Whenever a global variable bound by a polymorphic value definition is referenced, actual types must be substituted for 
the free type variables. These types  can  be explicitly specified using the following syntax:

  *Term*:
    | ``(`` Expression ``)``
    | *Variable*
    | *LiteralTerm*
    | *TupleTerm*
    | *RecordTerm*
    | *VariantTerm*
    | *LambdaTerm*
    | *PolyVariable*

  *PolyVariable*:
    | *Variable* ``[`` *OptMonoType* { ``,`` *OptMonoType* } ``]``

  *OptMonoType*:
    | *MonoType*
    | ``_``

If the types are not specified or if some types are specified by ``_``, the compiler tries to infer them.
If the compiler is unable to infer the types, then they must be explicitly specified. For example,
if the compiler has difficulty with the last type argument, instead of
``f [U8, Char, <A U8|B U16>]``, we can write ``f [_, _, <A U8 | B U16>]``.


If ``f`` has been bound by the polymorphic definition above, example references are::

  f[{fld1: U8, fld2: U8},U32]
  f[U16,{fld1: U8, fld2: U8}]

where the second reference is illegal since the second type variable ``t`` is substituted by type 
``{fld1: U8, fld2: U8}``  which
is not regular.
