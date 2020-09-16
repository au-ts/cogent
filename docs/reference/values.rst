************************************************************************
                          Working with Values
************************************************************************

The main part of a |cogent| program
is usually about specifying values,
typically the result values of functions,
depending on argument values.


Patterns
====================================

Functional programming languages
typically use the concept of *pattern matching*,
which covers several concepts from
imperative or object-oriented languages,
such as binding values to variables,
accessing components of a value,
or testing for alternatives.
In |cogent|, patterns are
the most important language construct
for working with composite values.

A pattern is a language construct
which can be *matched* against values.
A pattern may contain *variables*;
matching a variable with a value
has the effect of *binding* the contained variables
to components of the matched value.
In |cogent|,  as in languages like Haskell or Scala,
a variable may occur at most once in a pattern;
hence, it is not possible to construct patterns
which restrict matching values
to have some parts which are equal to each other.

A pattern *conforms* to a type,
if it matches at least one value of the type.
A pattern can conform to several different types.

A pattern is *irrefutable*,
if it matches all values of all its conforming types.
Irrefutable patterns cannot be used
to discriminate between different sets of values:
they can only be used to bind contained variables.

If a pattern is matched against a value,
the match must always be exhaustive:
alternative patterns must be specified
which together cover the value's type.

The conforming types of a pattern
can always be inferred from
the syntactical structure of the pattern;
therefore, type expressions are not needed as part of patterns.

Syntactically, patterns may be put in parentheses for grouping:

  *Pattern*:
    | ``(`` *Pattern* ``)``
    | ...

A pattern in parentheses is equivalent to the pattern itself.


Simple Patterns
------------------------------

The simplest patterns consist of only one part. They may be irrefutable or not.


Irrefutable Simple Patterns
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A simple pattern can be a single variable or the special symbol ``_``, which is called the *wildcard* pattern:

  *Pattern*:
    | ``(`` *Pattern* ``)``
    | *IrrefutablePattern*
    | ...

  *IrrefutablePattern*:
    | *Variable*
    | *WildcardPattern*
    | ...

  *Variable*:
    | *LowercaseID*

  *WildcardPattern*:
    | ``_``

Both patterns conform to all types and are irrefutable, hence they match every possible value which may occur in |cogent|. If a variable ``x`` 
is matched with a value, the value is bound to ``x``. This means that in a certain *scope*, the value can be referenced by denoting 
the variable ``x``.

The *WildcardPattern* ``_`` contains no variable, therefore no variable can be bound when the pattern is matched with a value. 
The *WildcardPattern* is used when, for some reason, a value must be matched with a pattern but need not be referenced afterwards.

As for type and data constructors, the syntactically equal *Variable*\ s, *FieldName*\ s, and *TypeVariables*
constitute three different namespaces. The same lowercase identifier can be used to denote a term variable, a type variable, and
a record field in the same context without imposing any relation among them.


Refutable Simple Patterns
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Refutable simple patterns consist of a single literal:

  *Pattern*:
    | ``(`` *Pattern* ``)``
    | *IrrefutablePattern*
    | *LiteralPattern*
    | ...

  *LiteralPattern*:
    | *BooleanLiteral*
    | *IntegerLiteral*
    | *CharacterLiteral*

A *LiteralPattern* matches exactly one value, the value which is denoted by the literal. A *BooleanLiteral*  conforms only to type
``Bool``, a *CharacterLiteral* conforms  only to type ``U8``.

An *IntegerLiteral* conforms to every bitstring type which includes the value denoted by the literal. For example, the literal 100000 
conforms to types ``U32`` and ``U64`` but not to ``U16`` or ``U8``.

Since a *LiteralPattern* contains no variables, no variable can be bound when it is matched with a value. *LiteralPattern*\ s are used 
for discriminating the value from other values, not for binding variables.


Note that you cannot use a value bound to a variable like a literal in a pattern to match just that value. If a variable
occurs in a pattern it is always used for a new binding which shadows any value already bound to it. In particular,
this applies to variables bound in a toplevel value definition (see :ref:`value-def`).


Composite Patterns
------------------------------

Composite patterns conform to composite types. However, there are no patterns which conform to function types.

Tuple Patterns
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A tuple pattern is syntactically denoted by a tuple of patterns:

  *IrrefutablePattern*:
    | *Variable*
    | *WildcardPattern*
    | *TuplePattern*
    | ...

  *TuplePattern*:
    | ``()``
    | ``(`` *IrrefutablePattern* ``,`` *IrrefutablePattern* { ``,`` *IrrefutablePattern* } ``)``

The subpatterns in a tuple pattern must all be irrefutable. As a consequence, tuple patterns are also irrefutable.
Even the tuple pattern ``()`` is irrefutable, although it matches only a single value. Since it conforms only to the
unit type which has only this single value, it satisfies the requirements for an irrefutable pattern.

Note that, as for tuple types, there is no tuple pattern with only one subpattern, the corresponding syntactical 
construct like ``(v)`` is a pattern in parentheses and conforms to all types the inner pattern conforms to, not
only to tuple types.

A tuple pattern :math:`\texttt{(} p_1, \ldots, p_n \texttt{)}` with :math:`n \neq 1` conforms to every tuple type with :math:`n` fields where each subpattern
:math:`p_i` conforms to the type of the :math:`i`'th field. 

.. ::

   Since tuple types are right associative, the pattern also conforms to all
   tuple types with more than :math:`n` fields, if the rightmost pattern :math:`p_n` conforms to the tuple type built from the remaining fields
   starting with the :math:`n`th field.

If a tuple pattern is matched with a value, the subpatterns are matched with the corresponding fields of the value. 

.. ::

   If the value 
   has more fields, subpattern :math:`p_n` is matched with the tuple of all remaining fields. 

A useful case is a tuple pattern where all 
subpatterns are (distinct) variables. Such a pattern can be used to bind all fields of a tuple value to variables for subsequent access.

Here are some examples for tuple patterns::

  (v1, v2, v3)
  (v1, (v21, v22), _)
  ()

The first pattern conforms to all tuple types with three fields. The second pattern conforms to all tuple types with
three fields where the second field has a tuple type with two fields. The third pattern only conforms to the unit type.


.. _pat-rec:

Record Patterns
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Patterns for record values exist in two syntactical variants, depending on whether the record is boxed or unboxed:

  *IrrefutablePattern*:
    | *Variable*
    | *WildcardPattern*
    | *TuplePattern*
    | *RecordPattern*

  *RecordPattern*:
    | *Variable* ``{`` *RecordMatchings* ``}``
    | ``#`` ``{`` *RecordMatchings* ``}``

The main part *RecordMatchings* of a record pattern is used to match the fields and has the following syntax:

  *RecordMatchings*:
    | *RecordMatching* { ``,`` *RecordMatching* }

  *RecordMatching*:
    | *FieldName* [ ``=`` *IrrefutablePattern* ]

The basic case is a sequence of field names with associated subpatterns, such as in::

  fld1 = v1, fld2 = (v21, v22), fld3 = _

A record pattern with these *RecordMatchings* conforms to all record types which have at least three fields named
``fld1``, ``fld2``, and ``fld3``, and where ``fld2`` has a tuple type with two fields. More general, a record pattern 
where the *RecordMatchings* consist of pairs of field names and subpatterns conforms to all record types which have at least the named 
(untaken) fields and every subpattern conforms to the corresponding field type. Since all subpatterns must be irrefutable, the record pattern 
is irrefutable as well.

A special application of a record pattern is to bind field values to local variables which have the same name as the field itself. The effect 
is to make the fields of a record value locally accessible using their field names. This can be accomplished for a specific field by matching 
a record pattern with a *RecordMatching* of the form ``fldi = fldi``. Such a *RecordMatching* can be abbreviated by simply 
specifying the field name alone: ``fldi``, for example in the *RecordMatchings*::

  fld1, fld2 = (v21, v22), fld3, fld4

Note that since the field name as a variable conforms to all types, the corresponding record patterns conform to all record types which have a 
(untaken) field named ``fldi``, irrespective of the field type.



A record pattern starting with ``#`` conforms only to unboxed record types. When matched with a value,  for every 
field according to the value's type a subpattern must be present in the 
*RecordMatchings* and is matched to the corresponding field value. 

A record pattern starting with a *Variable* conforms  to boxed and unboxed record types. 
When matched with a value this variable is bound to the 
remaining record after matching the subpatterns in the *RecordMatchings*. 
This "remaining" record has as its type the type of the 
matched value with all fields taken which are matched in the *RecordMatchings*.  Matching
a pattern of this kind with a value is called a "take operation". 

The rationale for this is that boxed record types are 
linear and their values must be used exactly once. Matching only some fields would only use these 
fields and not the rest, which is not allowed. 
Hence the remaining record must also be matched so that it can be used as well. 
Even when all linear fields are matched the remaining 
record itself is still linear and must be preserved.


If value ``val`` has type::

  {fld1: U8, fld2: U16, fld3: U32}

an example take operation would be to match the pattern::

  v {fld1 = v1, fld3 = v3}

with ``val``. This will bind ``v1`` to the value of the first field, ``v3`` to the value of the
third field, and ``v`` to the remaining record of type::

  {fld1: U8, fld2: U16, fld3: U32} take (fld1,fld3)

where only the second field is still present.


Although the ordering of fields is relevant in a record type expression, it is irrelevant in a record pattern. 
Therefore the record pattern
``#{fld1 = v1, fld2 = v2}`` conforms to the types::

  #{fld1: U8, fld2: U16}
  #{fld2: U32, fld1: U32}

and all other unboxed record types which have two fields named ``fld1`` and ``fld2``.


When a field of non-linear type is taken from a (boxed or unboxed) record value, a copy of it could remain
in the record and could be taken again. |cogent| does not allow this, non-linear fields can also be taken
only once. This way it is possible to represent uninitialised fields in a record by specifying the record 
type with the corresponding fields being taken.


Variant Patterns
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A variant pattern consists of a data constructor and a subpattern for every payload value in the corresponding alternative:

  *Pattern*:
    | ``(`` *Pattern* ``)``
    | *IrrefutablePattern*
    | *LiteralPattern*
    | *VariantPattern*

  *VariantPattern*:
    | *DataConstructor* { *IrrefutablePattern* }

A variant pattern conforms to every variant type which has at least an alternative with the *DataConstructor* as its tag. Although a variant 
pattern matches all values of the type having only that alternative, this is not true for all other conforming types. For those types the pattern 
only matches the subset of value sequences which have been constructed with the *DataConstructor* as its discriminating tag. Therefore variant 
patterns are always refutable.  As usual, when matched with a value, the match must be exhaustive, specifying
a pattern for every alternative. 


When a variant pattern is (successfully) matched with a value, the subpatterns are matched with the payload values.


The following is an example for a variant pattern::

  TwoDim x, y

It conforms, e.g., to the variant type::

  <TwoDim U32 U32 | ThreeDim U32 U32 U32>

and generally to every type with a variant tagged with ``TwoDim`` and having two values. When it is matched 
with a value tagged with ``TwoDim`` the first payload value is bound to ``x`` and the second payload value is bound to ``y``. 
The pattern also conforms to the variant type::

  <TwoDim U32 U32>

Although it matches all values of this type, it is still a refutable pattern, even if no other variant types with ``TwoDim``
exist in the program.


Expressions
====================================

As usual in programming languages, an *expression* denotes a way how to calculate a value. The actual calculation of a value according 
to an expression is called an *evaluation* of the expression. Since an expression may contain variables which are not bound in the expression 
itself ("free variables"), the value obtained by evaluating an expression may depend on the context in which the free variables are bound.

Usually, when an expression occurs in a |cogent| program, a type may be *inferred* for it. There are several ways to infer an expression's type.
The most basic way is to infer its type from its syntactical structure, although there are cases where that is not possible.
If an expression has an
inferred type, the value resulting from evaluating the expression always belongs to this type.

The general syntactical levels of expressions are as follows:

  *Expression*:
    | *BasicExpression*
    | ...

  *BasicExpression*:
    | *BasExpr*
    | ...

  *BasExpr*:
    | *Term*
    | ...

  *Term*:
    | ``(`` *Expression* ``)``
    | ...

Every *Expression* can be used wherever a *Term* is allowed by putting it in parentheses.


Terms
------------------------------

The simplest expressions are called *terms*. A term specifies a value directly or, for a composite value, by specifying its parts. 

A term can be a single variable, denoting the value which has been bound to the variable in the context. 

  *Term*:
    | ``(`` *Expression* ``)``
    | *Variable*
    | ...

From the variable alone no type can be inferred. However, a type may be inferred when the variable is bound. Then this type is 
also inferred for every occurrence of the variable as a term in its scope.

Literal Terms
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Terms for values of primitive types are simply the literals:

  *Term*:
    | ``(`` *Expression* ``)``
    | *Variable*
    | *LiteralTerm*
    | ...

  *LiteralTerm*:
    | *BooleanLiteral*
    | *IntegerLiteral*
    | *CharacterLiteral*
    | *StringLiteral*

The inferred type for a *BooleanLiteral*, a *CharacterLiteral*, or a *StringLiteral* is ``Bool``,
``U8``, or ``String``, respectively.
The inferred type for a *IntegerLiteral* is the smallest bitstring type covering the value, thus the literal 
``200`` has inferred type ``U8``, whereas the literal ``300`` has inferred type ``U16`` and ``100000`` has 
inferred type ``U32``.

Terms for Tuple Values
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Terms for tuple values are written as in most other programming languages supporting tuples:

  *Term*:
    | ``(`` *Expression* ``)``
    | *Variable*
    | *LiteralTerm*
    | *TupleTerm*
    | ...

  *TupleTerm*:
    | ``()``
    | ``(`` *Expression* ``,`` *Expression* { ``,`` *Expression* } ``)``

Again, as for tuple types and patterns, a single *Expression* in parentheses is not a tuple term but
is only syntactically grouped.

An example tuple term is::

  (15, 'x', 42, ("hello", 1024))

which specifies 4 subexpressions for the fields, separated by commas.

The type inferred from the structure of a tuple term is the tuple type with the same number of fields as are present in the term, where
the field types are the types inferred for the subexpressions. If one of the subexpressions does not have an
inferred type then no type can be inferred from the tuple term's structure.

.. ::

   Since tuple types are right associative, the same holds for the tuple terms. Hence, the example term is equivalent
   to the terms::

     (15, 'x', 42, "hello", 1024)
     (15, ('x', (42, ("hello", (1024)))))

   but not to the term::
     (15, ('x', 42), "hello", 1024)


Terms for Record Values
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

|cogent| only suppoprts terms for unboxed record values. Boxed record values cannot be specified directly, they must
always be created externally in a C program part and passed to |cogent| as (part of) a function argument or result.

The syntax for terms for unboxed values specifies all field values together with the field names:

  *Term*:
    | ``(`` *Expression* ``)``
    | *Variable*
    | *LiteralTerm*
    | *TupleTerm*
    | *RecordTerm*
    | ...

  *RecordTerm*:
    | ``#`` ``{`` *RecordAssignments* ``}``

  *RecordAssignments*:
    | *RecordAssignments* { ``,`` *RecordAssignment* }

  *RecordAssignment*:
    | *FieldName* [ ``=`` *Expression* ]

An example is the record term::

  #{fld1 = 15, fld2 = 'x', fld3 = 42, fld4 = ("hello", 1024)}

which specifies 4 subexpressions for the fields, separated by commas. The field names must be pairwise different.
As for record types, but other than for record patterns, the order of the field specifications is significant. Hence
the term::

  #{fld2 = 'x', fld3 = 42, fld1 = 15, fld4 = ("hello", 1024)}

evaluates to a different value than the first example term.

The type inferred from a record type's structure is the unboxed record type with the same number of fields in the same order 
as are present in the expression, named according to the names given in the term. The field types are the types inferred
for the subexpressions. If a subexpression has no inferred type, no type can be inferred from the record term's structure.

Terms for Values of Variant Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A term for a value of a variant type specifies the discriminating tag and the actual payload values:

  *Term*:
    | ``(`` *Expression* ``)``
    | *Variable*
    | *LiteralTerm*
    | *TupleTerm*
    | *RecordTerm*
    | *VariantTerm*
    | ...

  *VariantTerm*:
    | *DataConstructor* { *Term* }

Examples for such terms are::

  Small 42
  TwoDim 3 15


For a *VariantTerm* it is not possible to infer a type from its structure, since there may be several 
variant types using the same *DataConstructor*. The |cogent| compiler even does not infer the type if there
is only one variant type using the *DataConstructor* as tag.


.. _term-lambda:

Terms for Values of Function Types
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A term for a value of a function type is, as usual, called a *lambda expression*. Often in other programming languages, a lambda
expression consists of a body expression and a variable for every argument. In |cogent| all functions take only one
argument, therefore only one variable is needed. However, more general than a variable, an irrefutable pattern may be 
used. Every application of such a function is evaluated by first matching the pattern against the argument value,
thus binding all variables contained in the pattern. Then the body expression is evaluated in the context of
the bound variables to yield the result.

The syntax for lambda expressions is:

  *Term*:
    | ``(`` *Expression* ``)``
    | *Variable*
    | *LiteralTerm*
    | *TupleTerm*
    | *RecordTerm*
    | *VariantTerm*
    | *LambdaTerm*
    | ...

  *LambdaTerm*:
    | ``\`` *IrrefutablePattern* [ ``:`` *MonoType* ] ``=>`` *Expression*

Optionally, the argument type may be specified explicitly after the pattern. If no unique conforming type can be inferred for
the pattern, the argument type is mandatory.

Examples for lambda terms are::

  \x => (x,x)
  \(x,y,z) (U8, U8, Bool) => #{fld1 = y, fld2 = (x,z)}
  \(x,y) : (U32,U32) => TwoDim y x

In the first case the argument type must be known from the context by knowing an inferred type for the lambda term,
for example the type ``U8 -> (U8,U8)``. In the third case the result type must be known from the context by knowing
an inferred type for the lambda term, for example the type::

  (U32,U32) -> <TwoDim U32 U32 | Error U8>


The body expression in a lambda term is restricted to not contain any free non-global variables. Non-global variables
are variables bound by pattern matching in contrast to *global* variables which are bound by a toplevel definition
(see :ref:`toplevel-def`).

If the body expression of a lambda term has inferred type T2 and the argument type is explicitly specified as T1 then
the type inferred from the structure of the *LambdaTerm* is T1 ``->`` T2.


Basic Expressions
------------------------------

Basic expressions are constructed from terms in several ways, which all correspond semantically to a function application.

Plain Function Application
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

As is typical for functional programming languages, a value in |cogent| can be a function and it can be applied to arguments.

As we have seen with function types, in |cogent| all functions have only one argument. Hence, an expression for a function application 
consists of a term for the function and a second term for the argument:

  *BasExpr*:
    | *Term*
    | *FunctionalApplication*
    | ...

  *FunctionApplication*:
    | *BasExpr* *BasExpr*

The argument Expression is simply put after the Expression for the function. This is common in functional programming languages, whereas in
imperative and object oriented languages (and in mathematics) the argument is usually put in parentheses like in :math:`f(x)`. In |cogent|
this is allowed, since a *BasExpr* may be an expression in parentheses, but it is not necessary.

The syntax here is ambiguous. Several *BasExpr* in a row are interpreted as left associative. Therefore the following
two *BasExpr* are equivalent::

  f 42 17 4
  ((f 42) 17) 4


If the first *BasExpr* in a *FunctionApplication* has an inferred type it must be a function type T1 ``->`` T2.
If the second *BasExpr* has an inferred type it must be equal to T1. The type inferred from the *FunctionApplication*\ s
structure is type T2.

As an example, if the variable ``f`` is bound to a function of type ``U8 -> U16`` then the basic expression::

  f 42

is a *FunctionApplication* with a result of type ``U16``.

Operator Application
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In |cogent| there is a fixed set of predefined functions. These functions are denoted by *operator symbols* which are syntactically
different from variables. In contrast to normal functions, predefined functions may be binary, i.e., take two arguments. Binary 
operator applications are written in infix notation:

  *BasExpr*:
    | *Term*
    | *FunctionApplication*
    | *OperatorApplication*
    | ...

  *OperatorApplication*:
    | *UnaryOp* *BasExpr*
    | *BasExpr* *BinaryOp* *BasExpr*

  *UnaryOp*: one of
    | ``upcast``
    | ``complement``
    | ``not``

  *BinaryOp*: one of
    | ``o`` ``*`` ``/`` ``%`` ``+`` ``-``
    | ``>`` ``<`` ``>=`` ``<=`` ``==`` ``/=``
    | ``.&.`` ``.^.`` ``.|.`` ``>>`` ``<<``
    | ``&&`` ``||`` ``$``

As usual in most programming languages, the syntax here is ambiguous and operator precedence rules are used
for disambiguation. The precedence levels ordered from stronger to weaker binding are::

  upcast complement not <plain function application>
  o
  * / %
  + -
  > < >= <= == /=
  .&.
  .^.
  .|.
  >> <<
  &&
  ||
  $

Note that plain function application is treated like a binary invisible operator, where the first argument is the 
applied function and the second argument is the argument to which the function is applied. 

When binary operators on the same level are combined they are usually left associative, with the exception of 
``o``, ``&&``, ``||`` and ``$``  which are right associative and ``<``, ``>``, ``<=``, ``>=``, ``==``, ``/=`` which 
cannot be combined.

.. todo:: describe all operation semantics and inferred types


.. _expr-put:

Put Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A common function used in functional programming languages is the record update function. It takes a record
value and returns a new record value where one or more field values differ. In |cogent| the 
application of this function is restricted: if a field has a linear type, it cannot be replaced, since then
its old value would be discarded without being used. In this case the field can only be replaced, when
it has been taken in the old value. For this reason the record update function is called the "put function"
in |cogent|. For non-linear fields the put function may either put a value into a taken field or replace
the value of an untaken field.

|cogent| supports a *PutExpression* as specific syntax for applying the put function. It specifies the old record value and 
a sequence of new field values together with the corresponding field names:

  *BasExpr*:
    | *Term*
    | *FunctionalApplication*
    | *OperatorApplication*
    | *PutExpression*
    | ...

  *PutExpression*:
    | *BasExpr* { *RecordAssignments* }

As an operator the *RecordAssignments* have the same precedence as plain function application and the unary operators.

If a type T is inferred for the leading *BasExpr* in a *PutExpression*, T must satisfy the following conditions: it must
be a (boxed or unboxed) record type having all fields occurring in the *RecordAssignments*. If such a field has
a linear type it must be taken in T. The type inferred from the structure of the *PutExpression* then is
T ``put (fld1, ..., fldn)``,
where ``fld1``, ..., ``fldn`` are all fields occurring in the *RecordAssignments*.

Unlike in a record term, the field order in a *PutExpression* is not significant.

If the variable ``r`` is bound to a value of type ``R`` where::

  typedef A
  typedef R = {fld1: A, fld2: U32, fld3: (Bool,U8), fld4: A} 
              take (fld3,fld4)

and variable ``a`` is bound to a value of type ``A``, then the following are valid put expressions::

  r {fld2 = 55, fld3 = (True, 17)}
  r {fld4 = a, fld2 = 10000}

The first expression has inferred type ``R put (fld2,fld3)`` which is equal to the type::

  {fld1: A, fld2: U32, fld3: (Bool,U8), fld4: A} take (fld4)

The expression ``r {fld1 = a}`` is invalid since field ``fld1`` is untaken and has linear type.

Member Access
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A second function commonly provided for records is *member access* or projection, often denoted by a separating dot
in programming languages. |cogent| provides the same syntax for member access:

  *BasExpr*:
    | *Term*
    | *FunctionalApplication*
    | *OperatorApplication*
    | *PutExpression*
    | *MemberAccess*

  *MemberAccess*:
    | *BasExpr* ``.`` *FieldName*

Here, the *BasExpr* specifies the record value and the *FieldName* specifies the name of the field to be accessed.
As an operator, the dot in a *MemberAccess* has the highest precedence, higher than the unary operators.

Again, in |cogent| the use of member access is restricted. The type inferred for the leading *BasExpr* in a *MemberAccess*
must be either an unboxed record type or a readonly boxed record type. Then it is possible to use the value of only one field
without caring about the other fields. Moreover, also the type of the accessed field must be non-linear, since
in addition to being accessed, its value also remains in the record, hence it could be used twice.

The type inferred from the *MemberAccess* expression structure is the type of the field named by the *FieldName*.

If types ``A`` and ``R`` are defined as in :ref:`expr-put` and ``r`` is bound to a value of type ``R!``
then the basic expression ``r.fld2`` is a valid *MemberAccess*. The basic expression
``r.fld3`` is invalid since field ``fld3`` is taken in ``R!``, the basic expression 
``r.fld1`` is valid since field ``fld1`` has type ``A!`` in ``R!`` (due to recursive application of the bang operator).
If ``r`` is bound to a value
of type ``R`` then also the basic expression ``r.fld2`` is invalid since type ``R`` is linear.


General Expressions
------------------------------

In |cogent| the most general concept for specifying a calculation as an expression is *matching*. All other
forms of general expressions can be understood as specific variants of matching.


Matching Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A *MatchingExpression* matches a value against one (irrefutable) pattern or several (refutable) patterns.
For every pattern a subexpression is specified for the result:

  *Expression*:
    | *BasicExpression*
    | *MatchingExpression*
    | ...

  *MatchingExpression*:
    | *ObservableBasicExpression* *Alternative* { *Alternative* }

  *ObservableBasicExpression*:
    | *BasicExpression*
    | ...

  *Alternative*:
    | ``|`` *Pattern* *PArr* *Expression*

  *PArr*: one of
    | ``->``
    | ``=>``
    | ``~>``

All *Expression*\ s in the *Alternative*\ s must have equal inferred types, this is also the
type inferred from the *MatchingExpression*\ s structure.

For every *Alternative* the *Expression* is called the *scope* of the variables occurring in 
the *Pattern*.

All *Pattern*\ s in the *Alternative*\ s must conform to the type T inferred for the leading expression.
The *Pattern*\ s together must be exhaustive for T, that means, every value of type T must match one of them. This
may be accomplished by using an exhaustive set of refutable patterns, such as one for every alternative in a variant type,
or by optionally specifying some refutable patterns followed by a final alternative with an irrefutable pattern.


The order in which alternatives are specified is irrelevant. The pattern syntax in |cogent| 
guarantees that different refutable patterns cannot partially overlap, i.e. the sets of matching values
are disjunct or equal. Moreover, a refutable pattern may be specified in at most one alternative. Together,
every value matches at most one of the refutable patterns, there is no need to resolve conflicts.
An irrefutable pattern is only used when no refutable pattern matches.


If the variable ``x`` is bound to a value of type ``U8`` an example for a *MatchingExpression* is::

  x + 7 | 20 -> "too much"
        | 10 -> "too few"
        | _  -> "unknown"

It has the inferred type ``String``.

If the variable ``v`` is bound to a value of the variant type::

  < TwoDim U32 U32 | ThreeDim U32 U32 U32 | Error U8 >

then the following is a valid *MatchingExpression* with inferred type ``U32``::

  v | TwoDim   x y   -> x+y
    | ThreeDim x y z -> x+y+z
    | Error    code  -> 0

whereas::

  v | TwoDim   x y   -> x+y
    | ThreeDim x y z -> x+y+z

is invalid since it is not exhaustive for the type of ``v``.

.. todo: Using layout for Alternative grouping


Alternatively to the separator ``->`` the separators ``=>`` and ``~>`` can be used in an *Alternative*.
Semantically they have the same meaning, however they may allow for some code optimisation when the first is used for 
"likely" alternatives and the second for "unlikely" alternatives.


.. _expr-let:

Binding Variables
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If the only intention for using a *MatchingExpression* is binding variables, the simpler *LetExpression*
syntax can be used:

  *Expression*:
    | *BasicExpression*
    | *MatchingExpression*
    | *LetExpression*
    | ...

  *LetExpression*:
    |  ``let`` *Binding* { ``and`` *Binding* } ``in`` *Expression*

  *Binding*:
    | *IrrefutablePattern* [ ``:`` *MonoType* ] ``=`` *ObservableExpression*

  *ObservableExpression*:
    | *Expression*
    | ...

A simple *LetExpression* is equivalent to a *MatchingExpression* with one *Alternative*::

  let IP = E in F

is semantically equivalent with::

  E | IP -> F

From this it follows that pattern IP must conform to the type inferred for E and the type inferred
from the *LetExpression*\ s structure is that inferred for F. The expression F is also called the "body" of the
*LetExpression*, it is the scope of the variables in IP.

The *LetExpression*::

  let x = y + 5 in (True, x)

binds the variable ``x`` to the result of evaluating the expression ``y + 5`` and evaluates to a tuple
where the bound value is used as the second field value. The tuple expression is the scope of variable ``x``.

If types ``A`` and ``R`` are defined as in :ref:`expr-put` and ``r`` is bound to a value of type ``R``
then the *LetExpression*::

  let s {fld1 = x, fld2} = r in (x, fld2 + 5, s)

binds the variables ``s``, ``x``, and ``fld2`` by matching the pattern against the value bound to ``r``
as described in :ref:`pat-rec`. Then it uses them in their scope which is a tuple term. 
The type inferred for the *LetExpression* is::

  (A, U32, R take (fld1, fld2))

In a *Binding* optionally a *MonoType* may be specified:

  IP ``:`` T ``=`` E

If neither for E nor the pattern IP a type can be inferred the type specification is mandatory.

If E is an *IntegerLiteral* of type U  and T is a bitstring type which is a superset of U then 
the value of E is automatically widened to type T before matching it against IP. Therefore the *LetExpression*::

  let x: U32 = 5 in (True, x)

has inferred type ``(Bool, U32)``, although the literal ``5`` has type ``U8``.

A *LetExpression* of the form

  ``let`` B1 ``and`` B2 ``in`` F

is simply an abbreviation for the nested *LetExpression*

  ``let`` B1 ``in`` ``let`` B2 ``in`` F

A *LetExpression* which uses the wildcard pattern

  ``let`` ``_`` ``=`` E ``in`` F

can be abbreviated to

  E ``;`` F

using the following syntax:

  *BasicExpression*:
    | *BasExpr*
    | *BasExpr* ``;`` *Expression*

Since a *LetExpression* is only used to bind variables occurring in the pattern and there
is no variable in the wildcard pattern this case seems to be useless. Its only use is when
expression E has side effects. Note that functions which are completely defined in |cogent| do
not have side effects, however, functions defined externally can have side effects.

An example usage would be an externally defined function of type ``String -> ()`` which is
bound to the variable ``print`` and prints its *String* argument to a display. Then 
the expression::

  v | TwoDim   x y   -> print "flat"; x+y
    | ThreeDim x y z -> print "space"; x+y+z
    | Error    code  -> print "crash"; 0

would print one of the strings to the display whenever it is evaluated.


Conditional Expressions
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If the only intention for using a *MatchingExpression* is discrimination between two cases
the *ConditionalExpression* can be used which is nearly omnipresent in programming languages.
It has the usual syntax:

  *Expression*:
    | *BasicExpression*
    | *MatchingExpression*
    | *LetExpression*
    | *ConditionalExpression*

  *ConditionalExpression*:
    | ``if`` *ObservableExpression* ``then`` *Expression* ``else`` *Expression*

The *ConditionalExpression*::

  if C then E else F

is equivalent to the *MatchingExpression*::

  C | True  -> E
    | False -> F

From this it follows that ``C`` must have the inferred type ``Bool`` and ``E`` and ``F`` must have the same inferred type 
which is the type inferred from the *ConditionalExpression*\ s structure.

If a *MatchingExpression* discriminates among more than two cases, as usual
a nested *ConditionalExpression* can be used instead. 

.. todo:: Using layout to disambiguate nested ConditionalExpressions

An example for a *ConditionalExpression* is::

  if x > 5 then (True, "sufficient") else (False, "insufficient)

It has the inferred type ``(Bool, String)``.


Observing Variables
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

At some places variables can be "observed" in an expression. Observing a variable means replacing its bound
value with a copy of readonly type. Observing variables is the only way how values of readonly types can be
produced in |cogent|.

When a variable should be observed, an expression must be specified as scope of the observation. The readonly
value may be freely used in this scope, but it may not escape from it. Syntactically, an expression which may 
be the scope of a variable observation is called an *observable expression*.
The syntax for variable observation is as follows:

  *ObservableBasicExpression*:
    | *BasicExpression*
    | *BasicExpression* { ``!`` *Variable* }

  *ObservableExpression*:
    | *Expression*
    | *Expression* { ``!`` *Variable* }

In both cases one or more observed variables are specified at the *end* of the observation scope
using the "bang" operator as a prefix. Examples for *ObservableExpression*\ s are::

  if isok #{fld1=x, fld2=x, fld3=z} then 5 else 0 !x !y
  let v1 = x and v2 = x and v3 = z in (1, 2, 3) !x !z

If there is at least one banged variable in an observable expression, then the inferred type of the scope
may not be an escape-restricted type. 

The *ObservableExpression* ``E !V``
is conceptually equivalent to a *LetExpression* of the form

  ``let`` V ``=`` ``readonly`` V ``in`` E

where ``readonly`` would be an operator which produces a readonly copy from a value. An important effect of
this form is that the variable used for the readonly copy has the same name as the variable containing the original
value. Therefore the former variable shadows the latter in its scope, making the original value inaccessible there.

The operator ``readonly`` does not actually exist in |cogent|, hence expressions of the second form cannot be used
to bind readonly copies. This guarantees that the variable for the readonly copy *always* shadows the
original value in its scope.

Observable expressions may only occur in three places: As the leading expression in a *MatchingExpression* and 
in the corresponding position in the more specific forms, which is the right-hand side of a *Binding* in a 
*LetExpression* and the condition in a *ConditionalExpression*. 


.. _expr-usage:

Expression Usage Rules
====================================

|cogent|'s linear type system implies additional restrictions on expression usage over the usual restriction that
the type of a function argument must be compatible to the parameter type. The additional rules are described in 
this section.


Using Values of Linear Types
------------------------------

The basic rule for linear types is that their values must be used exactly once. For observing this rule it must 
be specified in more detail, what it means to use a value.

Sharing a Value
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

In a |cogent| program, values are always denoted by expressions. If an expression is a *Term* for a tuple, a record,
or a variant type, or if it is a *BasExpr* representing the application of a function or operator, or if it is
a *MatchingExpression* or one of its specific variants, the value is created by evaluating the expression. Then
it can only be used at most once: at the position where the expression syntactically occurs in the program. In the remaining
cases the expression is either a single variable or a *MemberAccess* (values of literals are never linear). 
A value 
bound to a variable can be used more than once: it is used at all places where it is referenced by
the variable name in its scope. The value of a record field can be used more than once by accessing the field
several times. In both cases we say the value may be "shared".

When a record field is accessed its value is not taken from the record, hence it is already shared between the record
and the access result upon a single member access. As a consequence, record fields of linear type may not be accessed
using a *MemberAccess* expression.

Hence the rule for using values of linear types not more than once is only relevant for variables: 
if a variable has a 
bound value of a linear type, the value must be used at most once by referencing it, it may not be shared. However, 
as can be seen for the variable ``v`` in the example::

  if x == 5 then f v else g v

the number of uses of the value is not simply the number of occurrences of the variable name in its scope.  Instead,
the rule is that a variable of linear type must occur at most once in all possible paths of an execution. Thus,
for a *ConditionalExpression* it must either occur once in the condition, or in each branch. For
a *MatchingExpression* it must either occur once in the leading 
*ObservableBasicExpression*, or in each *Alternative*.

Note that the field names in a *RecordTerm*, a *PutExpression*, a *RecordPattern* or a
*MemberAccess* are irrelevant, even if a field is present with the same name as the variable. Moreover,
only free occurrences count. If a variable of the same name is bound in the scope, the binding and its usages
are irrelevant for the original variable. Variables are bound by *LetExpression*\ s, 
*ObservableExpression*\ s, *ObservableBasicExpression*\ s, and *LambdaTerm*\ s.


Discarding a Value
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


If a variable is never used in its scope its value is "discarded". Values of linear type
may not be discarded. This is guaranteed for values bound to a variable, if it is used in every possible path of 
execution. 


Although the value of an expression other than a variable or member access cannot be used more than once, it can be discarded
by matching the expression with a pattern other than a variable or a boxed record pattern. In the case of the wildcard pattern 
as in::

  let _ = someExpression

the expression ``someExpression`` may have a linear type, then this matching would be illegal. In the case of a 
*LiteralPattern* the expression must always have a primitive type which is never linear. The same holds for an expression
which occurs as condition in a *ConditionalExpression*. 

In the case of a 
*TuplePattern*, a *VariantPattern* or an unboxed *RecordPattern* the expression only has a linear
type if it has components of a linear type. Then it is no problem to discard the value as long as no component of a 
linear type is discarded, as in::

  let (a, #{fld1= _, fld2=b}, c) = someExpression

In this case the ``fld1`` of the second field of the value is discarded which would be illegal if it has linear type.


A record field is also discarded if it is replaced in a *PutExpression*. Therefore in a *PutExpression*
the leading *BasExpr* must not have linear fields which are put, if there are linear fields they must have been taken.

The value of an expression is discarded when the expression is used as the *BasExpr* in a *MemberAccess*.

Together, linear values could be discarded by binding them to a variable which is never used in its scope, by matching them 
with the wildcard pattern, by replacing them in a *PutExpression*, or by using them as the record in a *MemberAccess*.
All these cases are not allowed for values of linear type in |cogent|.

However, there are two other cases which specifically apply to values of a boxed record type. If such an expression is used 
as the leading expression in a *PutExpression* or if it is matched against a *RecordPattern*, it is discarded
as well. These two cases are allowed in |cogent|. Note that in both cases a new value of the same type is created, in the
first case it becomes the result of the *PutExpression*, in the second case it is bound to the leading variable of the
*RecordPattern*.


The Result of Using a Value
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

What happens to a value after it has been used? "Using" here only means a *syntactical* usage, it does not mean
that the value is dismissed afterwards. Depending on the context of usage there are three possibilities: the value may immediately
be used in the context, it may become a part of another value (its "container" value), or it may be bound to a variable.

If the value results from evaluating an expression E in an *Alternative*, in a branch of a *ConditionalExpression*, or 
in the body of a *LetExpression*, then the value becomes the evaluation result of the expression containing E and is immediately
used in the context.

If expression E occurs as subexpression in a tuple term, a record term, or a variant term, or in a *RecordAssignment* of
a *PutExpression*, its evaluation result becomes a part of its container value created by the term or *PutExpression*, 
respectively. Since a value of linear type may be used only once, it is always the part of at most one container value. The container
value, since it has a part of linear type is also of linear type and behaves in the same way. 

Whenever a container value is used, it is used with all its parts. A linear part can be separated from its container by matching the
container value with a complex pattern which binds the part to a variable and dismisses the container. If the container is a boxed
record, a new container will be created where the part is taken. Thus, after binding the part to a variable 
it is not a part of its container anymore.

If expression E is the leading expression in a *MatchingExpression*, or occurs in a *Binding* of a *LetExpression*, 
or is the argument in a *FunctionApplication*,
then it is matched against a pattern. If the pattern is a variable, the evaluation result is bound to the variable. It remains bound to
it until the evaluation of its scope ends. However, if the value is of linear type, it cannot be referenced by the variable after
its first use, hence thereafter the binding is irrelevant.

Note that the body expression in a *LambdaTerm* is not evaluated when evaluating the *LambdaTerm* to yield a function.
The body will only be evaluated when the function is applied to an argument.

Taking it all together, the usage rules imply that a linear value in a pure |cogent| program is always either bound to exactly one variable 
which has not yet been used or it is a part of exactly one container value which also is linear. In a |cogent| program linear values are 
only dismissed and created in *PutExpression*s and by matching boxed *RecordPatterns*. In both cases a boxed record value is 
dismissed and a value of the same type is created.

These properties are exploited by |cogent| in the following way. Whenever a boxed record is dismissed it is "reused" to create the 
new value. Since the new value only differs from the old value by some fields having a different value, the old value is *modified*
by replacing these field values. As a consequence, linear values are *never* created or destroyed in a |cogent| program, 
they are only passed around as a single copy, possibly being modified on their way. Creating or destroying linear values must be accomplished 
externally implemented in C.


Using Values of Readonly Types
------------------------------

The basic rule for readonly types is that their values may not be modified. Of course, since |cogent| is a functional language,
values are conceptually never modified. However we have seen that value modification occurs in |cogent| as an optimisation for
linear values, although semantically this modification can never be observed. 


Modifying a Value
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The only way to modify a value in |cogent| is by changing the value of a field in a boxed record. This can be achieved
with the help of a *PutExpression* where a new value is specified for a field. It can also be achieved with the
help of a  take operation by matching a *RecordPattern* with a boxed record value. 

Therefore the following rules apply to values of readonly types:

- a value of readonly type may not be used as the leading *BasExpr* in a *PutExpression*,
- a value of readonly type may not be matched against a  record pattern.



When taking a field from a readonly record it is irrelevant whether the field has linear type or not. In both cases
the record would be modified which is not allowed. If the field has non-linear type, the taken value could
remain in the record. However, |cogent| implements taking fields always by removing the field value from the record, 
thus modifying the record.


Creating readonly Values
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The only way to create a value of readonly type is to apply the bang operator to a variable in an
*ObservableExpression* or *ObservableBasicExpression*. This creates a readonly copy of the bound value
and binds it to the same variable, using the subexpression  before the first banged variable  as scope for this binding. We call this subexpression a
banged scope. If the previously bound value had the linear type T, the readonly copy has type T! which is readonly or contains
readonly parts.

Note that the original binding is shadowed in the banged scope, hence the linear value cannot be referenced there, 
in particular, it cannot be modified. This is exploited by |cogent| in the following way. The original value is 
actually not copied at all, it remains bound to its variable. Only its type as seen through the variable is changed to T!
in the banged scope. 

In the banged scope the readonly copies can be freely duplicated, bound to any number of variables and inserted
as parts in any number of container values.


Preventing Values from Escaping
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

When execution leaves the banged context the shadowing ends and original value of linear type may be accessed again
and may be modified. Although all copies are still of readonly type, they would be modified as well, since actually
they have not been copied. This problem is solved by |cogent| by preventing the copies to "escape" from the banged 
scope. Then they cannot be referenced and observed outside the scope and modifications to the original value
are no problem.

If a readonly copy is bound to a variable, the scope of this binding must be syntactically enclosed in the banged
scope and cannot be referenced outside. The only way a value can escape from the banged scope is if it is the result
value the banged scope evaluates to or a part of it. This must be prevented by |cogent|.

It seems that to achieve this |cogent| has to "track" all readonly copies and prevent them to become a part of 
the result value. However, it is impossible to do this statically, since a copy can be passed to an externally
defined function which may return it as part of its result without |cogent| knowing this. Therefore a simpler
but much more radical approach is used, by preventing *all* values with an escape-restricted type from
escaping from *any* banged scope, irrespective whether it is related to the value or type of the 
banged variable. This safely also prevents the readonly copies from escaping. 

This approach can be implemented with the help of type checking. The rule to apply is that the type inferred 
for a banged scope in an *ObservableExpression* or *ObservableBasicExpression* must not be
escape-restricted.

This rule implies that even readonly values which existed outside of the banged scope cannot be used as part
of its result. Normally this is not a problem since they are available outside the banged scope anyways.
However, if the value's type is both escape-restricted and linear, the situation is different. Due to
the linearity, the value must not be discarded in the banged scope, it must leave it, which is not allowed
either. The solution here is to separate all escape-restricted parts from the rest, discard them in the 
banged scope and let the rest escape.

