************************************************************************
                             Surface Syntax
************************************************************************

.. note::
   As described in `#324`_,
   we are in the progress of revising the surface syntax;
   it's subject to change in near future.

.. _`#324`: https://github.com/NICTA/cogent/issues/324


Lexical Syntax
======================================================

The basic lexical items in |cogent| are
comments (including documentation blocks and pragmas),
identifiers (including reserved words),
symbols and literals.
Additionally, in a |cogent| program,
many C preprocessor directives can be used.


Comments
------------------------------------

Comments have the same form as in Haskell:
a comment may either be a single-line comment
starting with the symbol ``--``
and ending at the end of the line,
or it may be a block comment
enclosed in ``{-`` and ``-}``.

Block comments may occur in |cogent| source
between all other lexical entities.
Block comments can nest:
the closing brace of the inner comment
does not end an outer comment.

Some examples of comments are::

  f: U8 -> U8 -- this is a line comment after a function signature

  f x {- x is the function argument -} = x+1
    -- function f returns its incremented argument

  {- This is a comment with a nested {- inner comment. -}
     After it the outer comment continues. -}


A special form of comments are document blocks.
They have a similar form to line comments,
but start with the symbol ``@``.
Document blocks can be used
to generate HTML documentation
from |cogent| source using Docgent::

  @@ # Heading
  @@ This is a standalone documentation block

  @ Documentation for the following function
  f: U8 -> U8
  f x = x+1


Another special form of comments are pragmas,
which have the form::

  {-# ... #-}

Pragmas are used to optimise |cogent| programs,
and to interface external C components.
The details of pragmas are not (yet?) covered by this manual.

.. todo:: (jashankj, 2020-09-17): add pragma documentation somewhere


Identifiers
------------------------------------

Identifiers are used to name items in a program.
As usual in programming languages,
they consist of a sequence of letters and digits,
beginning with a letter.

|cogent| syntactically distinguishes between
lowercase identifiers and capitalized identifiers:

  *LowercaseID*: informally,
    | a sequence of letters, digits, underscore symbols, and single quotes
    | starting with a lowercase letter

  *CapitalizedID*: informally,
    | a sequence of letters, digits, underscore symbols, and single quotes
    | starting with an uppercase letter

The single quote, ``'``, may appear in an identifier
anywhere except at the beginning.
The underscore, ``_``, may appear in an identifier
anywhere except the beginning and end.

Examples for valid identifiers are
``v1``, ``very_long_identifier``,
``CamelCase``, ``T``, ``W_h_y``,
and ``v'``.

Lowercase identifiers are used
for record field names, and
for term variables and type variables.
Capitalized identifiers are used
for type constructors and data constructors.

There are some *reserved words* in |cogent|,
which syntactically are identifiers,
but cannot be used as identifiers.
The reserved words are, in alphabetical order::

  all and at complement else if in include inline layout let not o
  pointer put rec record take then type upcast variant True False

  array map2 @put @take

.. todo:: (jashankj, 2020-09-17): where did ``end`` and ``repr`` go?


Literals
------------------------------------

There are four kinds of literals in |cogent|.


Boolean Literals
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The Boolean literals are the reserved words ``True`` and ``False``.

  *BooleanLiteral*: one of
    | ``True``
    | ``False``

The type of a Boolean literal is ``Bool``.


Integer Literals
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Integer literals are digit sequences.
They can be written in decimal, hexadecimal, or octal form.

  *IntegerLiteral*: one of
    | *DecDigits*
    | ``0x`` *HexDigits*
    | ``0X`` *HexDigits*
    | ``0o`` *OctDigits*
    | ``0O`` *OctDigits*

  *DecDigits*: informally,
    | a sequence of decimal digits 0-9.

  *HexDigits*: informally,
    | a sequence of hexadecimal digits 0-9, A-F.

  *OctDigits*: informally,
    | a sequence of octal digits 0-7.

.. todo:: (jashankj, 2020-02-14): what type have int literals?


Character Literals
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A character literal consists of a quoted character.

  *CharacterLiteral*: informally,
    | a character enclosed in single quotes.

The type of a character literal is ``U8``,
corresponding to a single eight-bit byte.
Syntactically,
a character literal can be specified as in Haskell
(see the Haskell Report),
i.e., full Unicode and several escape sequences (such as ``\n``) are supported.
However, a valid character literal in |cogent|
must always correspond to a code value in the range 0..255.

Examples for valid character literals are ``'h'``, ``'8'``, and ``'/'``.
The quoted character ``'\300'`` is not a legal character literal,
since it is mapped to octal 0o300 (decimal 192).

.. todo:: (jashankj, 2020-02-14): uh, that octal 300 is probably ok?


String Literals
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

A string literal consists of a quoted character sequence.

  *StringLiteral*: informally,
    | a sequence of characters enclosed in double quotes.

Syntactically,
a string literal can be specified as in Haskell ---
again, see the Haskell Report.
As with character literals,
escape sequences are supported
for specifying every character.
For a valid |cogent| string literal,
every character must be mapped to
a code in the range 0..255.

An example for a valid string literal is
the string ``"This is a string literal\n"``.
Again, the string ``"String containing a \300 glyph"`` is not legal,
since it contains a character mapped to code 0o300.

.. todo:: (jashankj, 2020-02-14): sensible octal literal in a string?
