************************************************************************
                             Lexical Syntax
************************************************************************

The basic lexical items in |cogent| are comments (including document blocks and pragmas), identifiers (including reserved words), symbols and literals.
Additionally in a |cogent| program the usual Haskell preprocessor directives can be used, which are similar to the C preprocessor directives.


Comments
====================================

Comments have the same form as in Haskell. A comment may either be a line comment
starting with the symbol ``--`` and ending at the end of the line, or it may
be a block comment enclosed in ``{-`` and ``-}``.

Examples of comments are::

  f: U8 -> U8 -- this is a line comment after a function signature
  f x {- x is the function argument -} = x+1
    -- function f returns its incremented argument

Block comments may occur in a |cogent| source between all other lexical entities.  Block comments can be nested,
the closing brace of the inner comment does not end the outer comment::

  {- This is a comment with a nested {- inner comment. -}
     After it the outer comment continues. -}

A special form of comments are document blocks. They have a similar form like line comments but start 
with the symbol ``@``. Document blocks can be used to generate an HTML documentation from a Cogent source::

  @@ # Heading
  @@ This is a standalone documentation block

  @ Documentation for the following function
  f: U8 -> U8
  f x = x+1

Another special form of comments are pragmas, they have the form::

  {-# ... #-}

Pragmas are used to optimise Cogent programs and to interface external C components. The details
of pragmas are not (yet?) covered by this manual.


Identifiers
====================================

Identifiers are used to name items in a program. As usual in programming languages, they consist of
a sequence of letters and digits beginning with a letter.

|cogent| syntactically distinguishes between lowercase identifiers and capitalized identifiers.

  *LowercaseID*: informally,
    | a sequence of letters, digits, underscore symbols, and single quotes
    | starting with a lowercase letter

  *CapitalizedID*: informally,
    | a sequence of letters, digits, underscore symbols, and single quotes
    | starting with an uppercase letter

The underscore symbol ``_`` and the single quote ``'`` may appear in identifiers but not at the beginning. Examples for valid 
identifiers are ``v1``, ``very_long_identifier``, ``CamelCase``, ``T``, ``W_``, and ``v'``.

Lowercase identifiers are used for record field names and for term variables and type variables. Capitalized identifiers are
used for type constructors and data constructors.

There are some *reserved words* in |cogent| which syntactically are identifiers but cannot be used as identifiers.
The reserved words are in alphabetical order::

  all and complement else False if in include let not put
  take then True type


Literals
====================================

There are four kinds of literals in |cogent|.


Boolean Literals
------------------------------

The boolean literals are the reserved words ``True`` and ``False``.

  *BooleanLiteral*: one of
    | ``True``
    | ``False``


Integer Literals
------------------------------

Integer literals are digit sequences.  They can be written in decimal, hexadecimal, or octal form.

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


Character Literals
------------------------------

A character literal consists of a quoted character.

  *CharacterLiteral*: informally,
    | a character enclosed in single quotes.

The type of a character literal is ``U8`` (see below), which corresponds to a single byte.
Syntactically, a character literal can be specified as in Haskell (see the Haskell Report), i.e.,
full Unicode and several escape sequences (such as ``\n``) are supported. However, a valid
character literal in |cogent| must always correspond to a code value in the range 0..255.

Examples for valid character literals are ``'h'``, ``'8'``, and ``'/'``. The quoted character
``'\300'`` is not a legal character literal since it is mapped to code 300.


String Literals
------------------------------

A string literal consists of a quoted character sequence.

  *StringLiteral*: informally,
    | a sequence of characters enclosed in double quotes.

Syntactically a string literal can be specified as in Haskell (see the Haskell Report). The same
escape sequences as for character literals are supported for specifying every character.
For a valid |cogent| string literal every character must be mapped to a code in the range 0..255.

An example for a valid string literal is the string ``"This is a string literal\n"``. Again,
the string ``"String containing a \300 glyph"`` is not legal, since it contains a character
mapped to code 300.
