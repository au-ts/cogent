************************************************************************
				Grammar
************************************************************************

.. todo:: jashankj: transition to something like EBNF
.. todo:: jashankj: use productionlist


Here we use a grammar notation which is similar to that used in the Java language specifications.
The meta constructs have the following meaning:

- Brackets, [], make their content optional.
- Braces, {}, make their content repeatable (and optional).

Nonterminals are denoted in *italics*.  Literal code is denoted in ``typewriter`` font.

Productions are structured by indenting the right-hand side, every single line is one alternative.
There are special forms of productions for selecting among a set of terminals and for specifying
the syntax of a nonterminal informally.

  *Program*:
    | *TopLevelUnit* { *TopLevelUnit* }

  *TopLevelUnit*:
    | *Include*
    | *Definition*

  *Include*:
    | ``include`` *StringLiteral*
    | ``include`` *SystemFile*

  *Systemfile*: informally,
    | A file pathname enclosed in ``<`` and ``>``.

  *Definition*:
    | *TypeDefinition*
    | *ValueDefinition*
    | *FunctionDefinition*
    | *AbstractDefinition*

  *TypeDefinition*:
    | ``type`` *TypeConstructor* { *TypeVariable* } ``=`` *MonoType*
    | *AbstractTypeDefinition*

  *TypeConstructor*:
    | *CapitalizedID*

  *TypeVariable*:
    | *LowercaseId*

  *AbstractTypeDefinition*:
    | ``type`` *TypeConstructor* { *TypeVariable* }

  *MonoType*:
    | *TypeA1*
    | *FunctionType*

  *FunctionType*:
    | *TypeA1* ``->`` *TypeA1*

  *TypeA1*:
    | *TypeA2*
    | *ParameterizedType*
    | *PartialRecordType*

  *ParameterizedType*:
    | *TypeConstructor* { *TypeA2* }

  *PartialRecordType*:
    | *TypeA2* *TakePut* *TakePutFields*

  *TakePut*:
    | ``take``
    | ``put``

  *TakePutFields*:
    | *FieldName*
    | ``(`` [ *FieldName* { ``,`` FieldName } ] ``)``
    | ``( .. )``

  *FieldName*:
    | *LowercaseID*

  *TypeA2*:
    | *AtomType*
    | ``#`` *AtomType*
    | *AtomType* ``!``

  *AtomType*:
    | ``(`` *MonoType* ``)``
    | *TypeConstructor*
    | *TupleType*
    | *RecordType*
    | *VariantType*
    | *TypeVariable*

  *TupleType*:
    | ``()``
    | ``(`` *MonoType* ``,`` *MonoType* { ``,`` *MonoType* } ``)``

  *RecordType*:
    | ``{`` *FieldName* ``:`` *MonoType* { ``,`` *FieldName* ``:`` *MonoType* }  ``}``

  *VariantType*:
    | ``<`` *DataConstructor* { *TypeA2* } { ``|`` *DataConstructor* { *TypeA2* } } ``>``

  *DataConstructor*:
    | *CapitalizedID*

  *ValueDefinition*:
    | *Signature* *Variable* ``=`` *Expression*

  *Signature*:
    | *Variable* ``:`` *PolyType*

  *PolyType*:
    | *MonoType*
    | ``all`` *PermSignatures* ``.`` *MonoType*

  *PermSignatures*:
    | *PermSignature*
    | ``(`` *PermSignature* { ``,`` *PermSignature* } ``)``

  *PermSignature*:
    | *TypeVariable*
    | *TypeVariable* ``:<`` Permissions

  *Permissions*:
    | *Permission* { *Permission* }

  *Permission*: one of
    | ``D``
    | ``S``
    | ``E``

  *FunctionDefinition*:
    | *Signature* *Variable* *IrrefutablePattern* ``=`` *Expression*
    | *Signature* *Variable* *Alternative* { *Alternative* }

  *AbstractDefinition*:
    | *Signature*

  *Pattern*:
    | ``(`` *Pattern* ``)``
    | *IrrefutablePattern*
    | *LiteralPattern*
    | *VariantPattern*

  *LiteralPattern*:
    | *BooleanLiteral*
    | *IntegerLiteral*
    | *CharacterLiteral*

  *IrrefutablePattern*:
    | *Variable*
    | *WildcardPattern*
    | *TuplePattern*
    | *RecordPattern*

  *WildcardPattern*:
    | ``_``

  *TuplePattern*:
    | ``()``
    | ``(`` *IrrefutablePattern* ``,`` *IrrefutablePattern* { ``,`` *IrrefutablePattern* } ``)``

  *RecordPattern*:
    | *Variable* ``{`` *RecordMatchings* ``}``
    | ``#`` ``{`` *RecordMatchings* ``}``

  *RecordMatchings*:
    | *RecordMatching* { ``,`` *RecordMatching* }

  *RecordMatching*:
    | *FieldName* [ ``=`` *IrrefutablePattern* ]

  *VariantPattern*:
    | *DataConstructor* { *IrrefutablePattern* }

  *Expression*:
    | *BasicExpression*
    | *MatchingExpression*
    | *LetExpression*
    | *ConditionalExpression*

  *BasicExpression*:
    | *BasExpr*
    | *BasExpr* ``;`` *Expression*

  *MatchingExpression*:
    | *ObservableBasicExpression* *Alternative* { *Alternative* }

  *ObservableBasicExpression*:
    | *BasicExpression*
    | *BasicExpression* { ``!`` *Variable* }

  *Alternative*:
    | ``|`` *Pattern* *PArr* *Expression*

  *PArr*: one of
    | ``->``
    | ``=>``
    | ``~>``

  *LetExpression*:
    |  ``let`` *Binding* { ``and`` *Binding* } ``in`` *Expression*

  *Binding*:
    | *IrrefutablePattern* [ ``:`` *MonoType* ] ``=`` *ObservableExpression*

  *ObservableExpression*:
    | *Expression*
    | *Expression* { ``!`` *Variable* }

  *ConditionalExpression*:
    | ``if`` *ObservableExpression* ``then`` *Expression* ``else`` *Expression*

  *BasExpr*:
    | *Term*
    | *FunctionalApplication*
    | *OperatorApplication*
    | *PutExpression*
    | *MemberAccess*

  *FunctionApplication*:
    | *BasExpr* *BasExpr*

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

  *PutExpression*:
    | *BasExpr* { *RecordAssignments* }

  *RecordAssignments*:
    | *RecordAssignments* { ``,`` *RecordAssignment* }

  *RecordAssignment*:
    | *FieldName* [ ``=`` *Expression* ]

  *MemberAccess*:
    | *BasExpr* ``.`` *FieldName*

  *Term*:
    | ``(`` Expression ``)``
    | *Variable*
    | *LiteralTerm*
    | *TupleTerm*
    | *RecordTerm*
    | *VariantTerm*
    | *LambdaTerm*
    | *PolyVariable*

  *LiteralTerm*:
    | *BooleanLiteral*
    | *IntegerLiteral*
    | *CharacterLiteral*
    | *StringLiteral*

  *BooleanLiteral*: one of
    | ``True``
    | ``False``

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

  *CharacterLiteral*: informally,
    | a character enclosed in single quotes.

  *StringLiteral*: informally,
    | a sequence of characters enclosed in double quotes.

  *TupleTerm*:
    | ``()``
    | ``(`` *Expression* ``,`` *Expression* { ``,`` *Expression* } ``)``

  *RecordTerm*:
    | ``#`` ``{`` *RecordAssignments* ``}``

  *VariantTerm*:
    | *DataConstructor* { *Term* }

  *LambdaTerm*:
    | ``\`` *IrrefutablePattern* [ ``:`` *MonoType* ] ``=>`` *Expression*

  *PolyVariable*:
    | *Variable* ``[`` *OptMonoType* { ``,`` *OptMonoType* } ``]``

  *OptMonoType*:
    | *MonoType*
    | ``_``

  *LowercaseID*: informally,
    | a sequence of letters, digits, underscore symbols, and single quotes
    | starting with a lowercase letter

  *CapitalizedID*: informally,
    | a sequence of letters, digits, underscore symbols, and single quotes
    | starting with an uppercase letter
