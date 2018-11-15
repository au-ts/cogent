{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
module Cogent.DataLayout.CodeGen where

import Cogent.C.Syntax
import Cogent.Common.Syntax (FieldName)
import Cogent.Common.Types (Sigil (..))
import Cogent.Compiler (__fixme)
import Data.Nat
import Data.List (foldl', scanl')
import Data.Map
  ( (!)
  , fromList
  , insert
  )
import Control.Lens
  ( (%=)
  , (^.)
  , at
  , (&)
  , (?=)
  , use
  )
import Cogent.C.GenState
  ( Gen
  , genType
  , freshGlobalCId
  , boxedSettersAndGetters
  , boxedRecordGetters
  , boxedRecordSetters
  , boolField
  , boolT
  )
import Cogent.Core (Type (..))
import Cogent.Compiler
  ( __impossible
  , __todo
  )
import Cogent.DataLayout.Core
  ( AlignedBitRange (..)
  , DataLayout (..)
  , alignLayout
  , wordSizeBits
  , Architecture (..)
  , architecture
  )
import Debug.Trace (trace)

type CogentType = Type 'Zero

intTypeForPointer = case architecture of
  X86_64 -> CInt False CLongT -- unsigned long
  X86_32 -> CInt False CIntT -- unsigned int

{-|
Returns a getter function C expression for a field of a boxed record.

Will generate the getter function if it has not yet been generated
(ie. checks to see if it is already recorded in the GenState)
-}
genBoxedGetField
  :: CogentType
     -- ^ Cogent type of a boxed record.

  -> FieldName
     -- ^ Name of field in the boxed record to extract.

  -> Gen v CExpr
     -- ^
     -- The 'CExpr' which is the name of the getter function
     -- for the field of the record.
     --
     -- Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     -- to call this getter function.
genBoxedGetField cogentType fieldName = do
  boxedRecordGetter <- use (boxedRecordGetters . at (cogentType, fieldName))
  case boxedRecordGetter of
    Just getFieldFunction -> return getFieldFunction
    Nothing -> do
      let TRecord fieldTypes (Boxed _ (RecordLayout fieldLayouts))
                          = cogentType
          fieldType       = fst $ (fromList fieldTypes) ! fieldName
          fieldLayout     = alignLayout $ fst $ fieldLayouts ! fieldName
      boxCType            <- genType cogentType
      getFieldFunction    <- genBoxedGetter boxCType fieldType fieldLayout ("_" ++ fieldName)
      (boxedRecordGetters . at (cogentType, fieldName)) ?= getFieldFunction
      return getFieldFunction


{-|
Returns a setter function C expression for a field of a boxed record.

Will generate the setter function if it has not yet been generated
(ie. checks to see if it is already recorded in the GenState)
-}
genBoxedSetField
  :: CogentType
     -- ^ Cogent type of a boxed record.

  -> FieldName
     -- ^ Name of field in the boxed record to put.

  -> Gen v CExpr
     -- ^
     -- The 'CExpr' which is the name of the setter function
     -- for the field of the record.
     --
     -- Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     -- to call this setter function.
genBoxedSetField cogentType fieldName = do
  boxedRecordSetter <- use (boxedRecordSetters . at (cogentType, fieldName))
  case boxedRecordSetter of
    Just setFieldFunction -> return setFieldFunction
    Nothing -> do
      let TRecord fieldTypes (Boxed _ (RecordLayout fieldLayouts))
                          = cogentType
          fieldType       = fst $ (fromList fieldTypes) ! fieldName
          fieldLayout     = alignLayout $ fst $ fieldLayouts ! fieldName
      boxCType            <- genType cogentType
      setFieldFunction    <- genBoxedSetter boxCType fieldType fieldLayout ("_" ++ fieldName)
      (boxedRecordSetters . at (cogentType, fieldName)) ?= setFieldFunction
      return setFieldFunction



{-|
Returns a getter function C expression for a part of a boxed record.

Will always generate the getter function and record it in the GenState.
-}
genBoxedGetter
  :: CType
     -- ^
     -- The CType for the root boxed type which contains
     -- the embedded value that we would like to extract.
     --
     -- It will be the alternative @CStruct CId@ where the
     -- struct has previously been defined as follows:
     --
     -- @
     -- struct `CId` {
     --   unsigned int *data;
     -- }
     -- @

  -> CogentType
     -- ^ The Cogent type of the embedded value that we would like to extract

  -> DataLayout [AlignedBitRange]
     -- ^
     -- The part of the root boxed type's DataLayout corresponding to
     -- the embedded value that we would like to extract.

  -> String
     -- ^ To append onto generated function name for improved code readability

  -> Gen v CExpr
     -- ^
     -- The 'CExpr' which is the name of the generated getter function
     -- for the field of the record.
     --
     -- Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     -- to call this getter function.


genBoxedGetter boxType embeddedType@(TCon _ _ _) (PrimLayout {bitsDL = bitRanges}) getterName =
  genComposedAlignedRangeGetter bitRanges boxType embeddedType getterName

genBoxedGetter boxType embeddedType@(TPrim _) (PrimLayout {bitsDL = bitRanges}) getterName =
  genComposedAlignedRangeGetter bitRanges boxType embeddedType getterName

genBoxedGetter boxType embeddedType@(TRecord fields (Boxed _ _)) (PrimLayout {bitsDL = bitRanges}) getterName =
  genComposedAlignedRangeGetter bitRanges boxType embeddedType getterName

genBoxedGetter boxType (TSum alternatives) (SumLayout {tagDL, alternativesDL}) getterName =
  __todo $ "Cogent.DataLayout.CodeGen: genBoxedGetter: Case for embedded variant types not yet implemented."


genBoxedGetter boxType embeddedTypeCogent@(TRecord fields Unboxed) (RecordLayout { fieldsDL }) getterName = do
  embeddedTypeC         <- genType embeddedTypeCogent
  functionName          <- (++ getterName) <$> freshGlobalCId 'g' 
  fieldNamesAndGetters  <- mapM
                            ( \(fieldName, (fieldType, _)) -> do
                                let fieldLayout = fst $ fieldsDL ! fieldName
                                getter <- genBoxedGetter boxType fieldType fieldLayout (getterName ++ "_" ++ fieldName)
                                return (fieldName, getter)
                            )
                            fields
  declareSetterOrGetter $ recordGetter fieldNamesAndGetters boxType embeddedTypeC functionName
  return (CVar functionName Nothing)

genBoxedGetter boxType (TUnit) (UnitLayout) getterName=
  __todo $ "Cogent.DataLayout.CodeGen: genBoxedGetter: Case for embedded unit value not yet implemented."

genBoxedGetter boxCType _ _ _ = __impossible $
  "Cogent.DataLayout.CodeGen: genBoxedGetter: Type checking should restrict the types which can be embedded in boxed records," ++
  "and ensure that the data layouts match the types."




{-|
Returns a setter function C expression for a part of a boxed record.

Will always generate the setter function and record it in the GenState.
-}
genBoxedSetter
  :: CType
     -- ^
     -- The CType for the root boxed type which contains
     -- the embedded value that we would like to put

  -> CogentType
     -- ^ The Cogent type of the embedded value that we would like to put

  -> DataLayout [AlignedBitRange]
     -- ^
     -- The part of the root boxed type's DataLayout corresponding to
     -- the embedded value that we would like to put.

  -> String
     -- ^ To append onto generated function name for improved code readability

  -> Gen v CExpr
     -- ^
     -- The 'CExpr' which is the name of the generated setter function
     -- for the field of the record.
     --
     -- Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     -- to call this setter function.

genBoxedSetter boxType embeddedType@(TCon _ _ _) (PrimLayout {bitsDL = bitRanges}) setterName =
  genComposedAlignedRangeSetter bitRanges boxType embeddedType setterName

genBoxedSetter boxType embeddedType@(TPrim _) (PrimLayout {bitsDL = bitRanges}) setterName =
  genComposedAlignedRangeSetter bitRanges boxType embeddedType setterName

genBoxedSetter boxType embeddedType@(TRecord fields (Boxed _ _)) (PrimLayout {bitsDL = bitRanges}) setterName =
  genComposedAlignedRangeSetter bitRanges boxType embeddedType setterName

genBoxedSetter boxType (TSum alternatives) (SumLayout {tagDL, alternativesDL}) setterName =
  __todo $ "Cogent.DataLayout.CodeGen: genBoxedSetter: Case for embedded variant types not yet implemented."


genBoxedSetter boxType embeddedTypeCogent@(TRecord fields Unboxed) (RecordLayout { fieldsDL }) setterName = do
  embeddedTypeC         <- genType embeddedTypeCogent
  functionName          <- (++ setterName) <$> freshGlobalCId 's'
  fieldNamesAndSetters  <- mapM
                            ( \(fieldName, (fieldType, _)) -> do
                                let fieldLayout = fst $ fieldsDL ! fieldName
                                setter <- genBoxedSetter boxType fieldType fieldLayout (setterName ++ "_" ++ fieldName)
                                return (fieldName, setter)
                            )
                            fields
  declareSetterOrGetter $ recordSetter fieldNamesAndSetters boxType embeddedTypeC functionName
  return (CVar functionName Nothing)


genBoxedSetter boxType (TUnit) (UnitLayout) setterName =
  __todo $ "Cogent.DataLayout.CodeGen: genBoxedSetter: Case for embedded unit value not yet implemented."

genBoxedSetter boxCType _ _ _ = __impossible $
  "Cogent.DataLayout.CodeGen: genBoxedSetter: Type checking should restrict the types which can be embedded in boxed records," ++
  "and ensure that the data layouts match the types."





{-|
Calling
@variantGetter [(field1, field1Getter), ...] boxType embeddedType recordGetter@ will return
the C Syntax for the following function.
@
static inline embeddedType variantGetter(boxType p) {
  return
    (tagGetter(p) == boxedTagValue1)
    ? (embeddedType)
        { .tag = 0
        , .alt1 = alt1Getter(p);
        }
    : (tagGetter(p) == boxedTagValue2)
      ? (embeddedType)
          { .tag = 1
          , .alt2 = alt2Getter(p);
          }
      : ...
              : (embeddedType) {} // Impossible to reach here
}
@
-}
variantGetter
  :: [(CId, Int, Int, CExpr)]
      -- ^
      -- ( Name of the alternative of the variant,
      -- , Tag number for this alternative in the boxed structure
      -- , Tag number for this alternative in the unboxed structure
      -- , Expression for the getter function which will extract that field from the boxed data
      -- )
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter function
  -> CExtDecl
      -- ^ The C syntax tree for a function which extracts the embedded data from the box.

variantGetter fields boxType embeddedType functionName = __todo "Cogent.DataLayout.CodeGen: variantGetter: unimplemented."
{-
  ( CFnDefn
  
    -- (return type, function name)
    ( embeddedType, functionName )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier ) ]
    
    -- statements
    [ CBIStmt $ CReturn $ Just $ CCompLit embeddedType $
        fmap
        (\(fieldName, fieldGetter) -> ([CDesignFld fieldName], CInitE $ CEFnCall fieldGetter [boxVariable]))
        fields
    ]
  
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing
-}

{-|
Calling
@variantSetter [(field1, field1Setter), ...] boxType embeddedType recordSetter@ will return
the C Syntax for the following function.
@
static inline void variantSetter(boxType p, embeddedType v) {
  if (v.tag == 0) {
    tagSetter(p, alt0TagValue);
    alt0Setter(p, v.alt0);
  } else if (v.tag == 1) {
    tagSetter(p, alt1TagValue);
    alt1Setter(p, v.alt1);
  } else if
    ...
  }
}
@
-}
variantSetter
  :: [(CId, CExpr)]
      -- ^
      -- ( Name of the field in the struct for the embedded data
      -- , Expression for the setter function which will extract that field from the boxed data
      -- )
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter function
  -> CExtDecl
      -- ^ The C syntax tree for a function which extracts the embedded data from the box.

variantSetter fields boxType embeddedType functionName = __todo "Cogent.DataLayout.CodeGen: variantSetter: unimplemented."
{-
  ( CFnDefn
  
    -- (return type, function name)
    ( CVoid, functionName )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier ) 
    , ( embeddedType, valueIdentifier )
    ]
    
    -- statements
    ( fmap
      (\(fieldName, fieldGetter) ->
        CBIStmt $ CAssignFnCall Nothing fieldGetter [boxVariable, CStructDot valueVariable fieldName])
      fields
    )
  
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing

    valueIdentifier = "v"
    valueVariable   = CVar valueIdentifier Nothing
-}



{-|
Calling
@recordGetter [(field1, field1Getter), ...] boxType embeddedType recordGetter@ will return
the C Syntax for the following function.
@
static inline embeddedType recordGetter(boxType p) {
  return (embeddedType)
    { .field1 = field1Getter(p)
    , .field2 = field2Getter(p)
    , ...
    };
}
@

-}
recordGetter
  :: [(CId, CExpr)]
      -- ^
      -- ( Name of the field in the struct for the embedded data
      -- , Expression for the getter function which will extract that field from the boxed data
      -- )
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter function
  -> CExtDecl
      -- ^ The C syntax tree for a function which extracts the embedded data from the box.

recordGetter fields boxType embeddedType functionName =
  ( CFnDefn
  
    -- (return type, function name)
    ( embeddedType, functionName )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier ) ]
    
    -- statements
    [ CBIStmt $ CReturn $ Just $ CCompLit embeddedType $
        fmap
        (\(fieldName, fieldGetter) -> ([CDesignFld fieldName], CInitE $ CEFnCall fieldGetter [boxVariable]))
        fields
    ]
  
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing

{-|
Calling
@recordSetter [(field1, field1Setter), ...] boxType embeddedType recordSetter@ will return
the C Syntax for the following function.
@
static inline void recordSetter(boxType p, embeddedType v) {
  field1Setter(p, v.field1);
  field2Setter(p, v.field2);
  ...
}
@
-}
recordSetter
  :: [(CId, CExpr)]
      -- ^
      -- ( Name of the field in the struct for the embedded data
      -- , Expression for the setter function which will extract that field from the boxed data
      -- )
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter function
  -> CExtDecl
      -- ^ The C syntax tree for a function which extracts the embedded data from the box.

recordSetter fields boxType embeddedType functionName =
  ( CFnDefn
  
    -- (return type, function name)
    ( CVoid, functionName )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier ) 
    , ( embeddedType, valueIdentifier )
    ]
    
    -- statements
    ( fmap
      (\(fieldName, fieldGetter) ->
        CBIStmt $ CAssignFnCall Nothing fieldGetter [boxVariable, CStructDot valueVariable fieldName])
      fields
    )
  
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing

    valueIdentifier = "v"
    valueVariable   = CVar valueIdentifier Nothing

    


{-|
Declares in the Gen state a C function which gets the contents
of a list of aligned bitranges out of a boxed value and
concatenates the retrieved values to produce a value of the
given embedded value type.

Calls the function `composedAlignedRangeSetter` to generate the function.
-}
genComposedAlignedRangeGetter :: [AlignedBitRange] -> CType -> CogentType -> String -> Gen v CExpr
genComposedAlignedRangeGetter bitRanges boxType embeddedTypeCogent getterName = do
  embeddedTypeC   <- genType embeddedTypeCogent
  functionName    <- (++ getterName) <$> freshGlobalCId 'g'
  rangesGetters   <- mapM (genAlignedRangeGetter boxType getterName) bitRanges
  declareSetterOrGetter $
    composedAlignedRangeGetter (zip bitRanges rangesGetters) boxType embeddedTypeC functionName
  return (CVar functionName Nothing)



{-|
Declares in the Gen state a C function which sets the contents of
a list of aligned bitranges in a boxed value from the pieces of a
value of the given embedded value type.

Calls the function `composedAlignedRangeSetter` to generate the function.
-}
genComposedAlignedRangeSetter :: [AlignedBitRange] -> CType -> CogentType -> String -> Gen v CExpr
genComposedAlignedRangeSetter bitRanges boxType embeddedTypeCogent setterName = do
  embeddedTypeC   <- genType embeddedTypeCogent
  functionName    <- (++ setterName) <$> freshGlobalCId 's'
  rangesSetters   <- mapM (genAlignedRangeSetter boxType setterName) bitRanges
  declareSetterOrGetter $
    composedAlignedRangeSetter (zip bitRanges rangesSetters) boxType embeddedTypeC functionName
  return (CVar functionName Nothing)


{-|
Creates a C function which gets the contents of a list of aligned bitranges
out of a boxed value and concatenates the retrieved values
to produce a value of the given embedded value type.

@composedAlignedRangeGetter
  ((firstBitSize, firstGeterFunction) : bitRanges)
  boxType
  embeddedType
  functionName@
will return the C syntax for the C function

@
static inline `embeddedType` `functionName`(`boxType` p) {
  return (`embeddedType`) (
    (((`embeddedIntType`)`getBR0Identifier`(p)) << `0`) |
    (((`embeddedIntType`)`getBR1Identifier`(p)) << `0 + firstBitSize`) |
    (((`embeddedIntType`)`getBR2Identifier`(p)) << `0 + firstBitSize + secondBitSize`) |
    ...);
}
@
-}
composedAlignedRangeGetter
  :: [(AlignedBitRange, CExpr)]
      -- ^
      -- The bit ranges and the 'CExpr' which is
      -- the name of the getter function for the corresponding
      -- bit range.
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter function
  -> CExtDecl
      -- ^ The C syntax tree for a function which extracts the embedded data from the box.

composedAlignedRangeGetter
  ((firstRange, firstGetterFunction) : bitRanges)
  boxType
  embeddedType
  functionName
  =
  ( CFnDefn
  
    -- (return type, function name)
    ( embeddedType, functionName )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier ) ]
    
    -- statements
    [ CBIStmt $ CReturn $ Just $ fromIntValue embeddedType $ snd $ foldl'
      (\ (accumulatedBitOffset, accumulatedExpr) (range, rangeGetterFunction) ->
        ( accumulatedBitOffset + bitSizeABR range
        , CBinOp Or accumulatedExpr
            ( genGetAlignedRangeAtBitOffset rangeGetterFunction accumulatedBitOffset )
        )
      )
      (bitSizeABR firstRange, genGetAlignedRangeAtBitOffset firstGetterFunction 0)
      bitRanges
    ]
  
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing

    {-
    @genGetAlignedRangeAtBitOffset getRangeFunction offset@ will return the 'CExpr'

    @
      ((`embeddedType`) `getRangeFunction`(b)) << `offset`
    @
    -}
    genGetAlignedRangeAtBitOffset :: CExpr -> Integer -> CExpr
    genGetAlignedRangeAtBitOffset getRangeFunction offset =
      CBinOp Lsh
        ( CTypeCast (intTypeForType embeddedType) (CEFnCall getRangeFunction [boxVariable]) )
        ( unsignedIntLiteral offset )

composedAlignedRangeGetter _ _ _ _ = __impossible $
  "genComposedAlignedRangeGetter should never be called on an empty list of ranges!"




{-|
Creates a C function which sets the contents of a list of aligned bitranges
in a boxed value from the pieces of a value of the given embedded value type.

@composedAlignedRangeSetter
  bitRanges
  boxType
  embeddedType
  functionName@
will return the C syntax for the C function

@
static inline void `functionName`(`boxType` b, `embeddedType` v) {
  `setBR0Identifier`(b, (v >> `0`) & `bitSize0`);
  `setBR1Identifier`(b, (v >> `0 + bitSize0`) & `bitSize1`);
  `setBR2Identifier`(b, (v >> `0 + bitSize0 + bitSize1`) & `bitSize2`);
  ...
}
@
-}
composedAlignedRangeSetter
  :: [(AlignedBitRange, CExpr)]
      -- ^
      -- The bit ranges and the 'CExpr' which is
      -- the name of the getter function for the corresponding
      -- bit range.
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated setter function
  -> CExtDecl
      -- ^ The C syntax tree for a function which puts the data into the box.

composedAlignedRangeSetter
  bitRanges
  boxType
  embeddedType
  functionName
  =
  ( CFnDefn
  
    -- (return type, function name)
    ( CVoid, functionName )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier )
    , ( embeddedType, valueIdentifier )
    ]
    
    -- statements
    ( fmap
      (\((bitRange, setRangeFunction), offset) ->
          CBIStmt (genSetAlignedRangeAtBitOffset setRangeFunction offset (bitSizeABR bitRange))
      )
      $ zip bitRanges
      $ scanl' (+) 0
      $ fmap (bitSizeABR . fst) bitRanges
    )
  
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing

    valueIdentifier = "v"
    valueVariable   = CVar valueIdentifier Nothing

    -- If embeddedType is a boxed type, we cast valueVariable to the integer type of the correct size
    -- If it is a boolean type, we extract the boolean value
    valueExpression = toIntValue embeddedType valueVariable

    {-
    @genSetAlignedRangeAtBitOffset setRangeFunction offset size@ will return the 'CExpr'

    @
      `setRangeFunction`(b, (unsigned int) ((v >> `offset`) & `size`))
    @
    -}
    genSetAlignedRangeAtBitOffset :: CExpr -> Integer -> Integer -> CStmt
    genSetAlignedRangeAtBitOffset setRangeFunction offset size =
      CAssignFnCall Nothing setRangeFunction
        [ boxVariable
        , CTypeCast
            unsignedIntType
            ( CBinOp And
              ( CBinOp Rsh valueExpression (unsignedIntLiteral offset) )
              ( unsignedIntLiteral (sizeToMask size) )
            )
        ]

{-|
Declares in the Gen state a C function to extract the contents of an
AlignedBitRange from a Cogent boxed type.

Calls the function `alignedRangeGetter` to generate the function.
-}
genAlignedRangeGetter :: CType -> String -> AlignedBitRange -> Gen v CExpr
genAlignedRangeGetter boxType getterName bitRange = do
  functionIdentifier <- (++ getterName) <$> freshGlobalCId 'g'
  declareSetterOrGetter $
    alignedRangeGetter boxType bitRange functionIdentifier
  return (CVar functionIdentifier Nothing)



{-|
Declares in the Gen state a C function to set the contents of an
AlignedBitRange in a Cogent boxed type.

Calls the function `alignedRangeSetter` to generate the function.
-}
genAlignedRangeSetter :: CType -> String -> AlignedBitRange -> Gen v CExpr
genAlignedRangeSetter boxType setterName bitRange = do
  functionIdentifier <- (++ setterName) <$> freshGlobalCId 's'
  declareSetterOrGetter $
    alignedRangeSetter boxType bitRange functionIdentifier
  return (CVar functionIdentifier Nothing)


{-|
Creates a C function to extract the contents of an
AlignedBitRange from a Cogent boxed type.
     
@alignedRangeGetter boxType AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR} functionNameIdentifier@
should be the C function

@
static inline unsigned int get`functionNameIdentifier`(`boxType` p) {
  return (p.data[`wordOffsetABR`] >> `bitOffsetABR`) & `mask bitSizeABR`;
}
@
-}
alignedRangeGetter :: CType -> AlignedBitRange -> CId -> CExtDecl
alignedRangeGetter
  boxType
  AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR }
  functionIdentifier
  =
  ( CFnDefn
  
    -- (return type, function name)
    ( unsignedIntType, functionIdentifier )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier ) ]
    
    -- statements
    [ CBIStmt $ CReturn $ Just
      ( CBinOp And
        ( CBinOp Rsh ( genBoxWordExpr boxVariable wordOffsetABR ) bitOffsetLiteral )
        maskLiteral
      )
    ]
  
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing
  
    bitOffsetLiteral  = unsignedIntLiteral bitOffsetABR
    maskLiteral       = unsignedIntMask $ sizeToMask bitSizeABR


{-|
Creates a C function to set the contents of an
AlignedBitRange in a Cogent boxed type.

@alignedRangeSetter boxType AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR} functionNameIdentifier@
should be the C function

@
static inline void set`functionNameIdentifier`(`boxType` p, unsigned int v) {
  p.data[`wordOffsetABR`]
    = p.data[`wordOffsetABR`]

    // clear the bits
    & ~(`sizeToMask bitSizeABR` << `bitOffsetABR`)) 
    
    // set the bits
    | ((`sizeToMask bitSizeABR` & v) << `bitOffsetABR`);
}
@
-}
alignedRangeSetter :: CType -> AlignedBitRange -> CId -> CExtDecl
alignedRangeSetter
  boxType
  AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR }
  functionNameIdentifier
  =
  ( CFnDefn
  
    -- (return type, function name)
    ( CVoid, functionNameIdentifier )
    
    -- [(param type, param name)]
    [ ( boxType, boxIdentifier )
    , ( unsignedIntType, valueIdentifier )
    ]
    
    -- statements
    [ CBIStmt
      ( CAssign
        ( genBoxWordExpr boxVariable wordOffsetABR )
        ( CBinOp Or
          ( CBinOp And
            ( genBoxWordExpr boxVariable wordOffsetABR )
            ( CUnOp Not ( CBinOp Lsh maskLiteral bitOffsetLiteral ) )
          )
          ( CBinOp Lsh
            ( CBinOp And maskLiteral valueVariable )
            bitOffsetLiteral
          )
        )
      )
    ]
    
    staticInlineFnSpec
  )
  where
    boxIdentifier = "b"
    boxVariable   = CVar boxIdentifier Nothing
    
    valueIdentifier = "v"
    valueVariable   = CVar valueIdentifier Nothing
    
    bitOffsetLiteral  = unsignedIntLiteral bitOffsetABR
    maskLiteral       = unsignedIntMask $ sizeToMask bitSizeABR
    
sizeToMask :: Integer -> Integer
sizeToMask n
  | 0 <= n && n <= wordSizeBits = 2^n - 1
  | otherwise = __impossible $ "DataLayout.CodeGen: sizeToMask " ++ show n ++ ": n not in range [0, " ++ show wordSizeBits ++ "] after alignment"


{-|
Saves the given setter or getter function
C syntax tree into the Gen state.
-}
declareSetterOrGetter :: CExtDecl -> Gen v ()
declareSetterOrGetter function = boxedSettersAndGetters %= (function :)


{-|
@genBoxWordExpr boxExpr wordOffset@
returns syntax for the 'CExpr'
@
`boxExpr`.data[`wordOffset`]
@
-}
genBoxWordExpr :: CExpr -> Integer -> CExpr
genBoxWordExpr boxExpr wordOffset =
  CArrayDeref (CStructDot boxExpr boxFieldName) (unsignedIntLiteral wordOffset)
  -- ALTERNATELY: CDeref ( CBinOp Add (CStructDot boxExpr "data") (unsignedIntLiteral wordOffset))

boxFieldName :: CId
boxFieldName = "data"

-- | Produces a C expression for an unsigned integer literal with the given integer value.
unsignedIntLiteral :: Integer -> CExpr
unsignedIntLiteral n = CConst $ CNumConst n unsignedIntType DEC

unsignedIntMask :: Integer -> CExpr
unsignedIntMask n = CConst $ CNumConst n unsignedIntType (__fixme DEC) {- TODO: Change DEC to BIN. Requires implementing this in cLitConst function of Render.hs -}

unsignedIntType = CInt False CIntT


toIntValue :: CType -> CExpr -> CExpr
toIntValue (CIdent t) cexpr
  | t == boolT                            = CStructDot cexpr boolField
  | t `elem` ["u8", "u16", "u32", "u64"]  = cexpr
toIntValue (CPtr _)   cexpr               = CTypeCast intTypeForPointer cexpr
toIntValue _          cexpr               = CTypeCast intTypeForPointer (CStructDot cexpr boxFieldName)

fromIntValue :: CType -> CExpr -> CExpr
fromIntValue (CIdent t)     cexpr
  | t == boolT                            = CCompLit (CIdent boolT) [([CDesignFld boolField], CInitE cexpr)]
  | t `elem` ["u8", "u16", "u32", "u64"]  = cexpr
fromIntValue ctype@(CPtr _) cexpr         = CTypeCast ctype cexpr
fromIntValue ctype          cexpr         = CCompLit ctype [([CDesignFld boxFieldName], CInitE (CTypeCast (CPtr unsignedIntType) cexpr))]

{-
Given the CType of an embedded value (leaf of composite type tree) to extract,
returns the corresponding integer type it should be extracted as before casting.
-}
intTypeForType :: CType -> CType
intTypeForType (CIdent t)
  | t == boolT                            = CInt False CCharT -- embedded boolean
  | t `elem` ["u8", "u16", "u32", "u64"]  = CIdent t
intTypeForType (CPtr _)                   = intTypeForPointer -- embedded boxed abstract type
intTypeForType _                          = intTypeForPointer -- embedded boxed record



