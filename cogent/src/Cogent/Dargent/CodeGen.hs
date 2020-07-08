--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}

module Cogent.Dargent.CodeGen where

import Cogent.C.Monad
import Cogent.C.Type (genType, typeCId, simplifyType)
import Cogent.C.Syntax
import Cogent.Common.Syntax (FieldName, FunName, VarName, Size)
import Cogent.Common.Types (Sigil (..))
import Cogent.Compiler
  ( __fixme
  , __impossible
  , __todo
  , __assert_
  , Architecture (..)
  , __cogent_arch
  )
import Cogent.Core (Type (..))
import Cogent.Dargent.Allocation
import Cogent.Dargent.Surface (Endianness(..))
import Cogent.Dargent.Core
  ( DataLayout' (..)
  , DataLayout (..)
  , alignLayout'
  , alignLayoutToBytes'
  , dataLayoutSizeInBytes'
  )
import Cogent.Dargent.Util
import Data.Nat
import qualified Data.OMap as OMap
import Data.Char

import Control.Monad.Writer.Class (tell)
import Data.List (foldl', scanl')
import Data.Map
  ( (!)
  , fromList
  , insert
  )
import Lens.Micro
  ( (^.)
  , at
  , (&)
  )
import Lens.Micro.GHC  -- orphan instances for 'Micro.Lens.at'
import Lens.Micro.Mtl
  ( (%=)
  , (?=)
  , use
  )
import Debug.Trace

-- * Getter/setter generation

{-|
Returns a getter/setter function C expression for a field of a boxed record.

Will generate the getter/setter function if it has not yet been generated
(ie. checks to see if it is already recorded in the GenState)
-}
genBoxedGetSetField
  :: CogentType
     -- ^ Cogent type of a boxed record.

  -> FieldName
     -- ^ Name of field in the boxed record to extract.

  -> GetOrSet
     -- ^ The type of function to generate

  -> Gen v FunName
     -- ^
     -- The 'FunName' which is the name of the getter/setter function
     -- for the field of the record.

genBoxedGetSetField cogentType fieldName getOrSet = do
  boxedRecordGetterSetter    <- use ((case getOrSet of Get -> boxedRecordGetters; Set -> boxedRecordSetters) . at (StrlCogentType cogentType, fieldName))
  case boxedRecordGetterSetter of
    Just getSetFieldFunction -> return getSetFieldFunction
    Nothing                  ->
      case cogentType of
        TRecord _ fieldTypes (Boxed _ (Layout (RecordLayout fieldLayouts))) ->
          do
            let fieldType       = fst $ (fromList fieldTypes) ! fieldName
                fieldLayout     = alignLayout' $ fieldLayouts ! fieldName
            boxCType            <- genType cogentType
            cid                 <- typeCId cogentType
            getSetFieldFunction <- genBoxedGetterSetter True boxCType fieldType fieldLayout [fieldName] getOrSet
            ((case getOrSet of Get -> boxedRecordGetters; Set -> boxedRecordSetters) . at (StrlCogentType cogentType, fieldName))
                                ?= getSetFieldFunction
            let updGS Get f (Nothing, s) = (Just f, s)
                updGS Get f (Just g , s) = __assert_ (f == g) "genBoxedGetSetField: different getter for the same field" (Just g, s)
                updGS Set f (g, Nothing) = (g, Just f)
                updGS Set f (g, Just s ) = __assert_ (f == s) "genBoxedGetSetField: different setter for the same field" (g, Just s)
                updSort (SRecord ss (Just as)) =
                  SRecord ss $ Just $ OMap.adjust (updGS getOrSet getSetFieldFunction) fieldName as  -- it only updates the functions
            typeCorres' %= (OMap.adjust updSort cid)
            return getSetFieldFunction
        TRecord _ fieldTypes (Boxed _ CLayout) ->
          error "genBoxedGetSetField: tried to gen a getter/setter for a c-type"


{-|
Returns a getter/setter function C expression for a part of a boxed record.

Will always generate the getter/setter function and record it in the GenState.
-}
genBoxedGetterSetter
  :: IsStruct
     -- ^ Whether the c-type of the box is of struct or of byte-array

  -> CType
     -- ^
     -- The CType for the root boxed type which contains
     -- the embedded value that we would like to extract.

  -> CogentType
     -- ^ The Cogent type of the embedded value that we would like to extract

  -> DataLayout' [AlignedBitRange]
     -- ^
     -- The part of the root boxed type's DataLayout corresponding to
     -- the embedded value that we would like to extract.

  -> [String]
     -- ^ Path in structure to value being get or set, to create readable function name

  -> GetOrSet
     -- ^ Whether to generate a getter or a setter

  -> Gen v FunName
     -- ^
     -- The 'FunName' is the name of the generated getter function
     -- for the field of the record.

genBoxedGetterSetter isStruct boxType embeddedType@(TCon _ _ _) PrimLayout{bitsDL = bitRanges, endianness = e} path getOrSet =
  genComposedAlignedRangeGetterSetter isStruct bitRanges e boxType embeddedType path getOrSet

genBoxedGetterSetter isStruct boxType embeddedType@(TPrim _) PrimLayout{bitsDL = bitRanges, endianness = e} path getOrSet =
  genComposedAlignedRangeGetterSetter isStruct bitRanges e boxType embeddedType path getOrSet

genBoxedGetterSetter isStruct boxType embeddedType@(TRecord _ fields Boxed{}) PrimLayout{bitsDL = bitRanges, endianness = e} path getOrSet =
  genComposedAlignedRangeGetterSetter isStruct bitRanges e boxType embeddedType path getOrSet

genBoxedGetterSetter isStruct boxType embeddedTypeCogent@(TSum alternatives) SumLayout{tagDL, alternativesDL} path getOrSet = do
  embeddedTypeC               <- genType embeddedTypeCogent
  functionName                <- genGetterSetterName path getOrSet
  tagGetterSetter             <- genComposedAlignedRangeGetterSetter' isStruct tagDL ME boxType unsignedIntType (path ++ ["tag"]) getOrSet -- Must add check to restrict number of alternatives to MAX_INT)
  alternativesGettersSetters  <-
      mapM
      (\(alternativeName, (alternativeType, _)) -> do
          let (boxedTagValue, alternativeLayout) = alternativesDL ! alternativeName
          getterSetter <- genBoxedGetterSetter isStruct boxType alternativeType alternativeLayout (path ++ [alternativeName]) getOrSet
          return (alternativeName, boxedTagValue, getterSetter)
      )
      alternatives
  declareSetterOrGetter $ variantGetterSetter tagGetterSetter alternativesGettersSetters boxType embeddedTypeC functionName getOrSet
  return functionName

genBoxedGetterSetter isStruct boxType embeddedTypeCogent@(TRecord _ fields Unboxed) RecordLayout{ fieldsDL } path getOrSet = do
  embeddedTypeC         <- genType embeddedTypeCogent
  functionName          <- genGetterSetterName path getOrSet
  fieldGettersSetters   <-
    mapM
      (\(fieldName, (fieldType, _)) -> do
          let fieldLayout = fieldsDL ! fieldName
          getterSetter <- genBoxedGetterSetter isStruct boxType fieldType fieldLayout (path ++ [fieldName]) getOrSet
          return (fieldName, getterSetter)
      )
      fields
  declareSetterOrGetter $ recordGetterSetter fieldGettersSetters boxType embeddedTypeC functionName getOrSet
  return functionName

genBoxedGetterSetter isStruct boxType TUnit UnitLayout path getOrSet = do
  functionName  <- genGetterSetterName path getOrSet
  declareSetterOrGetter $ unitGetterSetter boxType functionName getOrSet
  return functionName

#ifdef BUILTIN_ARRAYS
genBoxedGetterSetter isStruct box tau@(TArray t l (Boxed {}) _) PrimLayout{bitsDL = ranges, endianness = e} path getOrSet =
  genComposedAlignedRangeGetterSetter isStruct ranges e box tau path getOrSet
#endif

genBoxedGetterSetter isStruct boxType tau range _ _ = do
  traceM $ show tau ++ ", " ++ show range
  __impossible $ "Cogent.Dargent.CodeGen: genBoxedGetterSetter: Type checking should restrict the types which can be embedded in boxed records, and ensure that the data layouts match the types."


#ifdef BUILTIN_ARRAYS
{-|
Returns a getter/setter function C expression for a part of a boxed array.

We want all layout definition aligned to bytes and we don't want padding bytes between elements,
thus we use bytearray here.
-}
genBoxedArrayGetSet
  :: CogentType
     -- ^
     -- CogentType for the array.
  -> GetOrSet
     -- ^
     -- The type of function to generate.
  -> Gen v FunName
     -- ^
     -- The 'FunName' is the name of the getter/setter function
     -- for the field of the record.

genBoxedArrayGetSet cogentType getOrSet = do
  mf <- use ((case getOrSet of Get -> boxedArrayGetters; Set -> boxedArraySetters) . at cogentType)
  case mf of
    Just f  -> return f
    Nothing ->
      case cogentType of
        -- NOTE: do we need to check layout within elt here?
        TArray elemType _ (Boxed _ (Layout (ArrayLayout elemLayout))) _ -> do
          let elemSize = dataLayoutSizeInBytes' elemLayout
              elemLayout' = alignLayoutToBytes' elemLayout
              -- we get rid of unused info here, e.g. array length, hole location
          f' <- genArrayGetterSetter cogentType elemType elemSize elemLayout' getOrSet
          ((case getOrSet of Get -> boxedArrayGetters; Set -> boxedArraySetters) . at (simplifyType cogentType))
            ?= f'
          return f'
        _ -> __impossible $
          "Cogent.Dargent.CodeGen: genBoxedArrayGetSet: this function should only be called with boxed array with boxed types " ++
          "with layout provided, check caller."

genArrayGetterSetter
  :: CogentType
  -> CogentType
  -> Size
  -> DataLayout' [AlignedBitRange]
  -> GetOrSet
  -> Gen v FunName
genArrayGetterSetter arrType elemType elemSize elemLayout' getOrSet = do
  functionIdentifier <- genGetterSetterName [] getOrSet
  arrCType <- genType arrType
  elemCType <- genType elemType
  elemGetterSetter <- genBoxedGetterSetter False (CPtr unsignedCharType) elemType elemLayout' [] getOrSet
  ((case getOrSet of Get -> boxedArrayElemGetters; Set -> boxedArrayElemSetters) . at (simplifyType arrType))
    ?= elemGetterSetter
  declareSetterOrGetter $ arrayGetterSetter arrCType elemCType elemSize functionIdentifier elemGetterSetter getOrSet
  return functionIdentifier
#endif

{-|
Declares in the Gen state a C function which gets/sets the contents
of a list of aligned bitranges in a boxed value which concatenate to
a value of the given embedded type.

Calls the function `composedAlignedRangeGetterSetter` to generate the function.
-}
genComposedAlignedRangeGetterSetter :: IsStruct -> [AlignedBitRange] -> Endianness -> CType -> CogentType -> [String] -> GetOrSet -> Gen v FunName
genComposedAlignedRangeGetterSetter isStruct bitRanges endianness boxType embeddedTypeCogent path getOrSet = do
  embeddedTypeC   <- genType embeddedTypeCogent
  genComposedAlignedRangeGetterSetter' isStruct bitRanges endianness boxType embeddedTypeC path getOrSet

genComposedAlignedRangeGetterSetter' :: IsStruct -> [AlignedBitRange] -> Endianness -> CType -> CType -> [String] -> GetOrSet -> Gen v FunName
genComposedAlignedRangeGetterSetter' isStruct bitRanges endianness boxType embeddedTypeC path getOrSet = do
  functionName    <- genGetterSetterName path getOrSet
  rangesGetters   <- mapM (\(range, index) -> genAlignedRangeGetterSetter isStruct boxType (path ++ ["part" ++ show index]) getOrSet range) (zip bitRanges [0..])
  declareSetterOrGetter $ composedAlignedRangeGetterSetter (zip bitRanges rangesGetters) endianness boxType embeddedTypeC functionName getOrSet
  return functionName


{-|
Declares in the Gen state a C function to extract/set the contents of an
AlignedBitRange from/in a Cogent boxed type.

Calls the function `alignedRangeGetterSetter` to generate the function.
-}
genAlignedRangeGetterSetter :: IsStruct -> CType -> [String] -> GetOrSet -> AlignedBitRange -> Gen v FunName
genAlignedRangeGetterSetter isStruct boxType path getOrSet bitRange = do
  functionIdentifier <- genGetterSetterName path getOrSet
  declareSetterOrGetter $ alignedRangeGetterSetter isStruct boxType bitRange functionIdentifier getOrSet
  return functionIdentifier

{-|
Generates a unique function name for the getter or setter which is also readable.
-}
genGetterSetterName
  :: [String]   -- ^ Path in structure to value being get or set
  -> GetOrSet   -- ^ Whether to generate a getter or setter function
  -> Gen v CId  -- ^ The CId for the function, which is guaranteed to be unique
genGetterSetterName path getOrSet =
  let pathString      = concatMap ('_' :) path
      getOrSetString  = (case getOrSet of Get -> "_get" ; Set -> "_set")
  in  (++ (getOrSetString ++ pathString)) <$> freshGlobalCId 'd'


-- * Getter/setter function declarations

{-|
Calling
@variantGetterSetter [(alt1, alt1TagValue, alt1Getter), ...] boxType embeddedType recordGetter Get@ will return
the C Syntax for the following function.

@
static inline embeddedType variantGetter(boxType p) {
  return
    (tagGetter(p) == alt1TagValue)
    ? (embeddedType)
        { .tag = TAG_ENUM_`alt1`
        , .alt1 = alt1Getter(p);
        }
    : (tagGetter(p) == alt2TagValue)
      ? (embeddedType)
          { .tag = TAG_ENUM_`alt2`
          , .alt2 = alt2Getter(p);
          }
      : ...
}
@

Calling
@variantGetterSetter [(alt0, alt0TagValue, alt0Setter), ...] boxType embeddedType recordSetter Set@ will return
the C Syntax for the following function.

@
static inline void variantSetter(boxType p, embeddedType v) {
  if (v.tag == TAG_ENUM_`alt0`) {
    tagSetter(p, alt0TagValue);
    alt0Setter(p, v.alt0);
  } else if (v.tag == TAG_ENUM_`alt1`) {
    tagSetter(p, alt1TagValue);
    alt1Setter(p, v.alt1);
  } else if
    ...
  }
}
@
-}
variantGetterSetter
  :: FunName  -- Name of the setter/getter function for the tag
  -> [(CId, Integer, FunName)]
      -- ^
      -- ( Name of the alternative of the variant,
      -- , Tag value for this alternative in the boxed structure
      -- , Name of the getter/setter function for the alternative
      -- )
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter function
  -> GetOrSet
      -- ^ Whether to generate a getter or setter
  -> CExtDecl
      -- ^ The C syntax tree for a function which extracts the embedded data from the box.

variantGetterSetter tagGetterSetter ((firstAltName, firstTagValue, firstAltGetterSetter) : otherAlts) boxType embeddedType functionName getOrSet =
  getterSetterDecl boxType embeddedType functionName getOrSet
    -- Get statements
    [ CBIStmt $ CReturn $ Just $
        foldl'
          (\accumExpr (altName, tagValue, altGetter) ->
              CCondExpr
                (CBinOp
                  Eq
                  (CEFnCall (variable tagGetterSetter) [boxVariable])
                  (CConst $ CNumConst tagValue unsignedIntType DEC))
                (getUnboxedAlt altName altGetter)
                accumExpr
          )
          (getUnboxedAlt firstAltName firstAltGetterSetter)
          otherAlts
    ]

    -- Set statements
    (if otherAlts == []
      then (setUnboxedAlt firstAltName firstTagValue firstAltGetterSetter)
      else
        [CBIStmt $ foldl'
          (\accumBlockItems (altName, tagValue, altGetter) ->
            CIfStmt
              (CBinOp
                Eq
                (CStructDot valueVariable fieldTag)
                (variable $ tagEnum altName))
              (CBlock $ setUnboxedAlt altName tagValue altGetter)
              accumBlockItems
          )
          (CBlock $ setUnboxedAlt firstAltName firstTagValue firstAltGetterSetter)
          otherAlts
        ]
    )
  where
    getUnboxedAlt :: CId -> FunName -> CExpr
    getUnboxedAlt altName altGetter =
      CCompLit embeddedType
      [ ([CDesignFld fieldTag], CInitE $ variable (tagEnum altName))
      , ([CDesignFld altName] , CInitE $ CEFnCall (variable altGetter) [boxVariable])
      ]

    setUnboxedAlt :: CId -> Integer -> FunName -> [CBlockItem]
    setUnboxedAlt altName tagValue altSetter = fmap CBIStmt
      [ CAssignFnCall Nothing (variable tagGetterSetter) [boxVariable, CConst $ CNumConst tagValue unsignedIntType DEC]
      , CAssignFnCall Nothing (variable altSetter)       [boxVariable, CStructDot valueVariable altName]
      ]



{-|
Calling
@recordGetterSetter [(field1, field1Getter), ...] boxType embeddedType recordGetter Get@ will return
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

Calling
@recordGetterSetter [(field1, field1Setter), ...] boxType embeddedType recordSetter Set@ will return
the C Syntax for the following function.

@
static inline void recordSetter(boxType p, embeddedType v) {
  field1Setter(p, v.field1);
  field2Setter(p, v.field2);
  ...
}
@

-}
recordGetterSetter
  :: [(CId, FunName)]
      -- ^
      -- ( Name of the field in the struct for the embedded data
      -- , Name of the getter/setter function which will extract that field from the boxed data
      -- )
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter/setter function
  -> GetOrSet
      -- ^ Whether to generate getter or setter
  -> CExtDecl
      -- ^ The C syntax tree for a function which puts/extracts the embedded data from the box.

recordGetterSetter fields boxType embeddedType functionName getOrSet =
  getterSetterDecl boxType embeddedType functionName getOrSet
    -- Get statements
    [ CBIStmt $ CReturn $ Just $ CCompLit embeddedType $
        fmap
        (\(fieldName, fieldGetter) -> ([CDesignFld fieldName], CInitE $ CEFnCall (variable fieldGetter) [boxVariable]))
        fields
    ]

    -- Set statements
    ( fmap
      (\(fieldName, fieldSetter) ->
        CBIStmt $ CAssignFnCall Nothing (variable fieldSetter) [boxVariable, CStructDot valueVariable fieldName])
      fields
    )


unitGetterSetter
  :: CType
     -- ^ The C type of the box.
  -> CId
     -- ^ The name to give the generated getter/setter function
  -> GetOrSet
     -- ^ Whether to generate getter or setter
  -> CExtDecl
     -- ^ The C syntax tree for a function which puts/extracts the embedded data from the box.

unitGetterSetter boxType functionName getOrSet =
  getterSetterDecl boxType unitType functionName getOrSet
    -- Get statements
    -- Not sure if need to initialise field of unit values to a given number
    [ CBIStmt $ CReturn $ Just $
        CCompLit unitType [([CDesignFld dummyField], CInitE $ CConst $ CNumConst 0 signedIntType DEC)]
    ]

    -- Set statements
    -- Intentionally empty
    []



{-|
Creates a C function which either:

* gets the contents of a list of aligned bitranges
  out of a boxed value and concatenates the retrieved values
  to produce a value of the given embedded value type.
* sets the contents of a list of aligned bitranges
  in a boxed value from the pieces of a value of the given embedded value type.

@composedAlignedRangeGetter
  ((firstBitSize, firstGeterFunction) : bitRanges)
  boxType
  embeddedType
  functionName
  Get@
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

@composedAlignedRangeSetter
  bitRanges
  boxType
  embeddedType
  functionName
  Set@
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
composedAlignedRangeGetterSetter
  :: [(AlignedBitRange, FunName)]
      -- ^
      -- The bit ranges and the 'FunName' which is
      -- the name of the getter/setter function for the corresponding
      -- bit range.
  -> Endianness
      -- ^ The endianness of the embedded data.
  -> CType
      -- ^ The C type of the box.
  -> CType
      -- ^ The C type of the embedded data.
  -> CId
      -- ^ The name to give the generated getter/setter function
  -> GetOrSet
      -- ^ Whether to generate a getter or setter
  -> CExtDecl
      -- ^ The C syntax tree for a function which extracts/puts the embedded data from/in the box.

composedAlignedRangeGetterSetter
  bitRanges@((firstRange, firstGetterFunction) : bitRangesTail)
  endianness
  boxType
  embeddedType
  functionName
  getOrSet
  =
  getterSetterDecl boxType embeddedType functionName getOrSet
    -- Get statements
    [ CBIStmt $ CReturn $ Just $ fromIntValue embeddedType $ snd $ foldl'
      (\ (accumulatedBitOffset, accumulatedExpr) (range, rangeGetterFunction) ->
        ( accumulatedBitOffset + bitSizeABR range
        , CBinOp Or accumulatedExpr
            ( genGetAlignedRangeAtBitOffset rangeGetterFunction accumulatedBitOffset )
        )
      )
      (bitSizeABR firstRange, genGetAlignedRangeAtBitOffset firstGetterFunction 0)
      bitRangesTail
    ]

    -- Set statements
    ( fmap
      (\((bitRange, setRangeFunction), offset) ->
          CBIStmt (genSetAlignedRangeAtBitOffset setRangeFunction endianness offset (bitSizeABR bitRange))
      )
      $ zip bitRanges
      $ scanl' (+) 0
      $ fmap (bitSizeABR . fst) bitRanges
    )
  where
    -- If embeddedType is a boxed type, we cast valueVariable to the integer type of the correct size
    -- If it is a boolean type, we extract the boolean value
    valueExpression = toIntValue embeddedType valueVariable

    endiannessConversionFunction :: Endianness -> FunName
    endiannessConversionFunction endianness = case intTypeForType embeddedType of
      (CIdent cid) -> map toLower $ show endianness ++ "_" ++ cid
      (CInt _ _)   -> map toLower $ show endianness ++ "_" ++ "u8"
      _            -> __impossible "endiannessConversionFunction called with invalid embedded type"

    {-
    @genGetAlignedRangeAtBitOffset getRangeFunction offset@ will return the 'CExpr'

    @
      ((`embeddedType`) `getRangeFunction`(b)) << `offset`
    @
    -}
    genGetAlignedRangeAtBitOffset :: FunName -> Integer -> CExpr
    genGetAlignedRangeAtBitOffset getRangeFunction offset =
      case endianness of
            ME -> expression
            _  -> CEFnCall (variable $ endiannessConversionFunction endianness) [expression]
      where expression = CBinOp Lsh
                          ( CTypeCast (intTypeForType embeddedType) (CEFnCall (variable getRangeFunction) [boxVariable]) )
                          ( unsignedIntLiteral offset )

    {-
    @genSetAlignedRangeAtBitOffset setRangeFunction offset size@ will return the 'CExpr'

    @
      `setRangeFunction`(b, (unsigned int) ((v >> `offset`) & `size`))
    @
    -}
    genSetAlignedRangeAtBitOffset :: FunName -> Endianness -> Integer -> Integer -> CStmt
    genSetAlignedRangeAtBitOffset setRangeFunction endianness offset size =
      let expression = case endianness of
            ME -> valueExpression
            _  -> CEFnCall (variable $ endiannessConversionFunction endianness) [valueExpression]
      in CAssignFnCall Nothing (variable setRangeFunction)
        [ boxVariable
        , CTypeCast
            unsignedIntType
            ( CBinOp And
              ( CBinOp Rsh expression (unsignedIntLiteral offset) )
              ( unsignedIntLiteral (sizeToMask size) )
            )
        ]

composedAlignedRangeGetterSetter _ _ _ _ _ _ = __impossible $ "composedAlignedRangeGetter should never be called on an empty list of ranges!"


{-|
Creates a C function to extract/set the contents of an
AlignedBitRange from/in a Cogent boxed type.

@alignedRangeGetter boxType AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR} functionNameIdentifier Get@
should be the C function

@
static inline unsigned int get`functionNameIdentifier`(`boxType` p) {
  return (p.data[`wordOffsetABR`] >> `bitOffsetABR`) & `mask bitSizeABR`;
}
@
or
@
static inline unsigned int get`functionNameIdentifier`(char *p) {
  return (p[`wordOffsetABR` * 4] >> `bitOffsetABR`) & `mask bitSizeABR`;
}
@

@alignedRangeSetter boxType AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR} functionNameIdentifier Set@
should be the C function

@
static inline void set`functionNameIdentifier`(`boxType` p, unsigned int v) {
  p->data[`wordOffsetABR`]
    = p->data[`wordOffsetABR`]

    // clear the bits
    & ~(`sizeToMask bitSizeABR` << `bitOffsetABR`))

    // set the bits
    | ((`sizeToMask bitSizeABR` & v) << `bitOffsetABR`);
}
@
or
@
static inline void set`functionNameIdentifier`(char *p, unsigned int v) {
  p[`wordOffsetABR` * 4]
    = p[`wordOffsetABR` * 4]
    & ~(`sizeToMask bitSizeABR` << `bitOffsetABR`)
    | ((`sizeToMask bitSizeABR` & v) << `bitOffsetABR`);
}
@
-}
alignedRangeGetterSetter :: IsStruct -> CType -> AlignedBitRange -> CId -> GetOrSet -> CExtDecl
alignedRangeGetterSetter
  isStruct
  boxType
  algnBR
  functionName
  getOrSet
  =
  getterSetterDecl boxType unsignedIntType functionName getOrSet
    -- Get statements
    [ CBIStmt $ CReturn $ Just
      ( CBinOp And
        ( CBinOp Rsh dataLocExpr bitOffsetLiteral )
        maskLiteral
      )
    ]

    -- Set statements
    [ CBIStmt
      ( CAssign
        dataLocExpr
        ( CBinOp Or
          ( CBinOp And
            dataLocExpr
            ( CUnOp Not ( CBinOp Lsh maskLiteral bitOffsetLiteral ) )
          )
          ( CBinOp Lsh
            ( CBinOp And maskLiteral valueVariable )
            bitOffsetLiteral
          )
        )
      )
    ]
  where
    bitSizeABR'      = bitSizeABR algnBR
    bitOffsetABR'    = bitOffsetABR algnBR
    wordOffsetABR'   = wordOffsetABR algnBR
    bitOffsetLiteral = unsignedIntLiteral bitOffsetABR'
    maskLiteral      = unsignedIntMask $ sizeToMask bitSizeABR'
    dataLocExpr      = case isStruct of
                         True -> genBoxWordExpr boxVariable wordOffsetABR'
                         False -> CArrayDeref boxVariable (unsignedIntLiteral $ wordOffsetABR')

-- | Returns a function declaration for setter or getter.
getterSetterDecl
  :: CType          -- ^ Box type
  -> CType          -- ^ Embedded type
  -> CId            -- ^ Function name
  -> GetOrSet       -- ^ Whether to generate getter or setter
  -> [CBlockItem]   -- ^ Statements for getter
  -> [CBlockItem]   -- ^ Statements for setter
  -> CExtDecl       -- ^ The setter or getter function declaration

getterSetterDecl boxType embeddedType functionName Get getStatements _ =
  ( CFnDefn
    ( embeddedType, functionName )  -- (return type, function name)
    [ ( boxType, boxIdentifier ) ]  -- [(param type, param name)]
    getStatements
    staticInlineFnSpec
  )

getterSetterDecl boxType embeddedType functionName Set _ setStatements =
  ( CFnDefn
    ( CVoid, functionName ) -- (return type, function name)

    -- [(param type, param name)]
    [ ( boxType, boxIdentifier )
    , ( embeddedType, valueIdentifier )
    ]

    setStatements
    staticInlineFnSpec
  )

arrayGetterSetter
  :: CType
  -> CType
  -> Size
  -> CId
  -> FunName
  -> GetOrSet
  -> CExtDecl
arrayGetterSetter arrType elemType elemSize functionName elemGetterSetter Get =
  ( CFnDefn
    ( elemType, functionName )  -- (return type, function name)
    -- [(param type, param name)]
    [ ( arrType, arrIdentifier )
    , ( unsignedIntType, idxIdentifier ) -- NOTE: type unverified
    ]
    [ CBIStmt $ CReturn $ Just
      ( CEFnCall (variable elemGetterSetter)
        [( CBinOp Add
          ( CTypeCast ( CPtr unsignedCharType ) arrVariable )
          ( CBinOp Mul idxVariable ( unsignedIntLiteral elemSize ) )
        )]
      )
    ]
    staticInlineFnSpec
  )
arrayGetterSetter arrType elemType elemSize functionName elemGetterSetter Set =
  ( CFnDefn
    ( CVoid, functionName ) -- (return type, function name)
    -- [(param type, param name)]
    [ ( arrType, arrIdentifier )
    , ( unsignedIntType, idxIdentifier )
    , ( elemType, valueIdentifier )
    ]
    [ CBIStmt $ CReturn $ Just
      ( CEFnCall (variable elemGetterSetter)
        [ ( CBinOp Add
            ( CTypeCast ( CPtr unsignedCharType ) arrVariable )
            ( CBinOp Mul idxVariable ( unsignedIntLiteral elemSize ) )
          )
        , valueVariable
        ]
      )
    ]
    staticInlineFnSpec
  )


-- * Auxilliary functions, definitions and constants


-- | @sizeToMask n@ is an integer whose binary representation has
-- exactly @n@ 1s in the @2^0@ to @2^(n-1)@ places
sizeToMask :: Integer -> Integer
sizeToMask n
  | 0 <= n && n <= wordSizeBits = 2^n - 1
  | otherwise = __impossible $ "Dargent.CodeGen: sizeToMask " ++ show n ++ ": n not in range [0, " ++ show wordSizeBits ++ "] after alignment"

{-|
Saves the given setter or getter function
C syntax tree into the Gen state.
-}
declareSetterOrGetter :: CExtDecl -> Gen v ()
declareSetterOrGetter function = tell [function]


{-|
@genBoxWordExpr boxExpr wordOffset@
returns syntax for the 'CExpr'
@
`boxExpr`.data[`wordOffset`]
@
-}
genBoxWordExpr :: CExpr -> Integer -> CExpr
genBoxWordExpr boxExpr wordOffset =
  CArrayDeref (CStructDot (CDeref boxExpr) boxFieldName) (unsignedIntLiteral wordOffset)
  -- ALTERNATELY: CDeref ( CBinOp Add (CStructDot boxExpr "data") (unsignedIntLiteral wordOffset))

boxFieldName :: CId
boxFieldName = "data"

{- | The first parameter to all setters/getters -}
boxIdentifier = "b"
boxVariable   = variable boxIdentifier

{- | The second parameter to setters -}
valueIdentifier = "v"
valueVariable   = variable valueIdentifier

-- | Below for array related operations
arrIdentifier = "a"
arrVariable   = variable arrIdentifier
idxIdentifier = "i"
idxVariable   = variable idxIdentifier


-- | Produces a C expression for an unsigned integer literal with the given integer value.
unsignedIntLiteral :: Integer -> CExpr
unsignedIntLiteral n = CConst $ CNumConst n unsignedIntType DEC

unsignedIntMask :: Integer -> CExpr
unsignedIntMask n = CConst $ CNumConst n unsignedIntType (__fixme DEC) {- TODO: Change DEC to BIN. Requires implementing this in cLitConst function of Render.hs -}

unsignedLongType = CInt False CLongT
unsignedIntType = CInt False CIntT
unsignedCharType = CInt False CCharT
signedIntType = CInt True CIntT
unitType = CIdent unitT
tagType = CIdent tagsT



toIntValue :: CType -> CExpr -> CExpr
toIntValue (CInt _ _) cexpr               = cexpr
toIntValue (CIdent t) cexpr
  | t == boolT                            = CStructDot cexpr boolField
  | t `elem` ["u8", "u16", "u32", "u64"]  = cexpr
toIntValue _          cexpr               = CTypeCast intTypeForPointer cexpr

fromIntValue :: CType -> CExpr -> CExpr
fromIntValue (CInt _ _)     cexpr         = cexpr
fromIntValue (CIdent t)     cexpr
  | t == boolT                            = CCompLit (CIdent boolT) [([CDesignFld boolField], CInitE cexpr)]
  | t `elem` ["u8", "u16", "u32", "u64"]  = cexpr
fromIntValue ctype          cexpr         = CTypeCast ctype cexpr

{-
Given the CType of an embedded value (leaf of composite type tree) to extract,
returns the corresponding integer type it should be extracted as before casting.
-}
intTypeForType :: CType -> CType
intTypeForType ctype@(CInt _ _)           = ctype
intTypeForType (CIdent t)
  | t == boolT                            = unsignedCharType-- embedded boolean
  | t == tagsT                            = unsignedIntType
  | t `elem` ["u8", "u16", "u32", "u64"]  = CIdent t
intTypeForType _                          = intTypeForPointer -- embedded boxed abstract type/record

type CogentType = Type 'Zero VarName

intTypeForPointer = case __cogent_arch of
  X86_64 -> unsignedLongType
  X86_32 -> unsignedIntType
  ARM32  -> unsignedIntType

data GetOrSet = Get | Set
type IsStruct = Bool
