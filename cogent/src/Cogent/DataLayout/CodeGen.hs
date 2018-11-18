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
  , unitT
  , tagsT
  , tagEnum
  , fieldTag
  , dummyField -- Field of type unitT
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

-- GETTER/SETTER GENERATION

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

  -> Gen v CExpr
     -- ^
     -- The 'CExpr' which is the name of the getter/setter function
     -- for the field of the record.
     --
     -- Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     -- to call this getter/setter function.

genBoxedGetSetField cogentType fieldName getOrSet = do
  boxedRecordGetterSetter    <- use ((case getOrSet of Get -> boxedRecordGetters; Set -> boxedRecordSetters) . at (cogentType, fieldName))
  case boxedRecordGetterSetter of
    Just getSetFieldFunction -> return getSetFieldFunction
    Nothing                  -> do
      let TRecord fieldTypes (Boxed _ (RecordLayout fieldLayouts))
                              = cogentType
          fieldType           = fst $ (fromList fieldTypes) ! fieldName
          fieldLayout         = alignLayout $ fst $ fieldLayouts ! fieldName
      boxCType               <- genType cogentType
      getSetFieldFunction    <- genBoxedGetterSetter boxCType fieldType fieldLayout [fieldName] getOrSet
      ((case getOrSet of Get -> boxedRecordGetters; Set -> boxedRecordSetters) . at (cogentType, fieldName))
                             ?= getSetFieldFunction
      return getSetFieldFunction


{-|
Returns a getter/setter function C expression for a part of a boxed record.

Will always generate the getter/setter function and record it in the GenState.
-}
genBoxedGetterSetter
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

  -> [String]
     -- ^ Path in structure to value being get or set, to create readable function name

  -> GetOrSet
     -- ^ Whether to generate a getter or a setter

  -> Gen v CExpr
     -- ^
     -- The 'CExpr' which is the name of the generated getter function
     -- for the field of the record.
     --
     -- Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     -- to call this getter function.

genBoxedGetterSetter boxType embeddedType@(TCon _ _ _) (PrimLayout {bitsDL = bitRanges}) path getOrSet =
  genComposedAlignedRangeGetterSetter bitRanges boxType embeddedType path getOrSet

genBoxedGetterSetter boxType embeddedType@(TPrim _) (PrimLayout {bitsDL = bitRanges}) path getOrSet =
  genComposedAlignedRangeGetterSetter bitRanges boxType embeddedType path getOrSet

genBoxedGetterSetter boxType embeddedType@(TRecord fields (Boxed _ _)) (PrimLayout {bitsDL = bitRanges}) path getOrSet =
  genComposedAlignedRangeGetterSetter bitRanges boxType embeddedType path getOrSet

genBoxedGetterSetter boxType embeddedTypeCogent@(TSum alternatives) (SumLayout {tagDL, alternativesDL}) path getOrSet = do
  embeddedTypeC               <- genType embeddedTypeCogent
  functionName                <- genGetterSetterName path getOrSet
  tagGetterSetter             <- genComposedAlignedRangeGetterSetter' tagDL boxType unsignedIntType (path ++ ["tag"]) getOrSet -- Must add check to restrict number of alternatives to MAX_INT)
  alternativesGettersSetters  <-
      mapM
      (\(alternativeName, (alternativeType, _)) -> do
          let (boxedTagValue, alternativeLayout, _) = alternativesDL ! alternativeName
          getterSetter <- genBoxedGetterSetter boxType alternativeType alternativeLayout (path ++ [alternativeName]) getOrSet
          return (alternativeName, boxedTagValue, getterSetter)
      )
      alternatives
  declareSetterOrGetter $ variantGetterSetter tagGetterSetter alternativesGettersSetters boxType embeddedTypeC functionName getOrSet
  return (CVar functionName Nothing)

genBoxedGetterSetter boxType embeddedTypeCogent@(TRecord fields Unboxed) (RecordLayout { fieldsDL }) path getOrSet = do
  embeddedTypeC         <- genType embeddedTypeCogent
  functionName          <- genGetterSetterName path getOrSet
  fieldGettersSetters   <-
      mapM
      (\(fieldName, (fieldType, _)) -> do
          let fieldLayout = fst $ fieldsDL ! fieldName
          getterSetter <- genBoxedGetterSetter boxType fieldType fieldLayout (path ++ [fieldName]) getOrSet
          return (fieldName, getterSetter)
      )
      fields
  declareSetterOrGetter $ recordGetterSetter fieldGettersSetters boxType embeddedTypeC functionName getOrSet
  return (CVar functionName Nothing)

genBoxedGetterSetter boxType (TUnit) (UnitLayout) path getOrSet = do
  functionName  <- genGetterSetterName path getOrSet
  declareSetterOrGetter $ unitGetterSetter boxType functionName getOrSet
  return (CVar functionName Nothing)

genBoxedGetterSetter boxCType _ _ _ _ = __impossible $
  "Cogent.DataLayout.CodeGen: genBoxedGetterSetter: Type checking should restrict the types which can be embedded in boxed records," ++
  "and ensure that the data layouts match the types."


{-|
Declares in the Gen state a C function which gets/sets the contents
of a list of aligned bitranges in a boxed value which concatenate to
a value of the given embedded type.

Calls the function `composedAlignedRangeGetterSetter` to generate the function.
-}
genComposedAlignedRangeGetterSetter :: [AlignedBitRange] -> CType -> CogentType -> [String] -> GetOrSet -> Gen v CExpr
genComposedAlignedRangeGetterSetter bitRanges boxType embeddedTypeCogent path getOrSet = do
  embeddedTypeC   <- genType embeddedTypeCogent
  genComposedAlignedRangeGetterSetter' bitRanges boxType embeddedTypeC path getOrSet

genComposedAlignedRangeGetterSetter' :: [AlignedBitRange] -> CType -> CType -> [String] -> GetOrSet -> Gen v CExpr
genComposedAlignedRangeGetterSetter' bitRanges boxType embeddedTypeC path getOrSet = do
  functionName    <- genGetterSetterName path getOrSet
  rangesGetters   <- mapM (\(range, index) -> genAlignedRangeGetterSetter boxType (path ++ ["part" ++ show index]) getOrSet range) (zip bitRanges [0..])
  declareSetterOrGetter $ composedAlignedRangeGetterSetter (zip bitRanges rangesGetters) boxType embeddedTypeC functionName getOrSet
  return (CVar functionName Nothing)


{-|
Declares in the Gen state a C function to extract/set the contents of an
AlignedBitRange from/in a Cogent boxed type.

Calls the function `alignedRangeGetterSetter` to generate the function.
-}
genAlignedRangeGetterSetter :: CType -> [String] -> GetOrSet -> AlignedBitRange -> Gen v CExpr
genAlignedRangeGetterSetter boxType path getOrSet bitRange = do
  functionIdentifier <- genGetterSetterName path getOrSet
  declareSetterOrGetter $ alignedRangeGetterSetter boxType bitRange functionIdentifier getOrSet
  return (CVar functionIdentifier Nothing)

{-|
Generates a unique function name for the getter or setter which is also readable.
-}
genGetterSetterName
  :: [String]   -- ^ Path in structure to value being get or set
  -> GetOrSet   -- ^ Whether to generate a getter or setter function
  -> Gen v CId  -- ^ The CId for the function, which is guaranteed to be unique
genGetterSetterName path getOrSet =
  let pathString      = foldr (++) "" $ fmap ('_' :) $ path
      getOrSetString  = (case getOrSet of Get -> "_get" ; Set -> "_set")
  in  (++ (getOrSetString ++ pathString)) <$> freshGlobalCId 'd'


-- GETTER/SETTER FUNCTION DECLARATIONS

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
  :: CExpr -- Expression for the setter/getter function for the tag
  -> [(CId, Integer, CExpr)]
      -- ^
      -- ( Name of the alternative of the variant,
      -- , Tag value for this alternative in the boxed structure
      -- , Expression for the getter/setter function for the alternative
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
                  (CEFnCall tagGetterSetter [boxVariable])
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
                (CVar (tagEnum altName) Nothing))
              (CBlock $ setUnboxedAlt altName tagValue altGetter)
              accumBlockItems
          )
          (CBlock $ setUnboxedAlt firstAltName firstTagValue firstAltGetterSetter)
          otherAlts
        ]
    )
  where
    getUnboxedAlt :: CId -> CExpr -> CExpr
    getUnboxedAlt altName altGetter =
      CCompLit embeddedType
      [ ([CDesignFld fieldTag], CInitE $ CVar (tagEnum altName) Nothing)
      , ([CDesignFld altName], CInitE $ CEFnCall altGetter [boxVariable])
      ]

    setUnboxedAlt :: CId -> Integer -> CExpr -> [CBlockItem]
    setUnboxedAlt altName tagValue altSetter = fmap CBIStmt
      [ CAssignFnCall Nothing tagGetterSetter [boxVariable, CConst $ CNumConst tagValue unsignedIntType DEC]
      , CAssignFnCall Nothing altSetter       [boxVariable, CStructDot valueVariable altName]
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
  :: [(CId, CExpr)]
      -- ^
      -- ( Name of the field in the struct for the embedded data
      -- , Expression for the getter/setter function which will extract that field from the boxed data
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
        (\(fieldName, fieldGetter) -> ([CDesignFld fieldName], CInitE $ CEFnCall fieldGetter [boxVariable]))
        fields
    ]

    -- Set statements
    ( fmap
      (\(fieldName, fieldSetter) ->
        CBIStmt $ CAssignFnCall Nothing fieldSetter [boxVariable, CStructDot valueVariable fieldName])
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
  :: [(AlignedBitRange, CExpr)]
      -- ^
      -- The bit ranges and the 'CExpr' which is
      -- the name of the getter/setter function for the corresponding
      -- bit range.
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
          CBIStmt (genSetAlignedRangeAtBitOffset setRangeFunction offset (bitSizeABR bitRange))
      )
      $ zip bitRanges
      $ scanl' (+) 0
      $ fmap (bitSizeABR . fst) bitRanges
    )
  where
    -- If embeddedType is a boxed type, we cast valueVariable to the integer type of the correct size
    -- If it is a boolean type, we extract the boolean value
    valueExpression = toIntValue embeddedType valueVariable

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

composedAlignedRangeGetterSetter _ _ _ _ _ = __impossible $ "composedAlignedRangeGetter should never be called on an empty list of ranges!"


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

@alignedRangeSetter boxType AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR} functionNameIdentifier Set@
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
alignedRangeGetterSetter :: CType -> AlignedBitRange -> CId -> GetOrSet -> CExtDecl
alignedRangeGetterSetter
  boxType
  AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR }
  functionName
  getOrSet
  =
  getterSetterDecl boxType unsignedIntType functionName getOrSet
    -- Get statements
    [ CBIStmt $ CReturn $ Just
      ( CBinOp And
        ( CBinOp Rsh ( genBoxWordExpr boxVariable wordOffsetABR ) bitOffsetLiteral )
        maskLiteral
      )
    ]

    -- Set statements
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
  where
    bitOffsetLiteral  = unsignedIntLiteral bitOffsetABR
    maskLiteral       = unsignedIntMask $ sizeToMask bitSizeABR

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

 
-- AUXILLIARY FUNCTIONS, DEFINITIONS AND CONSTANTS


-- | @sizeToMask n@ is an integer whose binary representation has
-- exactly @n@ 1s in the @2^0@ to @2^(n-1)@ places
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

{- | The first parameter to all setters/getters -}
boxIdentifier = "b"
boxVariable   = CVar boxIdentifier Nothing

{- | The second parameter to setters -}
valueIdentifier = "v"
valueVariable   = CVar valueIdentifier Nothing

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
toIntValue (CPtr _)   cexpr               = CTypeCast intTypeForPointer cexpr
toIntValue _          cexpr               = CTypeCast intTypeForPointer (CStructDot cexpr boxFieldName)

fromIntValue :: CType -> CExpr -> CExpr
fromIntValue (CInt _ _)     cexpr         = cexpr
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
intTypeForType ctype@(CInt _ _)           = ctype
intTypeForType (CIdent t)
  | t == boolT                            = unsignedCharType-- embedded boolean
  | t == tagsT                            = unsignedIntType
  | t `elem` ["u8", "u16", "u32", "u64"]  = CIdent t
intTypeForType (CPtr _)                   = intTypeForPointer -- embedded boxed abstract type
intTypeForType _                          = intTypeForPointer -- embedded boxed record

type CogentType = Type 'Zero

intTypeForPointer = case architecture of
  X86_64 -> unsignedLongType
  X86_32 -> unsignedIntType

data GetOrSet = Get | Set