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


data GetOrSet = Get | Set

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

genBoxedGetterSetter boxType (TSum alternatives) (SumLayout {tagDL, alternativesDL}) path getOrSet =
  __todo $ "Cogent.DataLayout.CodeGen: genBoxedGetterSetter: Case for embedded variant types not yet implemented."


genBoxedGetterSetter boxType embeddedTypeCogent@(TRecord fields Unboxed) (RecordLayout { fieldsDL }) path getOrSet = do
  embeddedTypeC         <- genType embeddedTypeCogent
  functionName          <- genGetterSetterName path getOrSet
  fieldNamesAndGettersSetters 
                        <- mapM
                            (\(fieldName, (fieldType, _)) -> do
                                let fieldLayout = fst $ fieldsDL ! fieldName
                                getterSetter <- genBoxedGetterSetter boxType fieldType fieldLayout (path ++ [fieldName]) getOrSet
                                return (fieldName, getterSetter)
                            )
                            fields
  declareSetterOrGetter $ recordGetterSetter fieldNamesAndGettersSetters boxType embeddedTypeC functionName getOrSet
  return (CVar functionName Nothing)

genBoxedGetterSetter boxType (TUnit) (UnitLayout) path getOrSet =
  __todo $ "Cogent.DataLayout.CodeGen: genBoxedGetterSetter: Case for embedded unit value not yet implemented."

genBoxedGetterSetter boxCType _ _ _ _ = __impossible $
  "Cogent.DataLayout.CodeGen: genBoxedGetterSetter: Type checking should restrict the types which can be embedded in boxed records," ++
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

recordGetterSetter fields boxType embeddedType functionName Get =
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


recordGetterSetter fields boxType embeddedType functionName Set =
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
Declares in the Gen state a C function which gets/sets the contents
of a list of aligned bitranges in a boxed value which concatenate to
a value of the given embedded type.

Calls the function `composedAlignedRangeGetterSetter` to generate the function.
-}
genComposedAlignedRangeGetterSetter :: [AlignedBitRange] -> CType -> CogentType -> [String] -> GetOrSet -> Gen v CExpr
genComposedAlignedRangeGetterSetter bitRanges boxType embeddedTypeCogent path getOrSet = do
  embeddedTypeC   <- genType embeddedTypeCogent
  functionName    <- genGetterSetterName path getOrSet
  rangesGetters   <- mapM (genAlignedRangeGetterSetter boxType path getOrSet) bitRanges
  declareSetterOrGetter $
    composedAlignedRangeGetterSetter (zip bitRanges rangesGetters) boxType embeddedTypeC functionName getOrSet
  return (CVar functionName Nothing)


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
  ((firstRange, firstGetterFunction) : bitRanges)
  boxType
  embeddedType
  functionName
  Get
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

composedAlignedRangeGetterSetter _ _ _ _ Get = __impossible $
  "genComposedAlignedRangeGetter should never be called on an empty list of ranges!"


composedAlignedRangeGetterSetter
  bitRanges
  boxType
  embeddedType
  functionName
  Set
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
Declares in the Gen state a C function to extract/set the contents of an
AlignedBitRange from/in a Cogent boxed type.

Calls the function `alignedRangeGetterSetter` to generate the function.
-}
genAlignedRangeGetterSetter :: CType -> [String] -> GetOrSet -> AlignedBitRange -> Gen v CExpr
genAlignedRangeGetterSetter boxType path getOrSet bitRange = do
  functionIdentifier <- genGetterSetterName path getOrSet
  declareSetterOrGetter $
    alignedRangeGetterSetter boxType bitRange functionIdentifier getOrSet
  return (CVar functionIdentifier Nothing)


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
  functionIdentifier
  Get
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


alignedRangeGetterSetter
  boxType
  AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR }
  functionNameIdentifier
  Set
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
    


genGetterSetterName
  :: [String]   -- ^ Path in structure to value being get or set
  -> GetOrSet   -- ^ Whether to generate a getter or setter function
  -> Gen v CId  -- ^ The CId for the function, which is guaranteed to be unique
genGetterSetterName path getOrSet =
  let pathString      = foldr (++) "" $ fmap ('_' :) $ path
      getOrSetString  = (case getOrSet of Get -> "_get" ; Set -> "_set")
  in  (++ (getOrSetString ++ pathString)) <$> freshGlobalCId 'd'



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



