{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
module Cogent.DataLayout.CodeGen
  ( genBoxedGetField
  , genAlignedRangeGetter -- Exported only for testing
  , genAlignedRangeSetter -- Exported only for testing
  ) where
    
import Cogent.C.Syntax
import Cogent.Common.Syntax (FieldName)
import Data.Nat
import Cogent.C.Compile (Gen)
import Cogent.Core (Type (..))
import Cogent.Compiler (__impossible)
import Cogent.DataLayout.Core
  ( AlignedBitRange (..)
  , DataLayout (..)
  )

type CogentType t = Type t


-- | Returns a getter function C expression for a field of a boxed record.
--
--   Will generate the getter function if it has not yet been generated
--   (ie. checks to see if it is already recorded in the GenState)
genBoxedGetField
  :: CogentType 'Zero
     -- ^ Cogent type of an unboxed record.

  -> FieldName
     -- ^ Name of field in the unboxed record to extract.

  -> Gen v CExpr
     -- ^ The 'CExpr' which is the name of the getter function
     --   for the field of the record.
     --
     --   Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     --   to call this getter function.
genBoxedGetField = undefined


-- | Returns a getter function C expression for a part of a boxed record.
--
--   Will always generate the getter function and record it in the GenState.
genBoxedGet
  :: CType
     -- ^ The CType for the root boxed type which contains
     --   the embedded value that we would like to extract

  -> CogentType 'Zero
     -- ^ The Cogent type of the embedded value that we would like to extract

  -> DataLayout AlignedBitRange
     -- ^ The part of the root boxed type's DataLayout corresponding to
     --   the embedded value that we would like to extract.

  -> Gen v CExpr
     -- ^ The 'CExpr' which is the name of the generated getter function
     --   for the field of the record.
     --
     --   Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     --   to call this getter function.
genBoxedGet = undefined

-- | Returns a setter function C expression for a field of a boxed record.
--
--   Will generate the setter function if it has not yet been generated
--   (ie. checks to see if it is already recorded in the GenState)
genBoxedSetField
  :: CogentType 'Zero
     -- ^ Cogent type of an unboxed record.

  -> FieldName
     -- ^ Name of field in the unboxed record to put.

  -> Gen v CExpr
     -- ^ The 'CExpr' which is the name of the setter function
     --   for the field of the record.
     --
     --   Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     --   to call this setter function.
genBoxedSetField = undefined

-- | Returns a setter function C expression for a part of a boxed record.
--
--   Will always generate the setter function and record it in the GenState.
genBoxedSet
  :: CType
     -- ^ The CType for the root boxed type which contains
     --   the embedded value that we would like to put

  -> CogentType 'Zero
     -- ^ The Cogent type of the embedded value that we would like to put

  -> DataLayout AlignedBitRange
     -- ^ The part of the root boxed type's DataLayout corresponding to
     --   the embedded value that we would like to put.

  -> Gen v CExpr
     -- ^ The 'CExpr' which is the name of the generated setter function
     --   for the field of the record.
     --
     --   Use this 'CExpr' as the first argument of 'CEFnCall' when you want
     --   to call this setter function.
genBoxedSet = undefined



{- | Creates a C function to extract the contents of an
     AlignedBitRange from a Cogent boxed type.
     
     `alignedRangeGetter AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR} functionNameIdentifier` should be the C function
     
     @
      static inline unsigned int get`functionNameIdentifier`(unsigned int *p) {
        return (*(p + `wordOffsetABR`) >> `bitOffsetABR`) & `mask bitSizeABR`;
      }
     @
-}
genAlignedRangeGetter :: AlignedBitRange -> CId -> CExtDecl
genAlignedRangeGetter
  AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR}
  functionNameIdentifier
  =
  ( CFnDefn
  
    -- (return type, function name)
    ( unsignedIntType, functionNameIdentifier )
    
    -- [(param type, param name)]
    [ ( CPtr unsignedIntType, ptrIdentifier ) ]
    
    -- statements
    [ CBIStmt
      ( CReturn
        ( Just 
          ( CBinOp And
            ( CBinOp Rsh
              ( CDeref ( CBinOp Add ptrVariable wordOffsetLiteral ) )
              bitOffsetLiteral
            )
            maskLiteral
          )
        )
      )
    ]
  
    staticInlineFnSpec
  )
  where
    ptrIdentifier = "p"
    ptrVariable   = CVar ptrIdentifier Nothing
    
    wordOffsetLiteral = unsignedIntLiteral wordOffsetABR
    bitOffsetLiteral  = unsignedIntLiteral bitOffsetABR
    maskLiteral   = unsignedIntLiteral $ sizeToMask bitSizeABR


{- | Creates a C function to extract set the contents of an
     AlignedBitRange in a Cogent boxed type.
     
     `alignedRangeSetter AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR} functionNameIdentifier` should be the C function
     
     @
      static inline void set`functionNameIdentifier`(unsigned int *p, unsigned int v) {
        *(p + `wordOffsetABR`)
          = *(p + `wordOffsetABR`)

          // clear the bits
          & ~(`sizeToMask bitSizeABR` << `bitOffsetABR`)) 
          
          // set the bits
          | ((`sizeToMask bitSizeABR` & v) << `bitOffsetABR`);
      }
     @
-}
genAlignedRangeSetter :: AlignedBitRange -> CId -> CExtDecl
genAlignedRangeSetter
  AlignedBitRange { bitSizeABR, bitOffsetABR, wordOffsetABR }
  functionNameIdentifier
  =
  ( CFnDefn
  
    -- (return type, function name)
    ( CVoid, functionNameIdentifier )
    
    -- [(param type, param name)]
    [ ( CPtr unsignedIntType, ptrIdentifier )
    , ( unsignedIntType, valueIdentifier )
    ]
    
    -- statements
    [ CBIStmt
      ( CAssign
        ( CDeref ( CBinOp Add ptrVariable wordOffsetLiteral ) )
        ( CBinOp Or
          ( CBinOp And
            ( CDeref ( CBinOp Add ptrVariable wordOffsetLiteral ) )
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
    ptrIdentifier = "p"
    ptrVariable   = CVar ptrIdentifier Nothing
    
    valueIdentifier = "v"
    valueVariable   = CVar valueIdentifier Nothing
    
    wordOffsetLiteral = unsignedIntLiteral wordOffsetABR
    bitOffsetLiteral  = unsignedIntLiteral bitOffsetABR
    maskLiteral   = unsignedIntLiteral $ sizeToMask bitSizeABR
    
    
sizeToMask n
  | 0 <= n && n <= 8  = 2^n - 1
  | otherwise         = __impossible $ "After alignment"
    
-- Produces syntax for an unsigned integer literal with the given value
unsignedIntLiteral :: Integer -> CExpr
unsignedIntLiteral n = CConst $ CNumConst n unsignedIntType DEC

unsignedIntType = CInt False CIntT