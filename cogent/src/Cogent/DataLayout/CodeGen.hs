{-# LANGUAGE NamedFieldPuns #-}
module Cogent.DataLayout.CodeGen where
import Cogent.C.Syntax
import Cogent.Compiler
  ( __impossible
  )
import Cogent.DataLayout.Core
  ( AlignedBitRange (..)
  )

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