{-

This file provides a generator of records with custom layouts
(genRecordWithLayout), based on the core layout generator of 
CogentTests.Dargent.Core.

It finally provides a generator of cogent programs that tests
a generated record with custom layout (genTestLayoutProg).

As intermediate functions, this file also contains
- a surface layout generator out of a core layout
- a surface cogent type generator out of a surface layout

The intermediate layer (surface layout generator) is useful because a primary
core layout could either represent a primary type or a pointer. This difference
is visible in the surface layout, but not in the core layout.

-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
module CogentTests.Dargent.TypeWithLayout where
import Data.Nat (Nat(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)
import GHC.Generics (Generic)

import Text.Parsec.Pos (SourcePos, initialPos)
import Test.QuickCheck

import Text.PrettyPrint.ANSI.Leijen hiding (indent, tupled, (<$>))
import Cogent.PrettyPrint

import Cogent.Dargent.Core
import Cogent.Dargent.Util
import Cogent.Surface
import Cogent.Dargent.Allocation 
import Cogent.Common.Syntax (TagName, FieldName, Size, DLVarName, Likelihood( Regular ))
import Cogent.Common.Types (Sigil(..), RecursiveParameter(..) , PrimInt (..))

import CogentTests.Dargent.Core (genRecordLayout)


primIntMinSize = 1

primIntSizeBits' :: PrimInt -> Size
primIntSizeBits' U8      = 8
primIntSizeBits' U16     = 16
primIntSizeBits' U32     = 32
primIntSizeBits' U64     = 64
primIntSizeBits' Boolean = 1

possiblePrimInt :: Size -> [ PrimInt ]
possiblePrimInt n = filter (\p ->  primIntSizeBits' p == n) [ U8, U16, U32, U64, Boolean ]

primIntSurfName :: PrimInt -> String
primIntSurfName U8      = "U8"
primIntSurfName U16     = "U16"
primIntSurfName U32     = "U32"
primIntSurfName U64     = "U64"
primIntSurfName Boolean = "Bool"

primIntSurfType :: PrimInt -> Type t e l
primIntSurfType p = TCon (primIntSurfName p) [] Unboxed


errorType :: String -> Type t e l
errorType msg = TVar msg False False
  
-- genSurfaceType :: DataLayoutExpr -> Gen (Type t e l)
genSurfaceType :: DataLayoutExpr -> Gen RawType
genSurfaceType (DLPrim n) =
   if size < primIntMinSize then
     return $ RT TUnit
   else
     elements (map (RT . primIntSurfType) (possiblePrimInt size))
   where size = evalSize n

genSurfaceType (DLRecord fs) = do
  l <- sequence (map field_type fs)
  return $ RT $ TRecord NonRec l Unboxed
  where
    field_type :: (FieldName, SourcePos, DataLayoutExpr) -> Gen (FieldName, (RawType, Taken))
    field_type (name, _, dl) = do
      typ <- genSurfaceType dl
      return $ (name, (typ, False)) 


genSurfaceType (DLVariant _ fs) = do
  l <- sequence (map con_type fs)
  return $ RT $ TVariant (Map.fromList l)
  where
      con_type :: (TagName, SourcePos, Size, DataLayoutExpr) -> Gen (TagName, ([RawType], Taken))
      con_type (name, _, _, dl) = do
        typ <- genSurfaceType dl
        return (name, ([typ], False))
    

   -- (M.Map TagName ([t], Taken))
genSurfaceType (DLOffset e s) = genSurfaceType e
  -- unexpected stuff
genSurfaceType (DLRepRef n s) = return $ RT $ errorType "error_DLRepRef"
genSurfaceType (DLVar n) = return $ RT $ errorType "error_DLVar"

-- TODO: generate a real type
genSurfaceType DLPtr = return $ RT $ TRecord NonRec [ ("pointed", (RT TUnit, False))] (Boxed True Nothing)




somePos :: SourcePos
somePos = noPos -- initialPos "arbitrary"

bitRangeToDL :: BitRange -> DataLayoutExpr
bitRangeToDL (BitRange bitSizeBR bitOffsetBR) =
  DL $ Offset (DL $ Prim $ Bits bitSizeBR) (Bits bitOffsetBR)


-- Core to surface layout
genSurfaceLayout :: DataLayout' BitRange -> Gen DataLayoutExpr
genSurfaceLayout UnitLayout = return (DL (Prim (Bits 0)))
genSurfaceLayout (PrimLayout bitrange@(BitRange bitSizeBR bitOffsetBR)) =
  frequency $  ((3, return $ bitRangeToDL bitrange) :
        if bitSizeBR >= pointerSizeBits then
          [ (1, return $ DL $ Offset (DL Ptr) $ Bits bitOffsetBR)]
        else
          [])

genSurfaceLayout (RecordLayout fs) =
  (DL . Record) <$> sequence (map field_aux (Map.toList fs))
  where
    field_aux :: (FieldName, DataLayout' BitRange) -> Gen (FieldName, SourcePos, DataLayoutExpr)
    field_aux (name, dl) = do
      sl <- genSurfaceLayout dl
      return (name, somePos, sl)

genSurfaceLayout (SumLayout bitrange fs) = 
  (DL . (Variant (bitRangeToDL bitrange))) <$> sequence (map con_aux (Map.toList fs))
  where
      con_aux :: (TagName, (Integer, DataLayout' BitRange)) -> Gen (TagName, SourcePos, Size, DataLayoutExpr)
      con_aux (name, (v, dl)) = do
        sl <- genSurfaceLayout dl
        return (name, somePos, v, sl)

genSurfaceLayout (VarLayout _ _) = return $ DL $ LVar "error_VarLayout"

-- Set the custom layout
setRecordLayout :: DataLayoutExpr -> RawType -> RawType
setRecordLayout dl (RT (TRecord r l _)) =
  RT $ TLayout dl (RT (TRecord r l (Boxed False Nothing)))
setRecordLayout _ t = t

  -- size of the array of bytes as input
genRecordWithLayout :: Size -> Gen RawType
genRecordWithLayout size = do
    (dl, _) <- genRecordLayout (fromIntegral size) size (Allocation []) -- genRecord size
    dlSurf <- genSurfaceLayout dl
    typ <- genSurfaceType dlSurf
    return $ (setRecordLayout dlSurf) typ 

newtype CogentProg = CogentProg [TopLevel RawType RawPatn RawExpr]
instance Show CogentProg where
  show (CogentProg l) = intercalate "\n\n"
    (map
     (show . plain . pretty)
     l)

-- generate a cogent program from the given record type Example
{-
type Example = {field0 : .., field1 : .., ..}
main : Example -> Example
main (r {field0,field1,field2}) = r {field0,field1,field2}
-}
recordTestCogentProgram :: RawType -> CogentProg
recordTestCogentProgram typ@(RT (TLayout _ (RT (TRecord _ lrec _)))) =
   CogentProg
   [TypeDec "Example" [] typ,
     FunDef "main" polytype [alt]]
   where
     polytype = PT [] [] (RT $ TFun typName typName) 
     typName = RT $ TVar "Example" False False
     alt = Alt pat Regular expr
     pat :: RawPatn
     -- r {field1, field2, field3, ..}
     pat = RP $ PIrrefutable $ RIP $ PTake "r" (map (\n -> (Just (n, RIP $ PVar $ n))) fields)
     fields = map (\(name, _) -> name) lrec
     expr = RE $ Put (RE $ Var "r")
       (map (\n -> (Just (n, RE $ Var n))) fields)

genTestLayoutProg :: Size -> Gen CogentProg
genTestLayoutProg n = do
  t <- genRecordWithLayout n
  return $ recordTestCogentProgram t

