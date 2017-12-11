{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}

module Util where

import Meta
import Syntax
import Kinds
-- import Pretty

import Control.Applicative ((<$>), (<*>))
import Data.IORef
import Data.List as L (sort, map)
import Data.Map
import Language.Haskell.TH hiding (Kind)
-- import Language.Haskell.TH.Syntax
import Text.PrettyPrint.ANSI.Leijen (Pretty, plain, pretty)
import System.IO.Unsafe

type Level = Integer

type Def   = Map Ident (DataDesc, Level)
type Delta = Map Ident Kind  -- Type -> Kind
type Gamma = Map Ident Kind  -- Variable -> Kind
type Pi    = Map Ident (Kind, Value)  -- Constant -> (Kind, Value)

type Size = Integer
type Position = Integer

dummyPos :: SourcePos
dummyPos = newPos "dummySource" 0 0

progErr :: String -> String
progErr f = "ERROR: Fatal error occurs in function `" ++ f ++ "'"


data Module = Module { modName :: ModName
                     , modHead :: ModHead
                     , modDesc :: [DataDesc] }

instance Eq Module where
  Module n1 _ _ == Module n2 _ _ = n1 == n2
instance Ord Module where
  Module n1 _ _ <= Module n2 _ _ = n1 <= n2

newtype ModName = ModName FilePath deriving (Eq, Ord)
newtype ModHead = ModHead { impMods :: [ModName] }

-------------------------------------------------------------------------------
-- Value vs. Expr

data Value = BadV
           | IConst Integer
           | BConst Bool
           | IEnum  [(Expr, Integer)]

instance Eq Value where
  BadV        == BadV        = True
  (IConst n1) == (IConst n2) = (n1 == n2)
  (BConst b1) == (BConst b2) = (b1 == b2)
  (IEnum ns1) == (IEnum ns2) = (sort (L.map snd ns1) == sort (L.map snd ns2))
  _ == _ = False

valueToExpr :: Value -> Expr
valueToExpr (IConst n) = ILit n dummyPos
valueToExpr (BConst b) = BLit b dummyPos
valueToExpr _ = error $ progErr "valueToExpr"

appValueIII :: Value -> Value -> (Integer -> Integer -> Integer) -> Value
appValueIII (IConst n1) (IConst n2) f = IConst (f n1 n2)
appValueIII _ _ _ = error $ progErr "appValueIII"

appValueIIB :: Value -> Value -> (Integer -> Integer -> Bool) -> Value
appValueIIB (IConst n1) (IConst n2) f = BConst (f n1 n2)
appValueIIB _ _ _ = error $ progErr "appValueIIB"

appValueBBB :: Value -> Value -> (Bool -> Bool -> Bool) -> Value
appValueBBB (BConst b1) (BConst b2) f = BConst (f b1 b2)
appValueBBB _ _ _ = error $ progErr "appValueBBB"

appValueI :: Value -> (Integer -> Integer) -> Value
appValueI (IConst n) f = IConst (f n)
appValueI _ _ = error $ progErr "appValueI"

evalFunc :: Func -> [Value] -> Value
evalFunc (Func "toU16") (v:[]) = v
evalFunc (Func "toU24") (v:[]) = v
evalFunc (Func "toU32") (v:[]) = v
evalFunc (Func "toU64") (v:[]) = v
evalFunc (Func "in") ([IConst v, IEnum ev]) = BConst $ v `elem` L.map snd ev
evalFunc _ _ = error $ progErr "evalFunc"

-------------------------------------------------------------------------------
-- Flags

$(mkFlag "show_parse")
$(mkFlag "show_check")
$(mkFlag "show_rewrite")
$(mkFlag "show_rewrite_del")
$(mkFlag "show_gen")
$(mkFlag "allow_u24")
$(mkFlag "allow_empty_struct")
$(mkFlag "no_gen_file")

output_internal :: FilePath
output_internal = unsafePerformIO $ readIORef output_ref

output_ref :: IORef FilePath
{-# NOINLINE output_ref #-}
output_ref = unsafePerformIO $ newIORef $ error "`output_ref' not initialised"
