--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.ShallowTable where

import Cogent.Common.Syntax
import Cogent.Common.Types
-- import Cogent.Compiler
-- import Cogent.Desugar
import Cogent.Sugarfree
-- import Cogent.Surface
-- import Cogent.TypeCheck

import Control.Monad
import Control.Monad.State
import Data.Function (on)
import qualified Data.List as L (findIndex)
import Data.List as L hiding (findIndex, maximum)
import Data.Map as M hiding (findIndex, null)
import Data.Maybe
import Prelude as P hiding (maximum)

-- import Debug.Trace

data TypeStr = RecordStr  [FieldName]
             | VariantStr [TagName]
             deriving (Eq, Ord)

instance Show TypeStr where
  show (RecordStr  fs) = "{" ++ intercalate ", " fs ++ "}"
  show (VariantStr as) = "<" ++ intercalate "| " as ++ ">"

toTypeStr :: Type t -> [TypeStr]
toTypeStr (TVar v)         = []
toTypeStr (TVarBang v)     = []
toTypeStr (TUnit)          = []
toTypeStr (TProduct t1 t2) = nub $ toTypeStr t1 ++ toTypeStr t2
toTypeStr (TSum ts)        = nub $ VariantStr (sort $ P.map fst ts) : concat (P.map (toTypeStr . fst . snd) ts)  -- alternatives are sorted  -- FIXME: cogent.1
toTypeStr (TFun ti to)     = nub $ toTypeStr ti ++ toTypeStr to
toTypeStr (TRecord ts s)   = nub $ RecordStr (P.map fst ts) : concat (P.map (toTypeStr . fst . snd) ts)
toTypeStr (TPrim i)        = []
toTypeStr (TString)        = []
toTypeStr (TCon n ts s)    = nub $ concat $ P.map toTypeStr ts

getStrlType :: M.Map TypeStr TypeName -> [TypeStr] -> Type t -> Type t
getStrlType tsmap table (TSum ts) =  -- FIXME: cogent.1
  let ts' = sortBy (compare `on` fst) ts
      tstr = VariantStr (P.map fst ts')
      tps = P.map (fst . snd) ts'
  in case M.lookup tstr tsmap of
    Nothing ->
      let idx = findIndex tstr table
      in TCon ('T':show idx) tps Writable
    Just tn ->
      TCon tn tps Writable
getStrlType tsmap table (TRecord fs s) =
  let tstr = RecordStr (P.map fst fs)
      tps = P.map (fst . snd) fs
  in case M.lookup tstr tsmap of
    Nothing ->
      let idx = findIndex tstr table
      in TCon ('T':show idx) tps Writable
    Just tn ->
      TCon tn tps Writable
getStrlType _ _ t = t

type ST = State [TypeStr]

-- ds: from after desugaring, RHS's are unfolded already
st :: [Definition TypedExpr VarName] -> [TypeStr]
st ds = execState (stDefinitions ds) []

stDefinitions :: [Definition TypedExpr VarName] -> ST ()
stDefinitions = mapM_ stDefinition

stDefinition :: Definition TypedExpr VarName -> ST ()
stDefinition (FunDef  _ fn ts ti to e) = stExpr e  -- NOTE: `ti' and `to' will be included in `e', so no need to scan them / zilinc
stDefinition (AbsDecl _ fn ts ti to) = stType ti >> stType to
stDefinition (TypeDef tn ts (Just t)) = stType t
stDefinition (TypeDef tn ts Nothing) = return ()

stExpr :: TypedExpr t v VarName -> ST ()
stExpr (TE t e) = stExpr' e >> stType t
  where
    stExpr' (Variable v)   = return ()
    stExpr' (Fun fn tys _) = mapM_ stType tys
    stExpr' (Op opr es)    = mapM_ stExpr es
    stExpr' (App e1 e2)    = stExpr e1 >> stExpr e2
    stExpr' (Con cn e)     = stExpr e
    stExpr' (Unit)         = return ()
    stExpr' (ILit i pt)    = return ()
    stExpr' (SLit s)       = return ()
    stExpr' (Let a e1 e2)  = stExpr e1 >> stExpr e2
    stExpr' (LetBang vs a e1 e2) = stExpr e1 >> stExpr e2
    stExpr' (Tuple e1 e2) = stExpr e1 >> stExpr e2
    stExpr' (Struct fs)   = mapM_ (stExpr . snd) fs
    stExpr' (If e1 e2 e3) = mapM_ stExpr [e1,e2,e3]
    stExpr' (Case e tn (l1,a1,e1) (l2,a2,e2)) = stExpr e >> mapM_ stExpr [e1,e2]
    stExpr' (Esac e)      = stExpr e
    stExpr' (Split a e1 e2)  = stExpr e1 >> stExpr e2
    stExpr' (Member rec fld) = stExpr rec
    stExpr' (Take a rec fld e) = stExpr rec >> stExpr e
    stExpr' (Put rec fld v)  = stExpr rec >> stExpr v
    stExpr' (Promote ty e)   = stExpr e

-- Add types to the table if not exists
stType :: Type t -> ST ()
stType (toTypeStr -> ts) = forM_ ts $ \t -> do
  table <- get
  case lookupTypeStr t table of
    Nothing -> put $ t:table
    Just _  -> return ()

eqTypeStr :: TypeStr -> TypeStr -> Bool
eqTypeStr (RecordStr  v1) (RecordStr  v2) = v1 == v2
eqTypeStr (VariantStr v1) (VariantStr v2) = v1 == v2
eqTypeStr _ _ = False

findIndex :: TypeStr -> [TypeStr] -> Int
findIndex = (fromJust .) . L.findIndex . eqTypeStr

lookupTypeStr :: TypeStr -> [TypeStr] -> Maybe TypeStr
lookupTypeStr = find . eqTypeStr

-- For debugging
printTable :: [TypeStr] -> String
printTable table = unlines $ P.zipWith (\i t -> 'T':show i ++ " :-> " ++ show t) [1::Int ..] table


