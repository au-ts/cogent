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
{- LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.Isabelle.ShallowTable where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler (__fixme)
-- import Cogent.Desugar
import Cogent.Core
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
import Cogent.Compiler (__fixme)

-- import Debug.Trace

data TypeStr = RecordStr  [FieldName]
             | VariantStr [TagName]
           -- \ | ArrayStr
             deriving (Eq, Ord)

instance Show TypeStr where
  show (RecordStr  fs) = "{" ++ intercalate ", " fs ++ "}"
  show (VariantStr as) = "<" ++ intercalate "| " as ++ ">"
  -- show (ArrayStr)      = "array"

-- | Collects type structures from a Cogent type.
toTypeStr :: Type t a -> [TypeStr]
toTypeStr (TVar v)         = []
toTypeStr (TVarBang v)     = []
toTypeStr (TUnit)          = []
toTypeStr (TProduct t1 t2) = nub $ toTypeStr t1 ++ toTypeStr t2
toTypeStr (TSum ts)        = nub $ VariantStr (P.map fst ts) : concat (P.map (toTypeStr . fst . snd) ts)
   -- \ ^^^ NOTE: alternatives are ordered throughout the compiler / zilinc
toTypeStr (TFun ti to)     = nub $ toTypeStr ti ++ toTypeStr to
-- TODO: Should recpars be part of type strings?
toTypeStr (TRecord _ ts _)   = nub $ RecordStr (P.map fst ts) : concatMap (toTypeStr . fst . snd) ts
toTypeStr (TPrim i)        = []
toTypeStr (TString)        = []
toTypeStr (TCon n ts _)    = nub $ concatMap toTypeStr ts
toTypeStr (TSyn n ts _ _)  = nub $ concatMap toTypeStr ts
#ifdef BUILTIN_ARRAYS
toTypeStr (TArray {})      = []
#endif
toTypeStr (TRPar v m)      = []

-- | Given a map for type synonyms, the table, and a type @t@, returns
--   a type in the form of a 'TCon', which means that if there's a type
--   synonym, it will be used; otherwise we will create a unique name
--   for the type according to the position of that type in the table.
--   This will make the generated Isabelle files more readable by humans.
--   The result cannot collide with the original use of the type synonym
--   because that has the form of a 'TSyn'.
-- Caveat: the generated unique name could collide with an abstract type of 
--   the same name, this will cause an invalid Isabelle theory.
getStrlType :: M.Map TypeStr TypeName -> [TypeStr] -> Type t a -> Type t a
getStrlType tsmap table (TSum ts) =
  let tstr = VariantStr (P.map fst ts)
      tps = P.map (fst . snd) ts
  in case M.lookup tstr tsmap of
    Nothing ->
      let idx = findIndex tstr table
      in TCon ('T':show idx) tps Unboxed
    Just tn -> TCon tn tps Unboxed
-- TODO: recPars part of type strings?
getStrlType tsmap table (TRecord _ fs s) =
  let tstr = RecordStr (P.map fst fs)
      tps = P.map (fst . snd) fs
  in case M.lookup tstr tsmap of
    Nothing ->
      let idx = findIndex tstr table
      in TCon ('T':show idx) tps (__fixme (const () <$> s))
        -- The DataLayout is not included in shallow embeddings /mdimeglio zilinc
    Just tn -> TCon tn tps (__fixme (const () <$> s))
        -- The DataLayout is not included in shallow embeddings /mdimeglio zilinc
getStrlType _ _ t = t

type ST = State [TypeStr]

-- | Collects all the types used in a Cogent program.
st :: [Definition PosTypedExpr (VarName, Maybe VarName) b] -> [TypeStr]
st ds = execState (stDefinitions ds) []

stDefinitions :: [Definition PosTypedExpr (VarName, Maybe VarName) b] -> ST ()
stDefinitions = mapM_ stDefinition

-- (Since desugaring, the RHSes have been unfolded already)
-- This is not true anymore, but since all TypeDefs are scanned, it does not matter.

stDefinition :: Definition PosTypedExpr (VarName, Maybe VarName) b -> ST ()
stDefinition (FunDef  _ fn ts ls ti to e) = stExpr e  -- NOTE: `ti' and `to' will be included in `e', so no need to scan them / zilinc
stDefinition (AbsDecl _ fn ts ls ti to) = stType ti >> stType to
stDefinition (TypeDef tn ts (Just t)) = stType t
stDefinition (TypeDef tn ts Nothing) = return ()

stExpr :: PosTypedExpr t v (VarName, Maybe VarName) b -> ST ()
stExpr (TE t e) = stExpr' e >> stType t
  where
    stExpr' (Variable v _)   = return ()
    stExpr' (Fun fn ts _ _ _) = __fixme $ mapM_ stType ts
    stExpr' (Op opr es _)    = mapM_ stExpr es
    stExpr' (App e1 e2 _)    = stExpr e1 >> stExpr e2
    stExpr' (Con cn e _ _)   = stExpr e
    stExpr' (Unit _)         = return ()
    stExpr' (ILit i pt _)    = return ()
    stExpr' (SLit s _)       = return ()
#ifdef BUILTIN_ARRAYS
    stExpr' (ALit es)      = mapM_ stExpr es
    stExpr' (ArrayIndex e1 e2) = mapM_ stExpr [e1,e2]
    stExpr' (Pop _ e1 e2)  = stExpr e1 >> stExpr e2
    stExpr' (Singleton e)  = stExpr e
    stExpr' (ArrayMap2 (_,e) (e1,e2)) = stExpr e >> mapM_ stExpr [e1,e2]
    stExpr' (ArrayTake _ e1 _ e2)     = stExpr e1 >> stExpr e2
    stExpr' (ArrayPut e1 e2 e3)       = mapM_ stExpr [e1,e2,e3]
#endif
    stExpr' (Let a e1 e2 _) = stExpr e1 >> stExpr e2
    stExpr' (LetBang vs a e1 e2 _) = stExpr e1 >> stExpr e2
    stExpr' (Tuple e1 e2 _) = stExpr e1 >> stExpr e2
    stExpr' (Struct fs _)   = mapM_ (stExpr . snd) fs
    stExpr' (If e1 e2 e3 _) = mapM_ stExpr [e1,e2,e3]
    stExpr' (Case e tn (l1,a1,e1) (l2,a2,e2) _) = stExpr e >> mapM_ stExpr [e1,e2]
    stExpr' (Esac e _)      = stExpr e
    stExpr' (Split a e1 e2 _)  = stExpr e1 >> stExpr e2
    stExpr' (Member rec fld _) = stExpr rec
    stExpr' (Take a rec fld e _) = stExpr rec >> stExpr e
    stExpr' (Put rec fld v _)  = stExpr rec >> stExpr v
    stExpr' (Promote ty e _)   = stExpr e
    stExpr' (Cast    ty e _)   = stExpr e

-- | Add types to the table if not existing.
stType :: Type t b -> ST ()
stType (toTypeStr -> ts) = forM_ ts $ \t -> do
  table <- get
  case lookupTypeStr t table of
    Nothing -> put $ t:table
    Just _  -> return ()

findIndex :: TypeStr -> [TypeStr] -> Int
findIndex = (fromJust .) . L.elemIndex

lookupTypeStr :: TypeStr -> [TypeStr] -> Maybe TypeStr
lookupTypeStr = find . (==)

-- For debugging
printTable :: [TypeStr] -> String
printTable table = unlines $ P.zipWith (\i t -> 'T':show i ++ " :-> " ++ show t) [1::Int ..] table

