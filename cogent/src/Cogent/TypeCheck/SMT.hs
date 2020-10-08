
--
-- Copyright 2019, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.TypeCheck.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax as S
import Cogent.Common.Types
import Cogent.PrettyPrint (indent')
import Cogent.TypeCheck.Base
import Cogent.Surface as S

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.State
import Data.IntMap as IM
import Data.Map    as M
import Data.SBV as SMT
import Data.SBV.Dynamic as SMT
#if MIN_VERSION_sbv(8,8,0)
import Data.SBV.Internals as SMT
#endif
import Lens.Micro.Mtl
import Lens.Micro.TH
import Text.PrettyPrint.ANSI.Leijen (pretty)
import Prelude as P


data SmtTransState = SmtTransState { _unifs :: IntMap SVal
                                   , _vars  :: Map String SVal
                                   }

makeLenses ''SmtTransState

type SmtTransM = StateT SmtTransState Symbolic

typeToSmt :: TCType -> SMT.Kind
typeToSmt (T (TCon "Bool" [] Unboxed)) = KBool
typeToSmt (T (TCon "String" [] Unboxed)) = KString
typeToSmt (T (TCon n [] Unboxed))
  = let w = if | n == "U8"  -> 8
               | n == "U16" -> 16
               | n == "U32" -> 32
               | n == "U64" -> 64
     in KBounded False w
typeToSmt (T (TTuple ts))  = KTuple $ P.map typeToSmt ts
typeToSmt (T (TUnit))      = KTuple []
typeToSmt t = __impossible $ "typeToSmt: unsupported type in SMT:\n" ++ show (indent' $ pretty t)

sexprToSmt :: TCSExpr -> SmtTransM SVal
sexprToSmt (SU t x) = do
  m <- use unifs
  case IM.lookup x m of
    Nothing -> do sv <- mkQSymVar SMT.EX ('?':show x) (typeToSmt t)
                  unifs %= (IM.insert x sv)
                  return sv
    Just sv -> return sv
sexprToSmt (SE t (PrimOp op [e])) = (liftA $ uopToSmt op) (sexprToSmt e)
sexprToSmt (SE t (PrimOp op [e1,e2])) = (liftA2 $ bopToSmt op) (sexprToSmt e1) (sexprToSmt e2)
sexprToSmt (SE t (Var vn)) = do
  m <- use vars
  case M.lookup vn m of
    Nothing -> do sv <- mkQSymVar SMT.ALL vn (typeToSmt t)
                  vars %= (M.insert vn sv)
                  return sv
    Just sv -> return sv
  -- NOTE: For uninterpreted constants, SMT doesn't know anything about it, and they behave sort
  --       of like existentials, that if it's *possible* that something is true, then it's satisfiable.
  --       Only when it derives a contradiction it says it's unsat. / zilinc
  -- XXX | return $ svUninterpreted (typeToSmt t) vn Nothing []
sexprToSmt (SE t (IntLit i)) = return $ svInteger (typeToSmt t) i
sexprToSmt (SE t (BoolLit b)) = return $ svBool b
sexprToSmt (SE t (If e _ th el)) = (liftA3 svIte) (sexprToSmt e) (sexprToSmt th) (sexprToSmt el)
sexprToSmt (SE t (Upcast e)) = sexprToSmt e
sexprToSmt (SE t (Annot e _)) = sexprToSmt e
sexprToSmt e = __todo $ "sexprToSmt: unsupported expression in SMT:\n" ++ show (indent' $ pretty e)

-- type SmtM a = StateT (UVars, EVars) V.Symbolic a

bopToSmt :: OpName -> (SVal -> SVal -> SVal)
bopToSmt = \case
  "+"   -> svPlus
  "-"   -> svMinus
  "*"   -> svTimes
  "/"   -> svDivide
  "%"   -> svQuot  -- NOTE: the behaviour of `svDivide` and `svQuot` here. / zilinc
                   -- http://hackage.haskell.org/package/sbv-8.5/docs/Data-SBV-Dynamic.html#v:svDivide
  "&&"  -> svAnd
  "||"  -> svOr
  ".&." -> svAnd
  ".|." -> svOr
  ".^." -> svXOr
  "<<"  -> svShiftLeft
  ">>"  -> svShiftRight
  "=="  -> svEqual
  "/="  -> svNotEqual
  ">"   -> svGreaterThan
  "<"   -> svLessThan
  ">="  -> svGreaterEq
  "<="  -> svLessEq

uopToSmt :: OpName -> (SVal -> SVal)
uopToSmt = \case
  "not"        -> svNot
  "complement" -> svNot


-- ----------------------------------------------------------------------------
-- Helpers
--

mkSymVar :: String -> SMT.Kind -> SmtTransM SVal
#if MIN_VERSION_sbv(8,8,0)
mkSymVar nm k = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar Nothing) k (Just nm)
#else
mkSymVar nm k = symbolicEnv >>= liftIO . svMkSymVar Nothing k (Just nm)
#endif


mkQSymVar :: SMT.Quantifier -> String -> SMT.Kind -> SmtTransM SVal
#if MIN_VERSION_sbv(8,8,0)
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just q)) k (Just nm)
#else
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (Just q) k (Just nm)
#endif

bvAnd :: [SVal] -> SVal
bvAnd = P.foldr (svAnd) svTrue


