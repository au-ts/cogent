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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Cogent.Inference.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax as S
import Cogent.Common.Types
import Cogent.Core
import Cogent.PrettyPrint (indent', warn)

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State
import Data.Fin
import Data.IntMap as IM
import Data.Map    as M
import Data.Maybe (fromMaybe)
import Data.SBV as SMT hiding (proveWith)
import Data.SBV.Dynamic as SMT
import Data.Vec hiding (repeat, splitAt, length, zipWith, zip, unzip)
import Lens.Micro.Mtl
import Lens.Micro.TH
import Text.PrettyPrint.ANSI.Leijen (pretty)
import Prelude as P
import qualified Text.PrettyPrint.ANSI.Leijen as L

-- State from the core TC monad
type TcVec   t v b = Vec v (Maybe (Type t b))
type TcState t v b = (TcVec t v b, [LExpr t b], Int)

-- Int is the fresh variable count
type SmtStateM = StateT Int Symbolic

getSmtExpression :: String -> TcVec t v b -> [LExpr t b] -> LExpr t b -> LExpr t b -> Symbolic SVal
getSmtExpression dir v e p q = do
  (e', se) <- runStateT (extract v e) 0 
  (p', sp) <- runStateT (lexprToSmt v p) se
  (q', sp) <- runStateT (lexprToSmt v q) sp
  return $ case dir of
    "Subtype"   -> (svOr (svNot (svAnd p' e')) q') -- ~(P ^ E) v Q
    "Supertype" -> (svOr (svNot (svAnd q' e')) p') -- ~(Q ^ E) v P

extract :: TcVec t v b -> [LExpr t b] -> SmtStateM SVal
extract v ls = do
                  initialSVal <- return $ return svTrue
                  vecPreds <- P.foldr (extractVec v) initialSVal v
                  ctxPreds <- P.foldr (extractLExprs v) initialSVal ls
                  return $ svAnd vecPreds ctxPreds

extractVec :: TcVec t v b -> Maybe (Type t b) -> SmtStateM SVal -> SmtStateM SVal
extractVec vec t acc = case t of
  Just (TRefine _ p) -> svAnd <$> acc <*> (lexprToSmt vec p)
  _ -> acc

extractLExprs :: TcVec t v b -> LExpr t b -> SmtStateM SVal -> SmtStateM SVal
extractLExprs vec l acc = svAnd <$> acc <*> lexprToSmt vec l

strToPrimInt:: [Char] -> PrimInt
strToPrimInt "U8"  = U8
strToPrimInt "U16" = U16
strToPrimInt "U32" = U32
strToPrimInt "U64" = U64

primIntToSmt :: PrimInt -> SMT.Kind
-- it shouldn't be bool, we do bool case first
-- primIntToSmt Boolean = return KBool
primIntToSmt u
  = let w = if | u == U8  -> 8
               | u == U16 -> 16
               | u == U32 -> 32
               | u == U64 -> 64
      in KBounded False w

bopToSmt :: Op -> (SVal -> SVal -> SVal)
bopToSmt Plus = svPlus
bopToSmt Minus = svMinus
bopToSmt Times = svTimes
bopToSmt Divide = svDivide
bopToSmt Mod = svRem -- care with the defn, x rem 0 = 0
bopToSmt And = svAnd
bopToSmt Or = svOr 
bopToSmt Gt = svGreaterThan 
bopToSmt Lt = svLessThan
bopToSmt Le = svLessEq
bopToSmt Ge = svGreaterEq
bopToSmt Eq = svEqual
bopToSmt NEq = svNotEqual
bopToSmt BitAnd = svAnd
bopToSmt BitOr = svOr
bopToSmt BitXor = svXOr
bopToSmt LShift = svShiftLeft
bopToSmt RShift = svShiftRight

uopToSmt :: Op -> (SVal -> SVal)
uopToSmt Not = svNot
uopToSmt Complement = svNot

-- lexprToSmt :: LExpr t b -> TC t v b (Symbolic SVal)
-- lexprToSmt :: (MonadState (TcState t v b) m) => LExpr t b -> m (SmtStateM SVal)
lexprToSmt :: TcVec t v b -> LExpr t b -> SmtStateM SVal
-- lexprToSmt (LVariable (t, vn)) = do
-- lexprToSmt (LFun fn ts ls) = LFun fn (map upshiftVarType ts) ls
lexprToSmt vec (LOp op [e]) = (liftA $ uopToSmt op) $ lexprToSmt vec e
lexprToSmt vec (LOp op [e1,e2]) = (liftA2 $ bopToSmt op) (lexprToSmt vec e1) (lexprToSmt vec e2)
-- lexprToSmt (LApp a b) = LApp (upshiftVarLExpr a) (upshiftVarLExpr b)
-- lexprToSmt (LCon tn e t) = LCon tn (upshiftVarLExpr e) (upshiftVarType t)
-- lexprToSmt (LUnit) =
lexprToSmt vec (LILit i Boolean)
  = case i of
      0 -> return svFalse
      1 -> return svTrue
lexprToSmt vec (LILit i pt) = return $ svInteger (primIntToSmt pt) i
lexprToSmt vec (LSLit s) = return $ svUninterpreted KString "" Nothing []
-- lexprToSmt (LLet a e1 e2) = LLet a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LLetBang bs a e1 e2) = LLetBang bs a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LTuple e1 e2) = LTuple (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LStruct fs) = LStruct $ map (\(fn, e) -> (fn, upshiftVarLExpr e)) fs
lexprToSmt vec (LIf c t e) = do
    c' <- lexprToSmt vec c
    t' <- lexprToSmt vec t
    e' <- lexprToSmt vec e
    let thenBranch = svOr (svNot c') t'   -- c => t
        elseBranch = svOr c' e'           -- ~c => e
    return $ svAnd thenBranch elseBranch 
-- lexprToSmt (LCase e tn (v1, a1) (v2, a2)) = LCase (upshiftVarLExpr e) tn (v1, upshiftVarLExpr a1) (v2, upshiftVarLExpr a2)
-- lexprToSmt (LEsac e) = LEsac $ upshiftVarLExpr e
-- lexprToSmt (LSplit (v1, v2) e1 e2) = LSplit (v1, v2) (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LMember x f) = LMember (upshiftVarLExpr x) f
-- lexprToSmt (LTake (a,b) rec f e) = LTake (a,b) rec f (upshiftVarLExpr e)
-- lexprToSmt (LPut rec f v) = LPut rec f (upshiftVarLExpr v)
-- lexprToSmt (LPromote t e) = LPromote (upshiftVarType t) (upshiftVarLExpr e)
-- lexprToSmt (LCast t e) = LCast (upshiftVarType t) (upshiftVarLExpr e)
lexprToSmt _ _ = freshVal >>= \vn -> return $ svUninterpreted KString vn Nothing []

-- toBaseType :: Type t b -> Type t b
-- toBaseType (TRefine t _) = t
-- toBaseType x = x

-- typeToSmt :: Type t b -> TC t v b (Kind)
-- typeToSmt :: (MonadState (TcState t v b) m, t ~ v) => Type t b -> m (SmtStateM SMT.Kind)
typeToSmt :: (t ~ v) => TcVec t v b -> Type t b -> SmtStateM SMT.Kind
typeToSmt vec (TVar v) = do
    case (vec `at` v) of
      Just t' -> typeToSmt vec t'
typeToSmt vec (TVarBang v) = varIndexToSmt vec v
typeToSmt vec (TVarUnboxed v) = varIndexToSmt vec v
typeToSmt vec (TPrim pt) = return $ primIntToSmt pt
-- typeToSmt (TString) = typename "String"
typeToSmt vec (TUnit) = return $ KTuple []
typeToSmt vec (TProduct t1 t2) = do 
  ts <- mapM (typeToSmt vec) [t1, t2]
  return $ KTuple ts
-- typeToSmt (TSum alts) = variant (map (\(n,(t,b)) -> tagname n L.<> prettyTaken b <+> pretty t) alts)
-- typeToSmt (TFun t1 t2) = prettyT' t1 <+> typesymbol "->" <+> pretty t2
-- typeToSmt (TRecord rp fs s) = pretty rp <+> record (map (\(f,(t,b)) -> fieldname f <+> symbol ":" L.<> prettyTaken b <+> pretty t) fs)
typeToSmt vec (TCon "Bool" [] Unboxed) = return $ KBool
typeToSmt vec (TCon "String" [] Unboxed) = return $ KString
typeToSmt vec (TCon n [] Unboxed) = return $ primIntToSmt $ strToPrimInt n
typeToSmt vec (TRefine t _) = typeToSmt vec t
typeToSmt vec t = freshVal >>= \s -> return (KUninterpreted s (Left s)) -- check

varIndexToSmt :: (t ~ v) => TcVec t v b -> Fin t -> SmtStateM SMT.Kind
varIndexToSmt vec i = do
  case (vec `at` i) of
    Just t' -> typeToSmt vec t'

smtProveVerbose :: TcVec t v b -> [LExpr t b] -> LExpr t b -> LExpr t b -> IO (Bool, Bool)
smtProveVerbose v ls p q = 
  let solver = z3 { verbose = __cogent_ddump_smt
                   , redirectVerbose = Just $ fromMaybe "/dev/stderr" __cogent_ddump_to_file
                   } in
  do
    let toProve1 = getSmtExpression "Subtype" v ls p q
        toProve2 = getSmtExpression "Supertype" v ls p q
    smtRes1 <- liftIO (proveWith solver toProve1) >>= \case
      ThmResult (Satisfiable _ _) -> return True
      _ -> return False
    smtRes2 <- liftIO (proveWith solver toProve2) >>= \case
      ThmResult (Satisfiable _ _) -> return True
      _ -> return False
    return (smtRes1, smtRes2)

mkQSymVar :: SMT.Quantifier -> String -> SMT.Kind -> Symbolic SVal
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (Just q) k (Just nm)

freshVal :: SmtStateM String
freshVal = do
  i <- get 
  modify succ
  return ("smt_val_" ++ show i)