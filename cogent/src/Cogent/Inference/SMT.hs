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

module Cogent.Inference.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax as S
import Cogent.Common.Types
import Cogent.Core
import Cogent.PrettyPrint (indent', warn)

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.State
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


-- data SmtTransState = SmtTransState {  
--                                    _vars  :: Map String SVal
--                                    , _fresh :: Int
--                                    }

-- makeLenses ''SmtTransState

-- type SmtTransM = StateT SmtTransState Symbolic

typeToSmt :: Type t b -> Symbolic SMT.Kind
-- typeToSmt (TVar v) = prettyT v
-- typeToSmt (TVarBang v) = prettyT v L.<> typesymbol "!"
-- typeToSmt (TVarUnboxed v) = typesymbol "#" <> prettyT v
typeToSmt (TPrim pt) = primIntToSmt pt
-- typeToSmt (TString) = typename "String"
typeToSmt (TUnit) = return $ KTuple []
typeToSmt (TProduct t1 t2) = KTuple <$> mapM typeToSmt [t1, t2]
-- typeToSmt (TSum alts) = variant (map (\(n,(t,b)) -> tagname n L.<> prettyTaken b <+> pretty t) alts)
-- typeToSmt (TFun t1 t2) = prettyT' t1 <+> typesymbol "->" <+> pretty t2
-- typeToSmt (TRecord rp fs s) = pretty rp <+> record (map (\(f,(t,b)) -> fieldname f <+> symbol ":" L.<> prettyTaken b <+> pretty t) fs)
typeToSmt (TCon "Bool" [] Unboxed) = return KBool
typeToSmt (TCon "String" [] Unboxed) = return KString
typeToSmt (TCon n [] Unboxed) = primIntToSmt $ strToPrimInt n
-- typeToSmt t = freshSort >>= \s -> return (KUninterpreted s (Left s))

strToPrimInt:: [Char] -> PrimInt
strToPrimInt "U8"  = U8
strToPrimInt "U16" = U16
strToPrimInt "U32" = U32
strToPrimInt "U64" = U64

primIntToSmt :: PrimInt -> Symbolic SMT.Kind
-- it shouldn't be bool, we do bool case first
-- primIntToSmt Boolean = return KBool
primIntToSmt u
  = let w = if | u == U8  -> 8
               | u == U16 -> 16
               | u == U32 -> 32
               | u == U64 -> 64
      in return $ KBounded False w

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

lexprToSmt :: LExpr t b -> Symbolic SVal
{--
lexprToSmt (LVariable (t, vn)) = do
  m <- use vars
  case M.lookup vn m of
    Nothing -> do t' <- typeToSmt t
                  sv <- mkQSymVar SMT.ALL vn t'
                  vars %= (M.insert vn sv)
                  return sv
    Just sv -> return sv
--}
-- lexprToSmt (LFun fn ts ls) = LFun fn (map upshiftVarType ts) ls
lexprToSmt (LOp op [e]) = (liftA $ uopToSmt op) (lexprToSmt e)
lexprToSmt (LOp op [e1,e2]) = (liftA2 $ bopToSmt op) (lexprToSmt e1) (lexprToSmt e2) 
-- lexprToSmt (LApp a b) = LApp (upshiftVarLExpr a) (upshiftVarLExpr b)
-- lexprToSmt (LCon tn e t) = LCon tn (upshiftVarLExpr e) (upshiftVarType t)
-- lexprToSmt (LUnit) = 
lexprToSmt (LILit i Boolean)
  = return $ case i of
      0 -> svFalse
      1 -> svTrue
lexprToSmt (LILit i pt) = svInteger <$> (primIntToSmt pt) <*> pure i
lexprToSmt (LSLit s) = return $ svUninterpreted KString "" Nothing []
-- lexprToSmt (LLet a e1 e2) = LLet a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LLetBang bs a e1 e2) = LLetBang bs a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LTuple e1 e2) = LTuple (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LStruct fs) = LStruct $ map (\(fn, e) -> (fn, upshiftVarLExpr e)) fs
-- lexprToSmt (LIf c t e) = LIf (upshiftVarLExpr c) (upshiftVarLExpr t) (upshiftVarLExpr e)
-- lexprToSmt (LCase e tn (v1, a1) (v2, a2)) = LCase (upshiftVarLExpr e) tn (v1, upshiftVarLExpr a1) (v2, upshiftVarLExpr a2)
-- lexprToSmt (LEsac e) = LEsac $ upshiftVarLExpr e
-- lexprToSmt (LSplit (v1, v2) e1 e2) = LSplit (v1, v2) (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LMember x f) = LMember (upshiftVarLExpr x) f
-- lexprToSmt (LTake (a,b) rec f e) = LTake (a,b) rec f (upshiftVarLExpr e)
-- lexprToSmt (LPut rec f v) = LPut rec f (upshiftVarLExpr v)
-- lexprToSmt (LPromote t e) = LPromote (upshiftVarType t) (upshiftVarLExpr e)
-- lexprToSmt (LCast t e) = LCast (upshiftVarType t) (upshiftVarLExpr e)

smtProveVerbose :: Symbolic SVal -> Symbolic SVal -> [Symbolic SVal] -> IO (Bool, Bool)
smtProveVerbose p q e = 
  let solver = z3 { verbose = __cogent_ddump_smt
                   , redirectVerbose = Just $ fromMaybe "/dev/stderr" __cogent_ddump_to_file
                   } in
  do
    smtRes1 <- proveWith (solver) (p)
    smtRes2 <- proveWith (solver) (q)
    let 
      val1 = case smtRes1 of
        ThmResult (Satisfiable _ _) -> True 
        _ -> False
      val2 = case smtRes2 of
        ThmResult (Satisfiable _ _) -> True 
        _ -> False
    return (val1, val2)
-- what does delta satisfiable mean?

-- inputs: p, q, preds from context 
-- result: (first is a subtype of second, second is a subtype of first)
-- returns false if we can't prove true
smtProve :: Symbolic SVal -> Symbolic SVal -> [Symbolic SVal] -> IO (Bool, Bool)
smtProve p q e = smtProveVerbose p q e