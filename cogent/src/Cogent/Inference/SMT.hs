{--
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
import Lens.Micro.Mtl
import Lens.Micro.TH
import Text.PrettyPrint.ANSI.Leijen (pretty)
import Prelude as P


data SmtTransState = SmtTransState { _unifs :: IntMap SVal
                                   , _vars  :: Map String SVal
                                   , _fresh :: Int
                                   }

makeLenses ''SmtTransState

type SmtTransM = StateT SmtTransState Symbolic

typeToSmt :: Type t b -> SmtTransM SMT.Kind
typeToSmt t = freshSort >>= \s -> return (KUninterpreted s (Left s))

primIntToSmt :: PrimInt -> SmtTransM SMT.Kind
primIntToSmt Boolean = KBool
primIntToSmt u
  = let w = if | u == U8  -> 8
               | u == U16 -> 16
               | u == U32 -> 32
               | u == U64 -> 64
      in return $ KBounded False w


lexprToSmt :: LExpr t b -> SmtTransM SVal
lexprToSmt (LVariable (t, b)) = LVariable (Suc t, b)
lexprToSmt (LFun fn ts ls) = LFun fn (map upshiftVarType ts) ls
lexprToSmt (LOp opr es) = LOp opr (map upshiftVarLExpr es)
lexprToSmt (LApp a b) = LApp (upshiftVarLExpr a) (upshiftVarLExpr b)
lexprToSmt (LCon tn e t) = LCon tn (upshiftVarLExpr e) (upshiftVarType t)
lexprToSmt (LUnit) = 
lexprToSmt (LILit i pt) = svInteger (primIntToSmt pt) i
lexprToSmt (LSLit s) = 
lexprToSmt (LLet a e1 e2) = LLet a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
lexprToSmt (LLetBang bs a e1 e2) = LLetBang bs a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
lexprToSmt (LTuple e1 e2) = LTuple (upshiftVarLExpr e1) (upshiftVarLExpr e2)
lexprToSmt (LStruct fs) = LStruct $ map (\(fn, e) -> (fn, upshiftVarLExpr e)) fs
lexprToSmt (LIf c t e) = LIf (upshiftVarLExpr c) (upshiftVarLExpr t) (upshiftVarLExpr e)
lexprToSmt (LCase e tn (v1, a1) (v2, a2)) = LCase (upshiftVarLExpr e) tn (v1, upshiftVarLExpr a1) (v2, upshiftVarLExpr a2)
lexprToSmt (LEsac e) = LEsac $ upshiftVarLExpr e
lexprToSmt (LSplit (v1, v2) e1 e2) = LSplit (v1, v2) (upshiftVarLExpr e1) (upshiftVarLExpr e2)
lexprToSmt (LMember x f) = LMember (upshiftVarLExpr x) f
-- upshiftVarLExpr (LTake (a,b) rec f e) = LTake (a,b) rec f (upshiftVarLExpr e)
-- upshiftVarLExpr (LPut rec f v) = LPut rec f (upshiftVarLExpr v)
lexprToSmt (LPromote t e) = LPromote (upshiftVarType t) (upshiftVarLExpr e)
lexprToSmt (LCast t e) = LCast (upshiftVarType t) (upshiftVarLExpr e)

--}