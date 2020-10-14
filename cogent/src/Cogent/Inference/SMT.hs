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

smtProveVerbose :: Symbolic SVal -> Symbolic SVal -> Symbolic SVal -> IO (Bool, Bool)
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
smtProve :: Symbolic SVal -> Symbolic SVal -> Symbolic SVal -> IO (Bool, Bool)
smtProve p q e = smtProveVerbose p q e