--
-- Copyright 2020, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

module Cogent.LLVM.Expr (exprToLLVM, castVal, constUndef) where

-- This module converts Cogent expressions into LLVM IR via the IRBuilder
-- monadic interface

import Cogent.Common.Syntax as Sy (CoreFunName (unCoreFunName), Op (..))
import Cogent.Common.Types (PrimInt (Boolean))
import Cogent.Core as Core
import Cogent.Dargent.Util (primIntSizeBits)
import Cogent.LLVM.CodeGen (Codegen, bind, tagIndex, var)
import Cogent.LLVM.Types (maxMember, tagType, toLLVMType, typeSize)
import Cogent.Util (toCName)
import Data.Foldable (foldlM, foldrM)
import LLVM.AST as AST (Instruction (LShr), Operand (ConstantOperand), Type, mkName)
import qualified LLVM.AST.Constant as C
import LLVM.AST.IntegerPredicate as P (IntegerPredicate (EQ, NE, UGE, UGT, ULE, ULT))
import LLVM.AST.Type (i8, ptr)
import LLVM.AST.Typed (typeOf)
import LLVM.IRBuilder.Constant (int32, int8)
import LLVM.IRBuilder.Instruction as IR
import LLVM.IRBuilder.Monad (block, currentBlock, emitInstr, freshName, named)

-- Given a single typed expression, and a list of in-scope variables, create the
-- LLVM IR to compute the expression
exprToLLVM :: TypedExpr t v a b -> Codegen Operand
-- Unit is represented as a byte of arbitrary value
exprToLLVM (TE _ Unit) = pure $ int8 0
-- Integer literals are mapped to LLVM integer types
exprToLLVM (TE _ (ILit int p)) = pure $ constInt (primIntSizeBits p) int
-- For string literals use a byte array of ASCII values
exprToLLVM (TE _ (SLit str)) = freshName "str" >>= (fmap ConstantOperand . globalStringPtr str)
-- For binary operators evaluate each operand and then the result
exprToLLVM (TE t (Op op [a, b])) = do
    oa <- exprToLLVM a
    ob <- exprToLLVM b
    res <- toLLVMOp op oa ob
    case t of
        -- Coerce boolean results back to a full byte rather than a single bit
        TPrim Boolean -> if typeOf res == i8 then pure res else zext res i8
        _ -> pure res
-- Complement must be implemented by xor with an equal-length value consisting
-- entirely of 1 bits
exprToLLVM (TE t (Op Sy.Complement [a])) = do
    oa <- exprToLLVM a
    xor oa (constInt (typeSize t) (-1))
-- We want not to return 1 for the case of 0, and 0 otherwise, so we can't use xor again
exprToLLVM (TE _ (Op Sy.Not [a])) = do
    oa <- exprToLLVM a
    res <- icmp P.EQ oa (int8 0)
    zext res i8
-- For record member access just load the member and yield the field value
exprToLLVM (TE _ (Member recd fld)) = snd <$> loadMember recd fld
-- Take requires us to bind the field value and also the record value as new
-- variables which we can use to evaluate the body of the expression
exprToLLVM (TE _ (Take _ recd fld body)) = do
    (recv, fldv) <- loadMember recd fld
    foldr bind (exprToLLVM body) [recv, fldv]
-- To put a value into a record, evaluate the record and the value, then for:
--  - unboxed records: simply use the insertvalue IR instruction
--  - boxed records: calculate the field pointer and store the value
-- In either case the yielded result is the updated record
exprToLLVM (TE _ (Put recd fld val)) = do
    recv <- exprToLLVM recd
    v <- exprToLLVM val
    if isUnboxed (exprType recd)
        then insertValue recv v [toEnum fld]
        else do
            fldp <- gep recv [int32 0, int32 (toEnum fld)]
            store fldp 0 v
            pure recv
-- For a let binding we evalaute the value using the current vars, and then
-- evaluate the body using the updated set of variables
exprToLLVM (TE _ (Let _ val body)) = exprToLLVM val >>= flip bind (exprToLLVM body)
-- let! is the same as let
exprToLLVM (TE t (LetBang _ a val body)) = exprToLLVM (TE t (Let a val body))
-- Promote is syntactic only
exprToLLVM (TE _ (Promote _ e)) = exprToLLVM e
-- To upcast, zero extend the evaluated expression as needed
exprToLLVM (TE _ (Cast t e)) = do
    v <- exprToLLVM e
    toLLVMType t >>= zext v
-- Constructing a sumtype consists of inserting a 32bit tag, followed by a value
-- The value must be casted to the 'maximum member' of the variant beforehand
exprToLLVM (TE t (Con tag e (TSum ts))) = do
    tagv <- tagIndex tag
    t' <- toLLVMType t
    tagged <- insertValue (constUndef t') tagv [0]
    v <- exprToLLVM e
    case e of
        -- Don't bother doing anything for constructors with no arguments
        TE TUnit _ -> pure tagged
        _ -> do
            casted <- toLLVMType (maxMember ts) >>= upcastVal v
            insertValue tagged casted [1]
-- The binary case expression compares the tag of a variant with the desired tag
-- Branching is used for each alternative:
--  - if the tag matches, evaluate the true branch with the variant's value
--    bound as a new variable
--  - otherwise, evaluate the false branch with the whole variant bound
-- The phi instruction is used to yield the final result based on the branch
exprToLLVM (TE _ (Case e@(TE rt _) tag (_, _, tb) (_, _, fb))) = mdo
    variant <- exprToLLVM e
    tagv <- extractValue variant [0]
    cond <- tagIndex tag >>= icmp P.EQ tagv
    condBr cond brMatch brNotMatch
    brMatch <- block `named` "case.true"
    v <- extractValue variant [1]
    casted <- toLLVMType (tagType rt tag) >>= castVal v
    valTrue <- bind casted $ exprToLLVM tb
    brMatch' <- currentBlock
    br brExit
    brNotMatch <- block `named` "case.false"
    valFalse <- bind variant $ exprToLLVM fb
    brNotMatch' <- currentBlock
    br brExit
    brExit <- block `named` "case.done"
    phi [(valTrue, brMatch'), (valFalse, brNotMatch')]
-- Esac requires us to extract the value from the variant and cast it
exprToLLVM (TE t (Esac e)) = do
    variant <- exprToLLVM e
    v <- extractValue variant [1]
    toLLVMType t >>= castVal v
-- For if the condition must be evaluated and then branching is used to evaluate
-- the true or false branch
-- The phi instruction is used to yield the final result based on the branch
exprToLLVM (TE _ (If cd tb fb)) = mdo
    v <- exprToLLVM cd
    cond <- icmp NE v (int8 0)
    condBr cond brTrue brFalse
    brTrue <- block `named` "if.true"
    valTrue <- exprToLLVM tb
    brTrue' <- currentBlock
    br brExit
    brFalse <- block `named` "if.false"
    valFalse <- exprToLLVM fb
    brFalse' <- currentBlock
    br brExit
    brExit <- block `named` "if.done"
    phi [(valTrue, brTrue'), (valFalse, brFalse')]
-- A struct expression is constructed by iteratively inserting field values
exprToLLVM (TE t (Struct flds)) = do
    t' <- toLLVMType t
    foldlM
        (\struct (i, v) -> exprToLLVM v >>= \value -> insertValue struct value [i])
        (constUndef t')
        [(i, snd fld) | (i, fld) <- zip [0 ..] flds]
-- Use the variable index to look it up in the current variable context
exprToLLVM (TE _ (Variable (idx, _))) = var idx
-- Functions must be references to something already defined globally
exprToLLVM (TE t (Fun f _ _ _)) = do
    ft <- toLLVMType t
    pure $
        ConstantOperand $
            C.GlobalReference
                ft
                -- append .llvm to end of fn name for non-wrapped version
                ((mkName . (++ ".llvm") . toCName . unCoreFunName) f)
-- To apply a function, evaluate the argument and function then call it
exprToLLVM (TE _ (App f a)) = do
    arg <- exprToLLVM a
    fun <- exprToLLVM f
    call fun [(arg, [])]
exprToLLVM _ = error "unknown expression"

-- Map a Cogent binary operator to LLVM binary operators
toLLVMOp :: Sy.Op -> (Operand -> Operand -> Codegen Operand)
toLLVMOp Sy.Plus = add
toLLVMOp Sy.Minus = sub
toLLVMOp Sy.Times = mul
toLLVMOp Sy.Divide = udiv
toLLVMOp Sy.Mod = urem
toLLVMOp Sy.And = IR.and
toLLVMOp Sy.Or = IR.or
toLLVMOp Sy.Gt = icmp UGT
toLLVMOp Sy.Lt = icmp ULT
toLLVMOp Sy.Le = icmp ULE
toLLVMOp Sy.Ge = icmp UGE
toLLVMOp Sy.Eq = icmp P.EQ
toLLVMOp Sy.NEq = icmp NE
toLLVMOp Sy.BitAnd = IR.and
toLLVMOp Sy.BitOr = IR.or
toLLVMOp Sy.BitXor = xor
toLLVMOp Sy.LShift = shl
-- we can't use the lshr helper because we don't want 'exact' enabled
toLLVMOp Sy.RShift = \a b -> emitInstr (typeOf a) $ LShr False a b []
toLLVMOp _ = error "not a binary operator"

-- Cast a value by temporarily storing it on the stack and casting the pointer
castVal :: Operand -> AST.Type -> Codegen Operand
castVal o t = do
    ptr_o <- alloca (typeOf o) Nothing 4
    ptr_t <- bitcast ptr_o (ptr t)
    store ptr_o 1 o
    load ptr_t 1

-- Version of the above safe for upcasts
upcastVal :: Operand -> AST.Type -> Codegen Operand
upcastVal o t = do
    ptr_t <- alloca t Nothing 0
    ptr_o <- bitcast ptr_t (ptr (typeOf o))
    store ptr_o 1 o
    load ptr_t 1

-- Load a field from a record, and yield both the record and the field value
-- For unboxed records, this is just an extractvalue instruction, for boxed it
-- requires calculating the field pointer and then loading the value
loadMember :: TypedExpr t v a b -> Int -> Codegen (Operand, Operand)
loadMember recd fld = do
    recv <- exprToLLVM recd
    fldv <-
        if isUnboxed (exprType recd)
            then extractValue recv [toEnum fld]
            else gep recv [int32 0, int32 (toEnum fld)] >>= \fldp -> load fldp 0
    pure (recv, fldv)

-- Helper to construct integer with a certain size and value
constInt :: Integer -> Integer -> Operand
constInt n i = ConstantOperand C.Int {integerBits = fromInteger n, integerValue = i}

-- Helper to construct undefined value with a certain type
constUndef :: AST.Type -> Operand
constUndef t = ConstantOperand C.Undef {constantType = t}
