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

module Cogent.LLVM.Expr (exprToLLVM, monomorphicTypeDef, castVal, constUndef) where

-- This module converts Cogent expressions into LLVM IR via the IRBuilder
-- monadic interface

import Cogent.Common.Syntax as Sy
import Cogent.Common.Types (PrimInt (Boolean))
import Cogent.Core as Core
import Cogent.Dargent.Util (primIntSizeBits)
import Cogent.LLVM.Types (fieldTypes, maxMember, nameType, tagType, toLLVMType, typeSize)
import Cogent.Util (toCName)
import Control.Monad (void)
import Control.Monad.Fix (MonadFix)
import Data.Char (ord)
import Data.Fin (finInt)
import Data.Foldable (foldrM)
import Data.List (findIndex)
import Data.Maybe (fromMaybe)
import LLVM.AST as AST (Instruction (LShr), Operand (ConstantOperand), Type, mkName)
import qualified LLVM.AST.Constant as C
import LLVM.AST.IntegerPredicate as P (IntegerPredicate (EQ, NE, UGE, UGT, ULE, ULT))
import LLVM.AST.Type (i8, ptr)
import LLVM.AST.Typed (typeOf)
import LLVM.IRBuilder.Constant (array, int32, int8)
import LLVM.IRBuilder.Instruction as IR
import LLVM.IRBuilder.Module (MonadModuleBuilder, typedef)
import LLVM.IRBuilder.Monad (MonadIRBuilder, block, currentBlock, emitInstr, named)

-- Given a single typed expression, and a list of in-scope variables, create the
-- LLVM IR to compute the expression
-- Also create monomorphised typedefs for any abstract types that appear in the
-- expression type
exprToLLVM ::
    (MonadIRBuilder m, MonadModuleBuilder m, MonadFix m) =>
    TypedExpr t v a b ->
    [Operand] ->
    m Operand
exprToLLVM e@(TE t _) vars = monomorphicTypeDef t >> exprToLLVM' e vars

-- If the provided type is abstract, or contains one, emit a typedef for it
monomorphicTypeDef :: (MonadModuleBuilder m) => Core.Type t b -> m ()
monomorphicTypeDef t@TCon {} = void $ typedef (mkName (nameType t)) Nothing
monomorphicTypeDef (TRecord _ ts _) = mapM_ monomorphicTypeDef $ fieldTypes ts
monomorphicTypeDef (TSum ts) = mapM_ monomorphicTypeDef $ fieldTypes ts
monomorphicTypeDef _ = pure ()

-- Given a single typed expression, and a list of in-scope variables, create the
-- LLVM IR to compute the expression
exprToLLVM' ::
    (MonadIRBuilder m, MonadModuleBuilder m, MonadFix m) =>
    TypedExpr t v a b ->
    [Operand] ->
    m Operand
-- Unit is represented as a byte of arbitrary value
exprToLLVM' (TE _ Unit) _ = pure $ int8 0
-- Integer literals are mapped to LLVM integer types
exprToLLVM' (TE _ (ILit int p)) _ = pure $ constInt (primIntSizeBits p) int
-- For string literals use a byte array of ASCII values
exprToLLVM' (TE _ (SLit str)) _ = pure $ array $ C.Int 8 . toInteger . ord <$> str
-- For binary operators evaluate each operand and then the result
exprToLLVM' (TE t (Op op [a, b])) vars = do
    oa <- exprToLLVM a vars
    ob <- exprToLLVM b vars
    res <- toLLVMOp op oa ob
    case t of
        -- Coerce boolean results back to a full byte rather than a single bit
        TPrim Boolean -> if typeOf res == i8 then pure res else zext res i8
        _ -> pure res
-- Complement must be implemented by xor with an equal-length value consisting
-- entirely of 1 bits
exprToLLVM' (TE t (Op Sy.Complement [a])) vars = do
    oa <- exprToLLVM a vars
    xor oa (constInt (typeSize t) (-1))
-- Not is simply complement but for the Bool type
exprToLLVM' (TE t (Op Sy.Not [a])) vars = exprToLLVM (TE t (Op Sy.Complement [a])) vars
-- For record member access just load the member and yield the field value
exprToLLVM' (TE _ (Member recd fld)) vars = snd <$> loadMember recd fld vars
-- Take requires us to bind the field value and also the record value as new
-- variables which we can use to evaluate the body of the expression
exprToLLVM' (TE _ (Take _ recd fld body)) vars = do
    (recv, fldv) <- loadMember recd fld vars
    exprToLLVM body (fldv : recv : vars)
-- To put a value into a record, evaluate the record and the value, then for:
--  - unboxed records: simply use the insertvalue IR instruction
--  - boxed records: calculate the field pointer and store the value
-- In either case the yielded result is the updated record
exprToLLVM' (TE _ (Put recd fld val)) vars = do
    recv <- exprToLLVM recd vars
    v <- exprToLLVM val vars
    if isUnboxed (exprType recd)
        then insertValue recv v [toEnum fld]
        else do
            fldp <- gep recv [int32 0, int32 (toEnum fld)]
            store fldp 0 v
            pure recv
-- For a let binding we evalaute the value using the current vars, and then
-- evaluate the body using the updated set of variables
exprToLLVM' (TE _ (Let _ val body)) vars = do
    v <- exprToLLVM val vars
    exprToLLVM body (v : vars)
-- let! is the same as let
exprToLLVM' (TE t (LetBang _ a val body)) vars = exprToLLVM (TE t (Let a val body)) vars
-- Promote is syntactic only
exprToLLVM' (TE _ (Promote _ e)) vars = exprToLLVM e vars
-- To upcast, zero extend the evaluated expression as needed
exprToLLVM' (TE _ (Cast t e)) vars = do
    v <- exprToLLVM e vars
    zext v (toLLVMType t)
-- Constructing a sumtype consists of inserting a 32bit tag, followed by a value
-- The value must be casted to the 'maximum member' of the variant beforehand
exprToLLVM' (TE t (Con tag e (TSum ts))) vars = do
    tagged <- insertValue (constUndef (toLLVMType t)) (int32 (toInteger (tagIndex t tag))) [0]
    v <- exprToLLVM e vars
    case e of
        -- Don't bother doing anything for constructors with no arguments
        TE TUnit _ -> pure tagged
        _ -> do
            casted <- castVal (toLLVMType (maxMember ts)) v
            insertValue tagged casted [1]
-- The binary case expression compares the tag of a variant with the desired tag
-- Branching is used for each alternative:
--  - if the tag matches, evaluate the true branch with the variant's value
--    bound as a new variable
--  - otherwise, evaluate the false branch with the whole variant bound
-- The phi instruction is used to yield the final result based on the branch
exprToLLVM' (TE _ (Case e@(TE rt _) tag (_, _, tb) (_, _, fb))) vars = mdo
    variant <- exprToLLVM e vars
    tagv <- extractValue variant [0]
    cond <- icmp P.EQ tagv (int32 (toInteger (tagIndex rt tag)))
    condBr cond brMatch brNotMatch
    brMatch <- block `named` "case.true"
    v <- extractValue variant [1]
    casted <- castVal (toLLVMType (tagType rt tag)) v
    valTrue <- exprToLLVM tb (casted : vars)
    brMatch' <- currentBlock
    br brExit
    brNotMatch <- block `named` "case.false"
    valFalse <- exprToLLVM fb (variant : vars)
    brNotMatch' <- currentBlock
    br brExit
    brExit <- block `named` "case.done"
    phi [(valTrue, brMatch'), (valFalse, brNotMatch')]
-- Esac requires us to extract the value from the variant and cast it
exprToLLVM' (TE t (Esac e)) vars = do
    variant <- exprToLLVM e vars
    v <- extractValue variant [1]
    castVal (toLLVMType t) v
-- For if the condition must be evaluated and then branching is used to evaluate
-- the true or false branch
-- The phi instruction is used to yield the final result based on the branch
exprToLLVM' (TE _ (If cd tb fb)) vars = mdo
    v <- exprToLLVM cd vars
    cond <- icmp NE v (int8 0)
    condBr cond brTrue brFalse
    brTrue <- block `named` "if.true"
    valTrue <- exprToLLVM tb vars
    brTrue' <- currentBlock
    br brExit
    brFalse <- block `named` "if.false"
    valFalse <- exprToLLVM fb vars
    brFalse' <- currentBlock
    br brExit
    brExit <- block `named` "if.done"
    phi [(valTrue, brTrue'), (valFalse, brFalse')]
-- A struct expression is constructed by iteratively inserting field values
exprToLLVM' (TE t (Struct flds)) vars =
    foldrM
        (\(i, v) struct -> exprToLLVM v vars >>= \value -> insertValue struct value [i])
        (constUndef (toLLVMType t))
        [(i, snd fld) | (i, fld) <- zip [0 ..] flds]
-- Use the variable index to look it up in the current variable context
exprToLLVM' (TE _ (Variable (idx, _))) vars = pure $ vars !! finInt idx
-- Functions must be references to something already defined globally
exprToLLVM' (TE t (Fun f _ _ _)) _ =
    pure $
        ConstantOperand $
            C.GlobalReference
                (toLLVMType t)
                -- append .llvm to end of fn name for non-wrapped version
                ((mkName . (++ ".llvm") . toCName . unCoreFunName) f)
-- To apply a function, evaluate the argument and function then call it
exprToLLVM' (TE _ (App f a)) vars = do
    arg <- exprToLLVM a vars
    fun <- exprToLLVM f vars
    call fun [(arg, [])]
exprToLLVM' _ _ = error "unknown expression"

-- Map a Cogent binary operator to LLVM binary operators
toLLVMOp :: MonadIRBuilder m => Sy.Op -> (Operand -> Operand -> m Operand)
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
castVal :: MonadIRBuilder m => AST.Type -> Operand -> m Operand
castVal t o = do
    tmp <- alloca (typeOf o) Nothing 4
    store tmp 4 o
    casted <- bitcast tmp (ptr t)
    load casted 4

-- Load a field from a record, and yield both the record and the field value
-- For unboxed records, this is just an extractvalue instruction, for boxed it
-- requires calculating the field pointer and then loading the value
loadMember ::
    (MonadIRBuilder m, MonadModuleBuilder m, MonadFix m) =>
    TypedExpr t v a b ->
    Int ->
    [Operand] ->
    m (Operand, Operand)
loadMember recd fld vars = do
    recv <- exprToLLVM recd vars
    fldv <-
        if isUnboxed (exprType recd)
            then extractValue recv [toEnum fld]
            else gep recv [int32 0, int32 (toEnum fld)] >>= \fldp -> load fldp 0
    pure (recv, fldv)

-- Convert the tag name for a variant to a 32-bit tag unique for that variant
tagIndex :: Core.Type t b -> TagName -> Int
tagIndex (TSum ts) tag =
    fromMaybe
        (error "unknown tag")
        (findIndex ((== tag) . fst) ts)
tagIndex _ _ = error "not a variant type"

-- Helper to construct integer with a certain size and value
constInt :: Integer -> Integer -> Operand
constInt n i = ConstantOperand C.Int {integerBits = fromInteger n, integerValue = i}

-- Helper to construct undefined value with a certain type
constUndef :: AST.Type -> Operand
constUndef t = ConstantOperand C.Undef {constantType = t}
