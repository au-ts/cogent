{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}

module Cogent.LLVM.Expr where

import Cogent.Common.Syntax as Sy
import Cogent.Common.Types (PrimInt (Boolean))
import Cogent.Core as Core
import Cogent.Dargent.Util (primIntSizeBits)
import Cogent.LLVM.Types
import Control.Monad (void)
import Control.Monad.Fix (MonadFix)
import Data.Char (ord)
import Data.Fin (finInt)
import Data.Foldable (foldrM)
import Data.List (findIndex)
import Data.Maybe (fromMaybe)
import LLVM.AST as AST
import qualified LLVM.AST.Constant as C
import LLVM.AST.IntegerPredicate as P
import LLVM.AST.Type (i8, ptr)
import LLVM.AST.Typed (typeOf)
import LLVM.IRBuilder.Constant (array, int32, int8)
import LLVM.IRBuilder.Instruction as IR
import LLVM.IRBuilder.Module (MonadModuleBuilder, typedef)
import LLVM.IRBuilder.Monad (MonadIRBuilder, block, currentBlock, emitInstr, named)

exprToLLVM ::
    (MonadIRBuilder m, MonadModuleBuilder m, MonadFix m, Show a, Show b) =>
    TypedExpr t v a b ->
    [Operand] ->
    m Operand
exprToLLVM e@(TE t _) vars = monomorphicTypeDef t >> exprToLLVM' e vars

monomorphicTypeDef :: (MonadModuleBuilder m) => Core.Type t b -> m ()
monomorphicTypeDef t@TCon {} = void $ typedef (mkName (nameType t)) Nothing
monomorphicTypeDef _ = pure ()

exprToLLVM' ::
    (MonadIRBuilder m, MonadModuleBuilder m, MonadFix m, Show a, Show b) =>
    TypedExpr t v a b ->
    [Operand] ->
    m Operand
exprToLLVM' (TE _ Unit) _ = pure $ int8 0
exprToLLVM' (TE _ (ILit int p)) _ = pure $ constInt (primIntSizeBits p) int
exprToLLVM' (TE _ (SLit str)) _ = pure $ array $ C.Int 8 . toInteger . ord <$> str
exprToLLVM' (TE t (Op op [a, b])) vars = do
    oa <- exprToLLVM a vars
    ob <- exprToLLVM b vars
    res <- toLLVMOp op oa ob
    case t of
        TPrim Boolean -> zext res i8
        _ -> pure res
exprToLLVM' (TE t (Op Sy.Complement [a])) vars = do
    oa <- exprToLLVM a vars
    xor oa (constInt (typeSize t) (-1))
exprToLLVM' (TE t (Op Sy.Not [a])) vars = exprToLLVM (TE t (Op Sy.Complement [a])) vars
exprToLLVM' (TE _ (Member recd fld)) vars = loadMember recd fld vars >>= (pure . fst)
exprToLLVM' (TE _ (Take _ recd fld body)) vars = do
    (recv, fldv) <- loadMember recd fld vars
    exprToLLVM body (fldv : recv : vars)
exprToLLVM' (TE _ (Put recd fld val)) vars = do
    recv <- exprToLLVM recd vars
    v <- exprToLLVM val vars
    if isUnboxed (exprType recd)
        then insertValue recv v [toEnum fld]
        else do
            fldp <- gep recv [int32 0, int32 (toEnum fld)]
            store fldp 0 v
            pure recv
exprToLLVM' (TE _ (Let _ val body)) vars = do
    v <- exprToLLVM val vars
    exprToLLVM body (v : vars)
exprToLLVM' (TE t (LetBang _ a val body)) vars = exprToLLVM (TE t (Let a val body)) vars
exprToLLVM' (TE _ (Promote _ e)) vars = exprToLLVM e vars
exprToLLVM' (TE _ (Cast t e)) vars = do
    typedef "foo" Nothing
    v <- exprToLLVM e vars
    zext v (toLLVMType t)
exprToLLVM' (TE t (Con tag e (TSum ts))) vars = do
    tagged <- insertValue (constUndef (toLLVMType t)) (int32 (tagIndex t tag)) [0]
    v <- exprToLLVM e vars
    case e of
        TE TUnit _ -> pure tagged
        _ -> do
            casted <- castVal (toLLVMType (maxMember ts)) v
            insertValue tagged casted [1]
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
exprToLLVM' (TE t (Esac e)) vars = do
    variant <- exprToLLVM e vars
    v <- extractValue variant [1]
    castVal (toLLVMType t) v
exprToLLVM' (TE _ (If cd tb fb)) vars = mdo
    v <- exprToLLVM cd vars
    cond <- icmp P.EQ v (int8 1)
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
exprToLLVM' (TE t (Struct flds)) vars =
    foldrM
        (\(i, v) struct -> exprToLLVM v vars >>= \value -> insertValue struct value [i])
        (constUndef (toLLVMType t))
        [(i, snd fld) | (i, fld) <- zip [0 ..] flds]
exprToLLVM' (TE _ (Variable (idx, _))) vars = pure $ vars !! finInt idx
exprToLLVM' (TE t (Fun f _ _ _)) _ =
    pure $
        ConstantOperand $
            C.GlobalReference
                (toLLVMType t)
                (mkName (unCoreFunName f))
exprToLLVM' (TE _ (App f a)) vars = do
    arg <- exprToLLVM a vars
    fun <- exprToLLVM f vars
    call fun [(arg, [])]
exprToLLVM' e _ = error $ "unknown" ++ show e

toLLVMOp :: MonadIRBuilder m => Sy.Op -> (Operand -> Operand -> m Operand)
toLLVMOp Sy.Plus = add
toLLVMOp Sy.Minus = sub
toLLVMOp Sy.Times = mul
toLLVMOp Sy.Divide = udiv
toLLVMOp Sy.Mod = urem
toLLVMOp Sy.Not = error "not binary"
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
toLLVMOp Sy.RShift = \a b -> emitInstr (typeOf a) $ LShr False a b []
toLLVMOp Sy.Complement = error "not binary"

castVal :: MonadIRBuilder m => AST.Type -> Operand -> m Operand
castVal t o = do
    tmp <- alloca (typeOf o) Nothing 4
    store tmp 4 o
    casted <- bitcast tmp (ptr t)
    load casted 4

loadMember ::
    (MonadIRBuilder m, MonadModuleBuilder m, MonadFix m, Show a, Show b) =>
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

tagIndex :: Core.Type t b -> TagName -> Integer
tagIndex (TSum ts) tag =
    toInteger $
        fromMaybe
            (error "cant find tag")
            (findIndex ((== tag) . fst) ts)
tagIndex _ _ = error "non variant type has no tags"
