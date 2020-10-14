{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.Expr where

import Cogent.Common.Syntax (TagName, unCoreFunName)
import qualified Cogent.Common.Syntax as Sy (Op (..))
import Cogent.Common.Types
import Cogent.Core as Core
import Cogent.Dargent.Util (primIntSizeBits)
import Cogent.LLVM.CodeGen
import Cogent.LLVM.Types
import Control.Monad.State (gets, modify)
import Data.Char (ord)
import Data.Either (fromLeft)
import Data.Fin (finInt)
import Data.Foldable (foldrM)
import Data.List (findIndex, null)
import Data.Maybe (fromMaybe)
import LLVM.AST as AST
import LLVM.AST.CallingConvention as CC
import qualified LLVM.AST.Constant as C
import LLVM.AST.IntegerPredicate as IntP
import LLVM.AST.Typed (typeOf)

exprToLLVM :: TypedExpr t v a b -> Codegen (Either Operand (Named Terminator))
exprToLLVM (TE _ Unit) = return (Left (constInt 8 0))
exprToLLVM (TE _ (ILit int p)) = return (Left (constInt (primIntSizeBits p) int))
exprToLLVM (TE _ (SLit str)) =
    return
        ( Left
            ( ConstantOperand
                C.Array
                    { C.memberType = IntegerType 8
                    , C.memberValues = [C.Int {C.integerBits = 8, C.integerValue = toInteger (ord c)} | c <- str]
                    }
            )
        )
exprToLLVM (TE rt (Op op [a, b])) =
    do
        _oa <- exprToLLVM a
        _ob <- exprToLLVM b
        -- If the operands are known at compile time, should we evaluate the expression here? / z.shang
        res <-
            let oa = fromLeft (error "operand of OP cannot be terminator") _oa
                ob = fromLeft (error "operand of OP cannot be terminator") _ob
             in case op of
                    Sy.Plus ->
                        instr
                            (toLLVMType rt)
                            ( Add
                                { nsw = False
                                , nuw = True
                                , operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.Minus ->
                        instr
                            (toLLVMType rt)
                            ( Sub
                                { nsw = False
                                , nuw = True
                                , operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.Times ->
                        instr
                            (toLLVMType rt)
                            ( Mul
                                { nsw = False
                                , nuw = True
                                , operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.Divide ->
                        instr
                            (toLLVMType rt)
                            ( SDiv
                                { exact = False -- Or should we do more check here?
                                , operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.Mod ->
                        instr
                            (toLLVMType rt)
                            ( SRem
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.And ->
                        instr
                            (toLLVMType rt)
                            ( And
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.Or ->
                        instr
                            (toLLVMType rt)
                            ( Or
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.Gt ->
                        instr
                            (IntegerType 1)
                            ( ICmp
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                , iPredicate = UGT -- assuming unsigned
                                }
                            )
                    Sy.Lt ->
                        instr
                            (IntegerType 1)
                            ( ICmp
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                , iPredicate = ULT -- assuming unsigned
                                }
                            )
                    Sy.Ge ->
                        instr
                            (IntegerType 1)
                            ( ICmp
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                , iPredicate = UGE -- assuming unsigned
                                }
                            )
                    Sy.Le ->
                        instr
                            (IntegerType 1)
                            ( ICmp
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                , iPredicate = ULE -- assuming unsigned
                                }
                            )
                    Sy.Eq ->
                        instr
                            (IntegerType 1)
                            ( ICmp
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                , iPredicate = IntP.EQ -- assuming unsigned
                                }
                            )
                    Sy.NEq ->
                        instr
                            (IntegerType 1)
                            ( ICmp
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                , iPredicate = NE -- assuming unsigned
                                }
                            )
                    Sy.BitAnd ->
                        instr
                            (toLLVMType rt)
                            ( And
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.BitOr ->
                        instr
                            (toLLVMType rt)
                            ( Or
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.BitXor ->
                        instr
                            (toLLVMType rt)
                            ( Xor
                                { operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.LShift ->
                        instr
                            (toLLVMType rt)
                            ( Shl
                                { nsw = False
                                , nuw = False
                                , operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
                    Sy.RShift ->
                        instr
                            (toLLVMType rt)
                            ( LShr
                                { exact = False
                                , operand0 = oa
                                , operand1 = ob
                                , metadata = []
                                }
                            )
        Left -- to convert i1 back to i8
            <$> ( case rt of
                    TPrim Boolean ->
                        instr
                            (toLLVMType rt)
                            ( ZExt
                                { operand0 = res
                                , type' = IntegerType 8
                                , metadata = []
                                }
                            )
                    _ -> return res
                )
exprToLLVM (TE rt (Op Sy.Complement [a])) =
    do
        _oa <- exprToLLVM a
        let oa = fromLeft (error "operand of OP cannot be terminator") _oa
        res <-
            instr
                (toLLVMType rt)
                ( Xor
                    { operand0 = oa
                    , operand1 = constInt (typeSize rt) (-1)
                    , metadata = []
                    }
                )
        return (Left res)
-- Not is just Complement for Bool
exprToLLVM (TE rt (Op Sy.Not t)) = exprToLLVM (TE rt (Op Sy.Complement t))
exprToLLVM (TE _ (Member recd fld)) =
    do
        (_, fldv) <- loadMember recd fld
        return (Left fldv)
exprToLLVM (TE _ (Take (_, _) recd fld body)) =
    do
        (recv, fldv) <- loadMember recd fld
        vars <- gets indexing
        modify (\s -> s {indexing = [fldv, recv] ++ vars})
        res <- exprToLLVM body
        case res of
            Left val -> terminator (Do (Ret (Just val) [])) >>= (return . Right)
            Right trm -> return (Right trm)
exprToLLVM (TE rt (Put recd fld val)) =
    do
        _recv <- exprToLLVM recd
        let recv = fromLeft (error "address cannot be terminator") _recv
        _v <- exprToLLVM val
        let v = fromLeft (error "address cannot be terminator") _v
        res <-
            instr
                (toLLVMType rt)
                ( InsertValue
                    { aggregate = recv
                    , element = v
                    , indices' = [toEnum fld]
                    , metadata = []
                    }
                )
        return (Left res)
exprToLLVM (TE _ (Let _ val body)) =
    -- it seems that the variable name is not used here
    do
        _v <- exprToLLVM val
        let v = fromLeft (error "let cannot bind a terminator") _v
        vars <- gets indexing
        modify (\s -> s {indexing = v : vars})
        res <- exprToLLVM body
        case res of
            Left val -> terminator (Do (Ret (Just val) [])) >>= (return . Right)
            Right trm -> return (Right trm)
exprToLLVM (TE rt (LetBang _ a val body)) = exprToLLVM (TE rt (Let a val body)) -- same as Let
exprToLLVM (TE _ (Promote _ e)) = exprToLLVM e
exprToLLVM (TE rt (Cast _ e)) =
    do
        _v <- exprToLLVM e
        res <-
            instr
                (toLLVMType rt)
                ( ZExt
                    { operand0 = fromLeft (error "cannot cast a terminator") _v
                    , type' = toLLVMType rt
                    , metadata = []
                    }
                )
        return (Left res)
exprToLLVM (TE rt (Con tag e (TSum ts))) =
    do
        tagged <-
            instr
                (toLLVMType rt)
                ( InsertValue
                    { aggregate = constUndef (toLLVMType rt)
                    , element = constInt 32 (toInteger (tagIndex rt tag))
                    , indices' = [0]
                    , metadata = []
                    }
                )
        _value <- exprToLLVM e
        let value = fromLeft (error "value cannot be a terminator") _value
        case e of
            TE TUnit _ -> return (Left tagged)
            _ -> do
                casted <- castVal (toLLVMType (maxMember ts)) value
                res <-
                    instr
                        (toLLVMType rt)
                        ( InsertValue
                            { aggregate = tagged
                            , element = casted
                            , indices' = [1]
                            , metadata = []
                            }
                        )
                return (Left res)
exprToLLVM (TE _ (Case e@(TE rt _) tag (_, _, tb) (_, _, fb))) =
    do
        _variant <- exprToLLVM e
        tagv <-
            instr
                (IntegerType 32)
                ( ExtractValue
                    { aggregate = fromLeft (error "variant cannot be a terminator") _variant
                    , indices' = [0]
                    , metadata = []
                    }
                )
        cond <-
            instr
                (IntegerType 1)
                ( ICmp
                    { iPredicate = IntP.EQ
                    , operand0 = tagv
                    , operand1 = constInt 32 (toInteger (tagIndex rt tag))
                    , metadata = []
                    }
                )
        currentBlk <- gets currentBlock
        blkCaseTrue <- addBlock "brCaseTrue"
        blkCaseFalse <- addBlock "brCaseFalse"
        -- blkEnd <- addBlock "brEnd"
        setBlock blkCaseTrue
        _tb <- exprToLLVM tb
        case _tb of
            Left val -> terminator (Do (Ret (Just val) []))
            Right trm -> terminator trm
        setBlock blkCaseFalse
        _fb <- exprToLLVM fb
        case _fb of
            Left val -> terminator (Do (Ret (Just val) []))
            Right trm -> terminator trm
        setBlock currentBlk
        terminator
            ( Do
                ( CondBr
                    { condition = cond
                    , trueDest = blkCaseTrue
                    , falseDest = blkCaseFalse
                    , metadata' = []
                    }
                )
            )
            >>= (return . Right)
exprToLLVM (TE rt (Esac e)) =
    do
        _variant <- exprToLLVM e
        let TE (TSum ts) _ = e
        value <-
            instr
                (toLLVMType (maxMember ts))
                ( ExtractValue
                    { aggregate = fromLeft (error "variant cannot be a terminator") _variant
                    , indices' = [1]
                    , metadata = []
                    }
                )
        casted <- castVal (toLLVMType rt) value
        return (Left casted)
exprToLLVM (TE _ (If cd tb fb)) =
    do
        _cond <- exprToLLVM cd
        cond <-
            instr
                (IntegerType 1)
                ( ICmp
                    { iPredicate = IntP.EQ
                    , operand0 = fromLeft (error "cond cannot be a terminator") _cond
                    , operand1 = constInt 1 1
                    , metadata = []
                    }
                )
        currentBlk <- gets currentBlock
        blkTrue <- addBlock "brTrue"
        blkFalse <- addBlock "brFalse"
        -- blkEnd <- addBlock "brEnd"
        setBlock blkTrue
        _tb <- exprToLLVM tb
        case _tb of
            Left val -> terminator (Do (Ret (Just val) []))
            Right trm -> terminator trm
        setBlock blkFalse
        _fb <- exprToLLVM fb
        case _fb of
            Left val -> terminator (Do (Ret (Just val) []))
            Right trm -> terminator trm
        setBlock currentBlk
        terminator
            ( Do
                ( CondBr
                    { condition = cond
                    , trueDest = blkTrue
                    , falseDest = blkFalse
                    , metadata' = []
                    }
                )
            )
            >>= (return . Right)
exprToLLVM (TE rt (Struct flds)) =
    foldrM
        ( \(i, v) struct ->
            exprToLLVM v >>= \value ->
                instr
                    (toLLVMType rt)
                    ( InsertValue
                        { aggregate = struct
                        , element = fromLeft (error "field value cannot be terminator") value
                        , indices' = [i]
                        , metadata = []
                        }
                    )
        )
        (constUndef (toLLVMType rt))
        [(i, snd fld) | (i, fld) <- zip [0 ..] flds]
        >>= (return . Left)
exprToLLVM (TE vt (Variable (idx, _))) =
    do
        unnames <- gets unnamedCount
        _indexing <- gets indexing
        let indexing = _indexing
         in let _idx = finInt idx
             in if Data.List.null indexing
                    then
                        let pos = fromIntegral unnames - _idx
                         in return (Left (LocalReference (toLLVMType vt) (UnName (fromIntegral pos))))
                    else return (Left (indexing !! _idx))
exprToLLVM (TE ft (Fun f _ _ _)) =
    return
        ( Left
            ( ConstantOperand
                ( C.GlobalReference
                    (toLLVMType ft)
                    (mkName (unCoreFunName f))
                )
            )
        )
exprToLLVM (TE rt (App f a)) = do
    _arg <- exprToLLVM a
    _fun <- exprToLLVM f
    let arg = fromLeft (error "argument value cannot be terminator") _arg
        fun = fromLeft (error "function value cannot be terminator") _arg
    res <-
        instr
            (toLLVMType rt)
            ( Call
                { tailCallKind = Nothing
                , callingConvention = CC.C
                , returnAttributes = []
                , function = Right fun
                , arguments = [(arg, [])]
                , functionAttributes = []
                , metadata = []
                }
            )
    return (Left res)
exprToLLVM _ = error "not implemented yet"

loadMember :: TypedExpr t v a b -> Int -> Codegen (Operand, Operand)
loadMember recd fld = do
    _recv <- exprToLLVM recd
    let recv = fromLeft (error "address cannot be terminator") _recv
    fldv <-
        instr
            (recordType recd !! fld)
            ( ExtractValue
                { aggregate = recv
                , indices' = [toEnum fld]
                , metadata = []
                }
            )
    return (recv, fldv)

castVal :: AST.Type -> Operand -> Codegen Operand
castVal t o = do
    tmp <-
        instr
            (ptrTo (typeOf o))
            ( Alloca
                { allocatedType = typeOf o
                , numElements = Nothing
                , alignment = 4
                , metadata = []
                }
            )
    unnamedInstr
        ( Store
            { volatile = False
            , address = tmp
            , maybeAtomicity = Nothing
            , value = o
            , alignment = 4
            , metadata = []
            }
        )
    casted <-
        instr
            (ptrTo t)
            ( BitCast
                { operand0 = tmp
                , type' = ptrTo t
                , metadata = []
                }
            )
    instr
        t
        ( Load
            { volatile = False
            , address = casted
            , maybeAtomicity = Nothing
            , alignment = 4
            , metadata = []
            }
        )

recordType :: TypedExpr t v a b -> [AST.Type]
recordType (TE rect _) = case rect of
    (TRecord _ flds _) -> map toLLVMType (fieldTypes flds)
    _ -> error "cannot get record type from a non-record type"

tagIndex :: Core.Type t b -> TagName -> Int
tagIndex (TSum ts) tag =
    fromMaybe
        (error "cant find tag")
        (findIndex ((== tag) . fst) ts)
tagIndex _ _ = error "non variant type has no tags"
