{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module Cogent.LLVM.WithCoq (compileWithCoq) where

-- Acts as a layer between the core Cogent Haskell compiler and the
-- extracted Coq implementation for a compiler.
-- Also includes functions to convert a VIR AST to a llvm-hs AST.

import Cogent.Common.Syntax (CoreFunName (..), Op, VarName)
import qualified Cogent.Common.Syntax as S (Op (..))
import Cogent.Common.Types (PrimInt)
import qualified Cogent.Common.Types as T (PrimInt (..), Sigil (..))
import Cogent.Core (TypedExpr (..))
import qualified Cogent.Core as C (Definition (..), Expr (..), Type (..))
import Cogent.LLVM.Compile (writeLLVM)
import Data.ByteString.Internal (packChars)
import Data.ByteString.Short.Internal (toShort)
import Data.Fin (Fin (..))
import ExtractedCoq.Compiler hiding (map)
import qualified LLVM.AST as LL
import LLVM.AST.CallingConvention as LLCC (CallingConvention (..))
import qualified LLVM.AST.Constant as LLC
import LLVM.AST.Global (Global (..))
import LLVM.AST.Type hiding (Type)
import LLVM.Target (getDefaultTargetTriple)
import System.FilePath (replaceExtension)
import System.IO (IOMode (..), hClose, openFile)

finNat :: Fin n -> Nat
finNat FZero = O
finNat (FSuc f) = S $ finNat f

nWord :: Num a => N -> a
nWord N0 = 0
nWord (Npos n) = fromInteger n

-- Top level compilation function
compileWithCoq :: [C.Definition TypedExpr VarName VarName] -> FilePath -> IO ()
compileWithCoq monoed source = do
    target <- getDefaultTargetTriple
    let sourceFilename = toShort $ packChars source
        source' = convCogentAST monoed
        Right output = compile_cogent source'
        output' = convVellvmAST output
        ast =
            LL.Module
                { LL.moduleName = sourceFilename
                , LL.moduleSourceFileName = sourceFilename
                , LL.moduleDataLayout = Nothing
                , LL.moduleTargetTriple = Just target
                , LL.moduleDefinitions = output'
                }
        resName = replaceExtension source "ll"
    outFile <- openFile resName WriteMode
    writeLLVM ast outFile
    hClose outFile
    return ()

-- Convert the Cogent AST into a form the Coq-based compiler understands
convCogentAST :: [C.Definition TypedExpr VarName VarName] -> Cogent_prog
convCogentAST = map convCogentDefinition

convCogentDefinition :: C.Definition TypedExpr VarName VarName -> Def
convCogentDefinition (C.FunDef _ name _ _ t rt body) =
    FunDef name (convCogentType t) (convCogentType rt) (convCogentExpr body)
convCogentDefinition C.AbsDecl {} = error "AbsDecl is not supported"
convCogentDefinition C.TypeDef {} = error "TypeDef is not supported"

convCogentType :: Show b => C.Type t b -> Type
convCogentType C.TUnit = TUnit
convCogentType (C.TFun t rt) = TFun (convCogentType t) (convCogentType rt)
convCogentType t@(C.TPrim _) = TPrim (convCogentPrimType t)
convCogentType C.TString = TPrim String
convCogentType (C.TRecord _ flds s) =
    let flds' = ([(f, (convCogentType t, if b then Taken else Present)) | (f, (t, b)) <- flds])
     in TRecord flds' (convCogentSigil s)
convCogentType t = error $ show t

convCogentExpr :: (Show a, Show b) => TypedExpr t v a b -> Expr
convCogentExpr (TE _ (C.ILit int p)) = Lit0 $ convCogentLit int p
convCogentExpr (TE _ (C.Op op [a, b])) =
    BPrim (convCogentOp (exprType a) op) (convCogentExpr a) (convCogentExpr b)
convCogentExpr (TE _ (C.Let _ val body)) = Let (convCogentExpr val) (convCogentExpr body)
convCogentExpr (TE _ (C.Variable (idx, _))) = Var (finNat idx)
convCogentExpr (TE _ C.Unit) = Unit
convCogentExpr (TE _ (C.If c b1 b2)) = If (convCogentExpr c) (convCogentExpr b1) (convCogentExpr b2)
convCogentExpr e = error $ show e

convCogentLit :: Integer -> PrimInt -> Lit
convCogentLit w T.U8 = LU8 w
convCogentLit w T.U32 = LU32 w
convCogentLit w T.U64 = LU64 w
convCogentLit w T.Boolean = LBool (w /= 0)

convCogentOp :: C.Type t b -> Op -> Prim_op
convCogentOp t S.Plus = Plus $ convCogentNumType t
convCogentOp t S.Minus = Minus $ convCogentNumType t
convCogentOp t S.Times = Times $ convCogentNumType t
convCogentOp t S.Divide = Divide $ convCogentNumType t
convCogentOp t S.Mod = Mod $ convCogentNumType t

convCogentPrimType :: C.Type t b -> Prim_type
convCogentPrimType (C.TPrim T.Boolean) = Bool
convCogentPrimType t@(C.TPrim _) = Num $ convCogentNumType t
convCogentPrimType C.TString = String
convCogentPrimType _ = error "not a PrimType"

convCogentNumType :: C.Type t b -> Num_type
convCogentNumType (C.TPrim T.U8) = U8
convCogentNumType (C.TPrim T.U32) = U32
convCogentNumType (C.TPrim T.U64) = U64
convCogentNumType _ = error "not a NumType"

convCogentSigil :: T.Sigil r -> Sigil
convCogentSigil (T.Boxed _ _) = Boxed
convCogentSigil T.Unboxed = Unboxed

-- Convert the Vellvm (VIR) AST into a llvm-hs AST
convVellvmAST :: Vellvm_prog -> [LL.Definition]
convVellvmAST = map convVellvmTLE

convVellvmTLE :: Toplevel_entity Typ (Block Typ, [Block Typ]) -> LL.Definition
convVellvmTLE (TLE_Definition d) = convVellvmDef d
convVellvmTLE _ = error "unsupported top level entity"

convVellvmDef :: Definition Typ (Block Typ, [Block Typ]) -> LL.Definition
convVellvmDef (Mk_definition dec args fnBody) =
    let Mk_declaration name (TYPE_Function retty argtys) _ _ _ _ _ _ _ _ _ = dec
        params = zipWith (\ty id -> LL.Parameter (convVellvmTyp ty) (convVellvmId id) []) argtys args
     in LL.GlobalDefinition
            LL.functionDefaults
                { name = convVellvmId name
                , parameters = (params, False)
                , returnType = convVellvmTyp retty
                , basicBlocks = convVellvmBlock <$> uncurry (:) fnBody
                }

convVellvmId :: Raw_id -> LL.Name
convVellvmId (Name s) = LL.Name (toShort $ packChars s)
convVellvmId (Anon i) = LL.UnName (fromInteger i)
convVellvmId (Raw i) = LL.Name (toShort $ packChars ("_RAW_" ++ show i))

convVellvmTyp :: Typ -> LL.Type
convVellvmTyp (TYPE_I n) = LL.IntegerType (nWord n)
convVellvmTyp (TYPE_Pointer t) = ptr (convVellvmTyp t)
convVellvmTyp TYPE_Void = void
convVellvmTyp TYPE_Half = half
convVellvmTyp TYPE_Float = float
convVellvmTyp TYPE_Double = double
convVellvmTyp TYPE_X86_fp80 = x86_fp80
convVellvmTyp TYPE_Fp128 = fp128
convVellvmTyp TYPE_Ppc_fp128 = ppc_fp128
convVellvmTyp TYPE_Metadata = LL.MetadataType
convVellvmTyp TYPE_X86_mmx = error "unsupported type"
convVellvmTyp (TYPE_Array sz t) = LL.ArrayType (nWord sz) (convVellvmTyp t)
convVellvmTyp (TYPE_Function ret args) = LL.FunctionType (convVellvmTyp ret) (convVellvmTyp <$> args) False
convVellvmTyp (TYPE_Struct flds) = LL.StructureType False (convVellvmTyp <$> flds)
convVellvmTyp (TYPE_Packed_struct flds) = LL.StructureType True (convVellvmTyp <$> flds)
convVellvmTyp TYPE_Opaque = error "unsupported type"
convVellvmTyp (TYPE_Vector sz t) = LL.VectorType (nWord sz) (convVellvmTyp t)
convVellvmTyp (TYPE_Identified i) = error "unsupported type"

convVellvmBlock :: Block Typ -> LL.BasicBlock
convVellvmBlock (Mk_block id phis code term _) =
    let instrs = ((convVellvmNamedPhi <$> phis) ++ (convVellvmNamedInstr <$> code))
     in LL.BasicBlock (convVellvmId id) instrs (LL.Do (convVellvmTerm term))

convVellvmTerm :: Terminator Typ -> LL.Terminator
convVellvmTerm (TERM_Ret e) = LL.Ret (Just (convVellvmTExp e)) []
convVellvmTerm TERM_Ret_void = LL.Ret Nothing []
convVellvmTerm (TERM_Br e b1 b2) = LL.CondBr (convVellvmTExp e) (convVellvmId b1) (convVellvmId b2) []
convVellvmTerm (TERM_Br_1 b) = LL.Br (convVellvmId b) []
convVellvmTerm (TERM_Switch e d bs) = LL.Switch (convVellvmTExp e) (convVellvmId d) [(convVellvmIntLit i, convVellvmId b) | (i, b) <- bs] []
convVellvmTerm (TERM_IndirectBr e bs) = LL.IndirectBr (convVellvmTExp e) (convVellvmId <$> bs) []
convVellvmTerm (TERM_Resume e) = LL.Resume (convVellvmTExp e) []
convVellvmTerm TERM_Invoke {} = error "unsupported terminator"

convVellvmIntLit :: Tint_literal -> LLC.Constant
convVellvmIntLit (TInt_Literal n i) = LLC.Int (nWord n) i

convVellvmNamedInstr :: (Instr_id, Instr Typ) -> LL.Named LL.Instruction
convVellvmNamedInstr (IId id, instr) = convVellvmId id LL.:= convVellvmInstr instr
convVellvmNamedInstr (IVoid _, instr) = LL.Do (convVellvmInstr instr)

convVellvmInstr :: Instr Typ -> LL.Instruction
convVellvmInstr (INSTR_Comment m) = error "unsupported instruction"
convVellvmInstr (INSTR_Op (OP_IBinop op t v1 v2)) =
    convVellvmIBinop op (convVellvmTExp (t, v1)) (convVellvmTExp (t, v2)) []
convVellvmInstr (INSTR_Call fn args) = LL.Call Nothing LLCC.C [] (Right (convVellvmTExp fn)) [(convVellvmTExp a, []) | a <- args] [] []
convVellvmInstr (INSTR_Alloca t nb align) = LL.Alloca (convVellvmTyp t) (convVellvmTExp <$> nb) (maybe 0 fromInteger align) []
convVellvmInstr (INSTR_Load volatile _ ptr align) = LL.Load volatile (convVellvmTExp ptr) Nothing (maybe 0 fromInteger align) []
convVellvmInstr (INSTR_Store volatile val ptr align) = LL.Store volatile (convVellvmTExp ptr) (convVellvmTExp val) Nothing (maybe 0 fromInteger align) []
convVellvmInstr INSTR_Fence = error "unsupported instruction"
convVellvmInstr INSTR_AtomicCmpXchg = error "unsupported instruction"
convVellvmInstr INSTR_AtomicRMW = error "unsupported instruction"
convVellvmInstr INSTR_VAArg = error "unsupported instruction"
convVellvmInstr INSTR_LandingPad = error "unsupported instruction"

convVellvmNamedPhi :: (Raw_id, Phi0 Typ) -> LL.Named LL.Instruction
convVellvmNamedPhi (id, Phi t args) =
    let args' = [(convVellvmTExp (t, e), convVellvmId bid) | (bid, e) <- args]
     in convVellvmId id LL.:= LL.Phi (convVellvmTyp t) args' []

convVellvmIBinop :: Ibinop -> LL.Operand -> LL.Operand -> LL.InstructionMetadata -> LL.Instruction
convVellvmIBinop (Add nuw nsw) = LL.Add nsw nuw
convVellvmIBinop (Sub nuw nsw) = LL.Sub nsw nuw
convVellvmIBinop (Mul nuw nsw) = LL.Mul nsw nuw
convVellvmIBinop (Shl nuw nsw) = LL.Shl nsw nuw
convVellvmIBinop (UDiv exact) = LL.UDiv exact
convVellvmIBinop (SDiv exact) = LL.SDiv exact
convVellvmIBinop (LShr exact) = LL.LShr exact
convVellvmIBinop (AShr exact) = LL.AShr exact
convVellvmIBinop URem = LL.URem
convVellvmIBinop SRem = LL.SRem
convVellvmIBinop And = LL.And
convVellvmIBinop Or = LL.Or
convVellvmIBinop Xor = LL.Xor

convVellvmTExp :: (Typ, Exp Typ) -> LL.Operand
convVellvmTExp (t, EXP_Ident (ID_Local id)) = LL.LocalReference (convVellvmTyp t) (convVellvmId id)
convVellvmTExp e = LL.ConstantOperand (convVellvmConstant e)

convVellvmConstant :: (Typ, Exp Typ) -> LLC.Constant
convVellvmConstant (TYPE_I n, EXP_Integer i) = LLC.Int (nWord n) i
convVellvmConstant (t, EXP_Float f) = error "unsupported type"
convVellvmConstant (t, EXP_Double f) = error "unsupported type"
convVellvmConstant (t, EXP_Hex f) = error "unsupported type"
convVellvmConstant (t, EXP_Bool f) = error "unsupported type"
convVellvmConstant (t, EXP_Null) = LLC.Null (convVellvmTyp t)
convVellvmConstant (t, EXP_Zero_initializer) = LLC.AggregateZero (convVellvmTyp t)
convVellvmConstant (t, EXP_Cstring s) = error "unsupported type"
convVellvmConstant (t, EXP_Undef) = LLC.Undef (convVellvmTyp t)
convVellvmConstant (t, EXP_Struct flds) = LLC.Struct Nothing False (convVellvmConstant <$> flds)
convVellvmConstant (t, EXP_Packed_struct flds) = LLC.Struct Nothing True (convVellvmConstant <$> flds)
convVellvmConstant (t, EXP_Array elms) = LLC.Array (convVellvmTyp t) (convVellvmConstant <$> elms)
convVellvmConstant (t, EXP_Vector elms) = LLC.Vector (convVellvmConstant <$> elms)
convVellvmConstant _ = error "not an expression"
