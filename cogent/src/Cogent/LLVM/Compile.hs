{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Cogent.LLVM.Compile where

import           Control.Applicative
import           Control.Monad.State

import           System.FilePath
import           System.IO

import           Data.ByteString                as BS
import           Data.ByteString.Internal
import           Data.ByteString.Short.Internal
import           Data.Char
import qualified Data.Either
import           Data.Function
import           Data.List
import qualified Data.Map                       as Map
import           Data.Monoid                    ((<>))
import           Data.String
import qualified Data.Vec
import           Data.Word

import           Cogent.Common.Repr
import           Cogent.Common.Syntax           as Sy
import           Cogent.Common.Types
import           Cogent.Core                    as Core

import           LLVM.AST
import qualified LLVM.AST                       as AST
import           LLVM.AST.AddrSpace
import qualified LLVM.AST.Attribute             as A
import qualified LLVM.AST.CallingConvention     as CC
import qualified LLVM.AST.Constant              as C
import           LLVM.AST.Global
import           LLVM.AST.Instruction
import           LLVM.AST.Name
import           LLVM.AST.Operand
import           LLVM.AST.Type
import           LLVM.AST.Typed                 (typeOf)
import           LLVM.Context
import           LLVM.Module

import           Debug.Trace                    (trace)


-- Module

newtype LLVM a = LLVM (State AST.Module a)
  deriving (Functor, Applicative, Monad, MonadState AST.Module)


newModule :: ShortByteString -> ShortByteString -> AST.Module
newModule moduleName fileName = defaultModule { moduleName = moduleName
                                              , moduleSourceFileName = fileName
                                              }

expandMod :: AST.Definition -> LLVM ()
expandMod def = do
  oldDefs <- gets moduleDefinitions
  modify (\s -> s { moduleDefinitions = oldDefs ++ [def] })


def :: ShortByteString -> [(LLVM.AST.Type.Type, Name)] -> LLVM.AST.Type.Type -> (LLVM.AST.Type.Type -> Codegen a) -> LLVM ()
def dName argTys retTy body =
  let thisPtrType = LLVM.AST.Type.PointerType { pointerReferent =
                                                  FunctionType { resultType = retTy
                                                               , argumentTypes = Data.List.map fst argTys
                                                               , isVarArg = False
                                                               }
                                              , pointerAddrSpace = AddrSpace 0 }
  in let bodyBlock = genBlocks
                       (execCodegen
                         (do
                             enter <- addBlock "entry"
                             _ <- setBlock enter
                             body thisPtrType))
  in expandMod
      (GlobalDefinition
        (functionDefaults
          { LLVM.AST.Global.name = Name dName
          , parameters = ([Parameter ty an [] | (ty, an) <- argTys], False)
          , returnType = retTy
          , basicBlocks = bodyBlock}))


-- Types

intType :: Cogent.Common.Types.PrimInt -> LLVM.AST.Type.Type
intType Boolean = IntegerType 1
intType U8      = IntegerType 8
intType U16     = IntegerType 16
intType U32     = IntegerType 32
intType U64     = IntegerType 64


cogentType :: Core.Type t -> LLVM.AST.Type.Type
cogentType (TPrim p) = intType p
cogentType (TRecord ts _) = -- don't know how to deal with sigil
  StructureType { isPacked = False
                , elementTypes = [ cogentType t | (_, (t, _)) <- ts ]
                }
cogentType (TUnit) = VoidType
cogentType (TProduct a b) = StructureType { isPacked = False
                                        , elementTypes = [ cogentType a, cogentType b ]
                                        }
cogentType (TString )= LLVM.AST.Type.PointerType { pointerReferent = IntegerType 8 }
#ifdef BUILTIN_ARRAYS
cogentType (TArray t s) = ArrayType { nArrayElements = s
                                  , elementType = cogentType t
                                  }
#endif
cogentType _         = VoidType


-- Name

type Names = Map.Map ShortByteString Int

newName :: ShortByteString -> Names -> (ShortByteString, Names)
newName name scope =
  case Map.lookup name scope of
    Nothing -> (name, Map.insert name 1 scope)
    Just i  -> (name <> fromString (show i), Map.insert name (i + 1) scope)

type Binding = [(ShortByteString, Operand)]

-- Codegen

data BlockState = BlockState
    { idx    :: Int
    , instrs :: [Named Instruction]
    , term   :: Maybe (Named Terminator)
    }
    deriving (Show)

data CodegenState = CodegenState
    { currentBlock :: Name
    , blocks       :: Map.Map Name BlockState
    , binding      :: Binding
    , blockCount   :: Int
    , unnamedCount :: Word
    , names        :: Names
    , indexing     :: [Operand]
    }
    deriving (Show)

newtype Codegen a = Codegen { cg :: State CodegenState a }
  deriving (Functor, Applicative, Monad, MonadState CodegenState)





genBlocks :: CodegenState -> [BasicBlock]
genBlocks m = Data.List.map mkBlock (sortBy (compare `on` (idx . snd))
                           (Map.toList (blocks m)))

mkBlock :: (Name, BlockState) -> BasicBlock
mkBlock (name, (BlockState _ instrs term)) =
  let t = (case term of
             Just t  -> t
             Nothing -> error ((show name) ++ " has no terminator"))
  in BasicBlock name instrs t

newBlock :: Int -> BlockState
newBlock i = BlockState i [] Nothing

cgInit :: CodegenState
cgInit = CodegenState (Name "entry") Map.empty [] 1 0 Map.empty []

execCodegen :: Codegen a -> CodegenState
execCodegen m = execState (cg m) cgInit

fresh :: Codegen Word
fresh = do
  i <- gets unnamedCount
  modify (\s -> s {unnamedCount = i + 1})
  return (i + 1)

instr :: LLVM.AST.Type.Type -> Instruction -> Codegen (Operand)
instr ty ins = do
  n <- fresh
  let localRef = (UnName n)
  blk <- current
  let i = instrs blk
  modifyBlock (blk {instrs = i ++ [(localRef := ins)] })
  return (LocalReference ty localRef)


unnamedInstr :: Instruction -> Codegen ()
unnamedInstr ins = do
  blk <- current
  let i = instrs blk
  modifyBlock (blk {instrs = i ++ [(Do ins)]})


terminator :: Named Terminator -> Codegen (Named Terminator)
terminator term = do
  blk <- current
  modifyBlock (blk {term = Just term})
  return term

entry :: Codegen Name
entry = gets currentBlock

current :: Codegen BlockState
current = do
  c <- gets currentBlock
  blks <- gets blocks
  case Map.lookup c blks of
    Just x  -> return x
    Nothing -> error ("Cannot find block: " ++ (show c))

modifyBlock :: BlockState -> Codegen ()
modifyBlock newBlk = do
  current <- gets currentBlock
  modify (\s -> s {blocks = Map.insert current newBlk (blocks s)})

addBlock :: ShortByteString -> Codegen Name
addBlock blkName = do
  bs <- gets blocks
  ix <- gets blockCount
  ns <- gets names
  let new = newBlock ix
      (name, newNames) = newName blkName ns
  modify (\s -> s { blocks = Map.insert (Name name) new bs
                  , blockCount = ix + 1
                  , names = newNames
                  })
  return (Name name)

setBlock :: Name -> Codegen Name
setBlock blkName = do
  modify (\s -> s { currentBlock = blkName })
  return blkName

rec_type :: TypedExpr t v a -> [LLVM.AST.Type.Type]
rec_type (TE rect _) = case rect of
                   (TRecord flds _) -> Data.List.map (\f -> cogentType (fst (snd f))) flds
                   _ -> error "cannot get record type from a non-record type"


expr_to_llvm :: Core.TypedExpr t v a -> Codegen (Either Operand (Named Terminator))
expr_to_llvm (TE _ (ILit int bits)) =
  return (Left (case bits of
             Boolean -> ConstantOperand C.Int { C.integerBits = 1, C.integerValue = int }
             U8 -> ConstantOperand C.Int { C.integerBits = 8, C.integerValue = int }
             U16 -> ConstantOperand C.Int { C.integerBits = 16, C.integerValue = int }
             U32 -> ConstantOperand C.Int { C.integerBits = 32, C.integerValue = int }
             U64 -> ConstantOperand C.Int { C.integerBits = 64, C.integerValue = int }))
expr_to_llvm (TE _ (SLit str)) =
  return (Left (ConstantOperand C.Array { C.memberType = IntegerType 8
                                        , C.memberValues = [ C.Int { C.integerBits = 8, C.integerValue = toInteger(ord c)} | c <- str]
                                        }))

expr_to_llvm (TE rt (Op op [a,b])) =
  do _oa <- expr_to_llvm a
     _ob <- expr_to_llvm b
      -- If the operands are known at compile time, should we evaluate the expression here? / z.shang
     res <- let oa = Data.Either.fromLeft (error "operand of OP cannot be terminator") _oa
                ob = Data.Either.fromLeft (error "operand of OP cannot be terminator") _ob
              in case op of
                     Sy.Plus -> instr (trace ("cogentType of rt: " ++ (show (cogentType rt))) (cogentType (trace ("Plus rt: " ++ (show rt)) rt))) (Add { nsw = False
                                                           , nuw = True
                                                           , operand0 = (trace ("plus oa: " ++ (show oa)) oa)
                                                           , operand1 = (trace ("plus ob: " ++ (show ob)) ob)
                                                           , LLVM.AST.Instruction.metadata = []
                                                           })
                     Sy.Minus -> instr (cogentType rt) (Sub { nsw = False
                                                            , nuw = True
                                                            , operand0 = oa
                                                            , operand1 = ob
                                                            , LLVM.AST.Instruction.metadata = []
                                                            })
                     Sy.Times -> instr (cogentType rt) (Mul { nsw = False
                                                            , nuw = True
                                                            , operand0 = oa
                                                            , operand1 = ob
                                                            , LLVM.AST.Instruction.metadata = []
                                                            })
                     Sy.Divide -> instr (cogentType rt) (SDiv { exact = False -- Or should we do more check here?
                                                              , operand0 = oa
                                                              , operand1 = ob
                                                              , LLVM.AST.Instruction.metadata = []
                                                              })
                     Sy.Mod -> instr (cogentType rt) (SRem { operand0 = oa
                                                           , operand1 = ob
                                                           , LLVM.AST.Instruction.metadata = []
                                                           })
                     Sy.And -> instr (cogentType rt) (LLVM.AST.Instruction.And { operand0 = oa
                                                                               , operand1 = ob
                                                                               , LLVM.AST.Instruction.metadata = []} )
                     Sy.Or -> instr (cogentType rt) (LLVM.AST.Instruction.Or { operand0 = oa
                                                                             , operand1 = ob
                                                                             , LLVM.AST.Instruction.metadata = []} )
                     Sy.Gt -> error "not implemented yet"
                     Sy.Lt-> error "not implemented yet"
                     Sy.Ge -> error "not implemented yet"
                     Sy.Le -> error "not implemented yet"
                     Sy.Eq -> error "not implemented yet"
                     Sy.NEq -> error "not implemented yet"
                     Sy.BitAnd-> error "not implemented yet"
                     Sy.BitOr-> error "not implemented yet"
                     Sy.BitXor-> error "not implemented yet"
                     Sy.LShift-> error "not implemented yet"
                     Sy.RShift-> error "not implemented yet"
                     Sy.Complement-> error "not implemented yet"
                     Sy.Not -> error "Not is not defined to be binary"
     return (Left (trace ("op res: " ++ (show res)) res))
expr_to_llvm (TE _ (Take (a, b) recd fld body)) =
  do
    _recv <- (expr_to_llvm recd)
    let recv = Data.Either.fromLeft (error "address cannot be terminator") _recv
    fldvp <- instr (trace ("FLD TYPE: " ++ (show ((trace ("REC TYPE: " ++ (show (rec_type recd))) (rec_type recd)) !! (trace ("FLD: " ++ (show fld)) fld))))
                   ((rec_type recd) !!  fld)
                  )
                  (GetElementPtr { inBounds = True
                                 , address = recv
                                 , indices = [
                                     ConstantOperand
                                               C.Int { C.integerBits = 32
                                                     , C.integerValue = toInteger 0 }
                                             ,
                                     ConstantOperand
                                               C.Int { C.integerBits = 32
                                                     , C.integerValue = toInteger fld }

                                             ]
                                 , LLVM.AST.Instruction.metadata = []
                                 })
    fldv <- instr ((rec_type recd) !! fld) (LLVM.AST.Instruction.Load { volatile = False
                                                                      , address = fldvp
                                                                      , maybeAtomicity = Just (LLVM.AST.Instruction.System, LLVM.AST.Instruction.Monotonic)
                                                                      , LLVM.AST.Instruction.alignment = 1
                                                                      , LLVM.AST.Instruction.metadata = []
                                                                      })
    vars <- gets indexing
    modify (\s -> s { indexing = [fldv, recv] ++ vars })
    res <- expr_to_llvm body
    case (trace ("res: " ++ (show res)) res) of
      Left val -> ((terminator (Do (Ret (Just val) [])) ) >>= (\a -> return (Right a)))
      Right trm -> return (Right trm)



expr_to_llvm r@(TE rect (Struct flds)) =
  do
    struct <- instr (LLVM.AST.Type.PointerType { pointerReferent = (cogentType rect) })
                    (Alloca { allocatedType = (cogentType rect)
                            , LLVM.AST.Instruction.alignment = 4
                            })
    let fldvs = [ (i, expr_to_llvm (snd fld)) | (i, fld) <- Data.List.zip [0..] flds] in
      (Data.List.foldr (>>) (pure struct)
                           [ (do
                                 elmptr <- (instr ((rec_type r) !! i)
                                            (GetElementPtr { inBounds = True
                                                           , address = struct
                                                           , indices = [ConstantOperand
                                                                         C.Int { C.integerBits = 64
                                                                               , C.integerValue = 0}
                                                                       , ConstantOperand
                                                                         C.Int { C.integerBits = 64
                                                                               , C.integerValue = toInteger i}
                                                                       ]}))
                                 fldv >>= (\v -> instr ((rec_type r) !! i) (Store { address = elmptr
                                                                                  , LLVM.AST.Instruction.value = (Data.Either.fromLeft (error "field value cannot be terminator") v)
                                                                                  , LLVM.AST.Instruction.alignment = 4})))
                           | (i, fldv) <- fldvs ]) >>= (\a -> return (Left a))



expr_to_llvm (TE vt (Variable (idx, _))) =
  do
    unnames <- gets unnamedCount
    _indexing <- gets indexing
    let indexing = (trace ("indexing: " ++ (show _indexing)) _indexing) in
      let _idx = (trace ("var idx: " ++ (show (Data.Vec.finInt idx))) (Data.Vec.finInt idx)) in
        if (Data.List.null indexing) then
          let pos = (fromIntegral unnames) - _idx in
            return (Left (LocalReference (cogentType vt) (UnName (fromIntegral pos))))
        else return (Left (indexing !! _idx))
    -- error ("variable not implemented yet. idx: " ++ show idx ++  " " ++ show uname_count)

expr_to_llvm (TE _ (Fun _ _ _)) = error "fun not implemented yet"
expr_to_llvm _ = error "not implemented yet"




hasBlock :: Core.TypedExpr t v a -> Bool
hasBlock (TE _ e) = hasBlock' e

hasBlock' :: Core.Expr t v a Core.TypedExpr -> Bool
hasBlock' (Variable _) = False
hasBlock' (Fun _ _ _) = False
hasBlock' (Op _ xs) = Data.List.foldl (\a b-> a || hasBlock b) False xs
hasBlock' (App a b) = hasBlock a || hasBlock b
hasBlock' (Con _ _ _) = False
hasBlock' (Unit) = False
hasBlock' (ILit _ _) = False
hasBlock' (SLit _) = False
#ifdef BUILTIN_ARRAYS
hasBlock' (ALit xs) = Data.List.foldl (\a b-> a || hasBlock b) False xs
hasBlock' (ArrayIndex _ _) = False
hasBlock' (Singleton _) = False
#endif
hasBlock' (Tuple a b) = hasBlock a || hasBlock b
hasBlock' (Struct xs) = Data.List.foldl (\a b-> a || hasBlock (snd b)) False xs
hasBlock' (Esac _) = False
hasBlock' (Core.Member a _) = hasBlock a
hasBlock' (Put a _ b) = hasBlock a || hasBlock b
hasBlock' (Promote _ e) = hasBlock e
hasBlock' (Cast _ e) = hasBlock e
hasBlock' _ = True


toLLVMDef :: Core.Definition Core.TypedExpr VarName -> LLVM ()
toLLVMDef (AbsDecl attr name ts t rt) =
    expandMod (GlobalDefinition
               (functionDefaults { LLVM.AST.Global.name = Name (toShort (Data.ByteString.Internal.packChars name))
                                 , parameters = ([Parameter (cogentType t) (UnName 0) []], False)
                                 , returnType = cogentType rt
                                 , basicBlocks = []
                                 }))
-- if passing in struct, it should be a pointer
toLLVMDef (FunDef attr name ts t rt body) =
  def (toShort (Data.ByteString.Internal.packChars name))
      [((LLVM.AST.PointerType { pointerReferent = (cogentType t)
                              , pointerAddrSpace = AddrSpace 0}),
         (UnName 0))]
      (cogentType rt)
      (\ptr -> (expr_to_llvm body))
    --expandMod (GlobalDefinition
    --           (functionDefaults { LLVM.AST.Global.name = Name (toShort (Data.ByteString.Internal.packChars name))
     --                            , parameters = ([Parameter (cogentType t) "" []], False)
      --                           , returnType = cogentType rt
       --                          , basicBlocks = genBlocks (execCodegen (expr_to_llvm body))
        --                         })
         --     )

toLLVMDef _ = error "not implemented yet"


to_mod :: [Core.Definition Core.TypedExpr VarName] -> FilePath -> AST.Module
to_mod (x:xs) source = to_mod' (toLLVMDef x) (to_mod xs source)
  where to_mod' (LLVM m) mod = execState m mod
to_mod [] source = (newModule (toShort (Data.ByteString.Internal.packChars source))
  (toShort (Data.ByteString.Internal.packChars source)))



print_llvm :: AST.Module -> IO ()
print_llvm mod = (withContext (\ctx ->
                                 (do
                                     ir <- (withModuleFromAST ctx mod moduleLLVMAssembly)
                                     (BS.putStrLn ir))))


to_llvm :: [Core.Definition Core.TypedExpr VarName] -> FilePath -> IO ()
to_llvm monoed source = do
  System.IO.putStrLn "Showing AST"
  let ast =  to_mod monoed source
  System.IO.putStrLn (show ast)
  print_llvm ast

