{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module Cogent.LLVM.Compile where

import           Cogent.Common.Syntax           (VarName)
import qualified Cogent.Common.Syntax           as Sy (Op (..))
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.Core                    as Core
import           Data.Fin                       (finInt)
import qualified Data.Vec

import           Control.Applicative
import           Control.Monad.State
import           Data.ByteString.Char8          as BS
import           Data.ByteString.Internal
import           Data.ByteString.Short.Internal
import           Data.Char
import           Data.Either                    (fromLeft)
import           Data.Function
import           Data.List
import qualified Data.Map                       as Map
import           Data.Monoid                    ((<>))
import           Data.String
import           Data.Word
import           LLVM.AST                       as AST
import           LLVM.AST.AddrSpace
import qualified LLVM.AST.Constant              as C
import           LLVM.AST.DataLayout            (defaultDataLayout, Endianness (LittleEndian))
import           LLVM.AST.Global                (Global (..))
import           LLVM.AST.Instruction
import           LLVM.AST.IntegerPredicate      as IntP
import           LLVM.AST.Typed                 (typeOf)
import           LLVM.Context                   (withContext)
import           LLVM.Module                    (moduleLLVMAssembly, withModuleFromAST)
import           System.FilePath
import           System.Info
import           System.IO

import           Debug.Trace                    (trace)


-- Module

mkModule :: ShortByteString -> ShortByteString -> [AST.Definition] -> AST.Module
mkModule moduleName fileName defs =
  defaultModule { moduleName = moduleName
                , moduleSourceFileName = fileName
                , moduleDataLayout = Just (defaultDataLayout LittleEndian)
                , moduleDefinitions = defs
                }

def :: ShortByteString
    -> [(AST.Type, Name)]
    -> AST.Type
    -> (AST.Type -> Codegen (Either Operand (Named Terminator)))
    -> AST.Definition
def dName argTys retTy body =
  let thisPtrType = PointerType { pointerReferent =
                                    FunctionType { resultType = retTy
                                                 , argumentTypes = Data.List.map fst argTys
                                                 , isVarArg = False
                                                 }
                                , pointerAddrSpace = AddrSpace 0 }
      bodyBlock = genBlocks
                    (execCodegen
                      (do enter <- addBlock "entry"
                          setBlock enter
                          body_exp <- body thisPtrType
                          case body_exp of
                            Right trm -> terminator trm
                            Left val -> terminator (Do (Ret (Just val) []))
                      ))
  in GlobalDefinition
        (functionDefaults
          { name = Name dName
          , parameters = ([Parameter ty an [] | (ty, an) <- argTys], False)
          , returnType = retTy
          , basicBlocks = bodyBlock})


-- Types

toLLVMInt :: Cogent.Common.Types.PrimInt -> AST.Type
toLLVMInt Boolean = IntegerType 1
toLLVMInt U8      = IntegerType 8
toLLVMInt U16     = IntegerType 16
toLLVMInt U32     = IntegerType 32
toLLVMInt U64     = IntegerType 64


toLLVMType :: Core.Type t b -> AST.Type
toLLVMType (TPrim p) = toLLVMInt p
toLLVMType (TRecord _ ts _) = -- don't know how to deal with sigil, also not handling recursive types
  StructureType { isPacked = False
                , elementTypes = [ toLLVMType t | (_, (t, _)) <- ts ]
                }
toLLVMType (TUnit) = VoidType
toLLVMType (TProduct a b) = StructureType { isPacked = False
                                          , elementTypes = [ toLLVMType a, toLLVMType b ]
                                          }
toLLVMType (TString )= PointerType { pointerReferent = IntegerType 8, pointerAddrSpace = AddrSpace 0 }
toLLVMType (TSum ts) =
  let types = [ t | (_, (t, _)) <- ts ] in
      let maxType = Data.List.foldl (\a b -> if typeSize a > typeSize b then a else b) (TUnit) types in
          StructureType { isPacked = False
                        , elementTypes = [ IntegerType 32 -- default 32 bit tag
                                         , toLLVMType maxType ]}
#ifdef BUILTIN_ARRAYS
toLLVMType (TArray t l s mh) =
  ArrayType { nArrayElements = __todo "toLLVMType: we cannot evaluate LExpr to a constant"
            , elementType = toLLVMType t
            }
#endif
toLLVMType _ = VoidType

typeSize :: Core.Type t b -> Int
typeSize (TPrim p) = case p of
                       Boolean -> 1
                       U8 -> 8
                       U16 -> 16
                       U32 -> 32
                       U64 -> 64
typeSize (TUnit) = 0
typeSize _ = 32 -- assuming 32 bit machine


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

instr :: AST.Type -> Instruction -> Codegen (Operand)
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

recordType :: TypedExpr t v a b -> [AST.Type]
recordType (TE rect _) = case rect of
                   (TRecord _ flds _) -> Data.List.map (\f -> toLLVMType (fst (snd f))) flds
                   _ -> error "cannot get record type from a non-record type"


exprToLLVM :: Core.TypedExpr t v a b -> Codegen (Either Operand (Named Terminator))
exprToLLVM (TE t Unit) = return (Left (ConstantOperand C.Undef { C.constantType = toLLVMType t }))

exprToLLVM (TE _ (ILit int bits)) =
  return (Left (case bits of
             Boolean -> ConstantOperand C.Int { C.integerBits = 1, C.integerValue = int }
             U8 -> ConstantOperand C.Int { C.integerBits = 8, C.integerValue = int }
             U16 -> ConstantOperand C.Int { C.integerBits = 16, C.integerValue = int }
             U32 -> ConstantOperand C.Int { C.integerBits = 32, C.integerValue = int }
             U64 -> ConstantOperand C.Int { C.integerBits = 64, C.integerValue = int }))

exprToLLVM (TE _ (SLit str)) =
  return (Left (ConstantOperand C.Array { C.memberType = IntegerType 8
                                        , C.memberValues = [ C.Int { C.integerBits = 8, C.integerValue = toInteger(ord c)} | c <- str]
                                        }))

exprToLLVM (TE rt (Op op [a,b])) =
  do _oa <- exprToLLVM a
     _ob <- exprToLLVM b
      -- If the operands are known at compile time, should we evaluate the expression here? / z.shang
     res <- let oa = fromLeft (error "operand of OP cannot be terminator") _oa
                ob = fromLeft (error "operand of OP cannot be terminator") _ob
              in case op of
                   Sy.Plus -> instr (toLLVMType rt) (Add { nsw = False
                                                         , nuw = True
                                                         , operand0 = oa
                                                         , operand1 = ob
                                                         , metadata = []
                                                         })
                   Sy.Minus -> instr (toLLVMType rt) (Sub { nsw = False
                                                          , nuw = True
                                                          , operand0 = oa
                                                          , operand1 = ob
                                                          , metadata = []
                                                          })
                   Sy.Times -> instr (toLLVMType rt) (Mul { nsw = False
                                                          , nuw = True
                                                          , operand0 = oa
                                                          , operand1 = ob
                                                          , metadata = []
                                                          })
                   Sy.Divide -> instr (toLLVMType rt) (SDiv { exact = False -- Or should we do more check here?
                                                            , operand0 = oa
                                                            , operand1 = ob
                                                            , metadata = []
                                                            })
                   Sy.Mod -> instr (toLLVMType rt) (SRem { operand0 = oa
                                                         , operand1 = ob
                                                         , metadata = []
                                                         })
                   Sy.And -> instr (toLLVMType rt) (And { operand0 = oa
                                                        , operand1 = ob
                                                        , metadata = []} )
                   Sy.Or -> instr (toLLVMType rt) (Or { operand0 = oa
                                                      , operand1 = ob
                                                      , metadata = []} )
                   Sy.Gt -> instr (IntegerType 1) (ICmp { operand0 = oa
                                                        , operand1 = ob
                                                        , metadata = []
                                                        , iPredicate = UGT -- assuming unsigned
                                                        })
                   Sy.Lt -> instr (IntegerType 1) (ICmp { operand0 = oa
                                                        , operand1 = ob
                                                        , metadata = []
                                                        , iPredicate = ULT -- assuming unsigned
                                                        })
                   Sy.Ge -> instr (IntegerType 1) (ICmp { operand0 = oa
                                                        , operand1 = ob
                                                        , metadata = []
                                                        , iPredicate = UGE -- assuming unsigned
                                                        })
                   Sy.Le -> instr (IntegerType 1) (ICmp { operand0 = oa
                                                        , operand1 = ob
                                                        , metadata = []
                                                        , iPredicate = ULE -- assuming unsigned
                                                        })
                   Sy.Eq -> instr (IntegerType 1) (ICmp { operand0 = oa
                                                        , operand1 = ob
                                                        , metadata = []
                                                        , iPredicate = IntP.EQ -- assuming unsigned
                                                        })
                   Sy.NEq -> instr (IntegerType 1) (ICmp { operand0 = oa
                                                         , operand1 = ob
                                                         , metadata = []
                                                         , iPredicate = NE -- assuming unsigned
                                                         })
                   Sy.BitAnd-> error "not implemented yet"
                   Sy.BitOr-> error "not implemented yet"
                   Sy.BitXor-> error "not implemented yet"
                   Sy.LShift-> error "not implemented yet"
                   Sy.RShift-> error "not implemented yet"
                   Sy.Complement-> error "not implemented yet"
                   Sy.Not -> error "Not is not defined to be binary"
     return (Left res)

exprToLLVM (TE _ (Take (a, b) recd fld body)) =
  do
    _recv <- (exprToLLVM recd)
    let recv = fromLeft (error "address cannot be terminator") _recv
    fldvp <- instr ((recordType recd) !!  fld)
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
                                 , metadata = []
                                 })
    fldv <- instr ((recordType recd) !! fld) (Load { volatile = False
                                                   , address = fldvp
                                                   , maybeAtomicity = Nothing
                                                   , alignment = 4
                                                   , metadata = []
                                                   })
    vars <- gets indexing
    modify (\s -> s { indexing = [fldv, recv] ++ vars })
    res <- exprToLLVM body
    case res of
      Left val -> ((terminator (Do (Ret (Just val) [])) ) >>= (\a -> return (Right a)))
      Right trm -> return (Right trm)

exprToLLVM (TE _ (Put recd fld val)) =
  do
    _recv <- (exprToLLVM recd)
    let recv = fromLeft (error "address cannot be terminator") _recv
    _v <- (exprToLLVM val)
    let v = fromLeft (error "address cannot be terminator") _v
    fldvp <- instr ((recordType recd) !!  fld)
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
                                 , metadata = []
                                 })
    unnamedInstr  (Store { volatile = False
                         , address = fldvp
                         , value = v
                         , maybeAtomicity = Nothing
                         , alignment = 4
                         , metadata = []
                         })
    return (Left recv)

exprToLLVM (TE _ (Let _ val body)) = -- it seems that the variable name is not used here
    do
      _v <- (exprToLLVM val)
      let v = fromLeft (error "let cannot bind a terminator") _v
      vars <- gets indexing
      modify (\s -> s { indexing = [v] ++ vars })
      res <- exprToLLVM body
      case res of
        Left val -> ((terminator (Do (Ret (Just val) [])) ) >>= (\a -> return (Right a)))
        Right trm -> return (Right trm)

exprToLLVM (TE _ (LetBang _  _ val body)) = -- let! and let should be the same here
    do
      _v <- (exprToLLVM val)
      let v = fromLeft (error "let cannot bind a terminator") _v
      vars <- gets indexing
      modify (\s -> s { indexing = [v] ++ vars })
      res <- exprToLLVM body
      case res of
        Left val -> ((terminator (Do (Ret (Just val) [])) ) >>= (\a -> return (Right a)))
        Right trm -> return (Right trm)

exprToLLVM (TE _ (Promote _ e))= exprToLLVM e
  
exprToLLVM (TE rt (Con tag e t))=
  do
    res <- instr (toLLVMType rt) (Alloca { allocatedType = toLLVMType rt
                                         , numElements = Nothing
                                         , alignment = 4
                                         , metadata = []
                                         })
    v <- exprToLLVM e
    casted <- instr (PointerType { pointerReferent = toLLVMType t
                                 , pointerAddrSpace = AddrSpace 0
                                 })
                     (BitCast { operand0 = res
                              , type' = PointerType { pointerReferent = toLLVMType t
                                                                         , pointerAddrSpace = AddrSpace 0}
                              , metadata = []})
    instr (toLLVMType rt) (Store { volatile = False
                                 , address = casted
                                 , maybeAtomicity = Nothing
                                 , value = fromLeft (error "value cannot be a terminator") v
                                 , alignment = 4
                                 , metadata = []})
    return (Left res)

exprToLLVM (TE _ (If cd tb fb)) =
  do
    _cond <- (exprToLLVM cd)
    cond <- instr (IntegerType 1)
                  (ICmp { iPredicate = IntP.EQ
                        , operand0 = fromLeft (error "cond cannot be a terminator") _cond
                        , operand1 = ConstantOperand C.Int { C.integerBits = 1, C.integerValue = 1}
                        , metadata = []
                        })
    currentBlk <- gets currentBlock
    blkTrue <- addBlock "brTrue"
    blkFalse <- addBlock "brFalse"
    -- blkEnd <- addBlock "brEnd"
    setBlock blkTrue
    _tb <- (exprToLLVM tb)
    case _tb of
      Left val -> (terminator (Do (Ret (Just val) [])) )
      Right trm -> terminator trm
    setBlock blkFalse
    _fb <- (exprToLLVM fb)
    case _fb of
      Left val -> (terminator (Do (Ret (Just val) [])) )
      Right trm -> terminator trm
    setBlock currentBlk
    (terminator (Do (CondBr { condition = cond
                            , trueDest = blkTrue
                            , falseDest = blkFalse
                            , metadata' = []
                            }))) >>= (\a -> return (Right a))

exprToLLVM r@(TE rect (Struct flds)) =
  do
    struct <- instr (PointerType { pointerReferent = (toLLVMType rect) })
                    (Alloca { allocatedType = (toLLVMType rect)
                            , alignment = 4
                            })
    let fldvs = [ (i, exprToLLVM (snd fld)) | (i, fld) <- Data.List.zip [0..] flds] in
      (Data.List.foldr (>>) (pure struct)
                           [ (do
                                 elmptr <- (instr ((recordType r) !! i)
                                            (GetElementPtr { inBounds = True
                                                           , address = struct
                                                           , indices = [ConstantOperand
                                                                         C.Int { C.integerBits = 64
                                                                               , C.integerValue = 0}
                                                                       , ConstantOperand
                                                                         C.Int { C.integerBits = 64
                                                                               , C.integerValue = toInteger i}
                                                                       ]}))
                                 fldv >>= (\v -> instr ((recordType r) !! i)
                                          (Store { address = elmptr
                                                 , value = (fromLeft (error "field value cannot be terminator") v)
                                                 , alignment = 4})))
                           | (i, fldv) <- fldvs ]) >>= (\a -> return (Left a))

exprToLLVM (TE vt (Variable (idx, _))) =
  do
    unnames <- gets unnamedCount
    _indexing <- gets indexing
    let indexing = _indexing in
      let _idx = finInt idx in
        if (Data.List.null indexing) then
          let pos = (fromIntegral unnames) - _idx in
            return (Left (LocalReference (toLLVMType vt) (UnName (fromIntegral pos))))
        else return (Left (indexing !! _idx))
    -- error ("variable not implemented yet. idx: " ++ show idx ++  " " ++ show uname_count)

exprToLLVM _ = error ("not implemented yet")


hasBlock :: Core.TypedExpr t v a b -> Bool
hasBlock (TE _ e) = hasBlock' e
  where
    hasBlock' :: Core.Expr t v a b Core.TypedExpr -> Bool
    hasBlock' (Variable _) = False
    hasBlock' (Fun _ _ _ _) = False
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


toLLVMDef :: Core.Definition Core.TypedExpr VarName VarName -> AST.Definition
toLLVMDef (AbsDecl attr name ts ls t rt) =
  GlobalDefinition
    (functionDefaults { name = Name (toShort (packChars name))
                      , parameters = ([Parameter (toLLVMType t) (UnName 0) []], False)
                      , returnType = toLLVMType rt
                      , basicBlocks = []
                      })
-- if passing in struct, it should be a pointer
toLLVMDef (FunDef attr name ts ls t rt body) =
  def (toShort (packChars name))
      [(argType t, (UnName 0))]
      (argType rt)
      (\ptr -> (exprToLLVM body))
  where argType at@(TRecord {}) = (PointerType { pointerReferent = (toLLVMType at)
                                               , pointerAddrSpace = AddrSpace 0})
        argType at@(TProduct {}) = (PointerType { pointerReferent = (toLLVMType at)
                                                , pointerAddrSpace = AddrSpace 0})
        argType at = toLLVMType at

toLLVMDef (TypeDef name tyargs mt) =
  TypeDefinition (Name (toShort (packChars name)))
                 (fmap toLLVMType mt)


to_mod :: [Core.Definition Core.TypedExpr VarName VarName] -> FilePath -> AST.Module
to_mod ds source =
  mkModule (toShort (packChars source))
           (toShort (packChars source))
           (fmap toLLVMDef ds)


print_llvm :: AST.Module -> IO ()
print_llvm mod = (withContext (\ctx ->
                                 (do
                                     ir <- (withModuleFromAST ctx mod moduleLLVMAssembly)
                                     (BS.putStrLn ir))))

write_llvm :: AST.Module -> Handle -> IO()
write_llvm mod file = (withContext (\ctx ->
                                      (do
                                          ir <- (withModuleFromAST ctx mod moduleLLVMAssembly)
                                          (BS.hPut file ir))))


to_llvm :: [Core.Definition Core.TypedExpr VarName VarName] -> FilePath -> IO ()
to_llvm monoed source = do
  let ast =  to_mod monoed source
  let resName = replaceExtension source "ll"
  outFile <- openFile resName ReadWriteMode
  write_llvm ast outFile
  hClose outFile
  return ()
