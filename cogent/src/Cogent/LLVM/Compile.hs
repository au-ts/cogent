module Cogent.LLVM.Compile (toLLVM) where

import Cogent.Common.Syntax (VarName)
import Cogent.Core as Core
import Cogent.LLVM.CCompat (auxCFFIDef)
import Cogent.LLVM.CodeGen (def, toShortBS)
import Cogent.LLVM.Expr (exprToLLVM)
import Cogent.LLVM.Types (toLLVMType)
import qualified Data.ByteString.Char8 as BS
import Data.ByteString.Short.Internal (ShortByteString)
import Data.Maybe (mapMaybe)
import LLVM.AST as AST
import LLVM.AST.DataLayout (Endianness (LittleEndian), defaultDataLayout)
import LLVM.AST.Global (Global (..))
import LLVM.Context (withContext)
import LLVM.Module (moduleLLVMAssembly, withModuleFromAST)
import System.FilePath (replaceExtension)
import System.IO (Handle, IOMode (WriteMode), hClose, openFile)

mkModule :: ShortByteString -> ShortByteString -> [AST.Definition] -> AST.Module
mkModule moduleName fileName defs =
  defaultModule
    { moduleName = moduleName
    , moduleSourceFileName = fileName
    , moduleDataLayout = Just (defaultDataLayout LittleEndian)
    , moduleDefinitions = defs
    }

toLLVMDef :: Core.Definition Core.TypedExpr VarName VarName -> AST.Definition
toLLVMDef (AbsDecl _ name _ _ t rt) =
  GlobalDefinition
    ( functionDefaults
        { name = Name (toShortBS name)
        , parameters = ([Parameter (toLLVMType t) (UnName 0) []], False)
        , returnType = toLLVMType rt
        , basicBlocks = []
        }
    )
toLLVMDef (FunDef _ name _ _ t rt body) =
  def
    (toShortBS name)
    [Parameter (toLLVMType t) (UnName 0) []]
    (toLLVMType rt)
    (exprToLLVM body)
toLLVMDef (TypeDef name _ mt) =
  TypeDefinition
    (Name (toShortBS name))
    (fmap toLLVMType mt)

toMod :: [Core.Definition Core.TypedExpr VarName VarName] -> FilePath -> AST.Module
toMod ds source =
  mkModule
    (toShortBS source)
    (toShortBS source)
    (map toLLVMDef ds ++ mapMaybe auxCFFIDef ds)

writeLLVM :: AST.Module -> Handle -> IO ()
writeLLVM mod file =
  withContext
    ( \ctx ->
        ( do
            ir <- withModuleFromAST ctx mod moduleLLVMAssembly
            BS.hPut file ir
        )
    )

toLLVM :: [Core.Definition Core.TypedExpr VarName VarName] -> FilePath -> IO ()
toLLVM monoed source = do
  let ast = toMod monoed source
  let resName = replaceExtension source "ll"
  outFile <- openFile resName WriteMode
  writeLLVM ast outFile
  hClose outFile
  return ()
