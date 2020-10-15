{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.Compile (toLLVM) where

import Cogent.Common.Syntax (VarName)
import Cogent.Core as Core
import Cogent.LLVM.CCompat (auxCFFIDef)
import Cogent.LLVM.Expr (exprToLLVM, monomorphicTypeDef)
import Cogent.LLVM.Types (toLLVMType)
import Control.Monad (void, (>=>))
import qualified Data.ByteString.Char8 as BS
import Data.ByteString.Internal (packChars)
import Data.ByteString.Short.Internal (toShort)
import Debug.Trace (traceShowId)
import LLVM.AST (Module (moduleSourceFileName), mkName)
import LLVM.Context (withContext)
import LLVM.IRBuilder.Instruction (ret)
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad (block, named)
import LLVM.Module (moduleLLVMAssembly, withModuleFromAST)
import System.FilePath (replaceExtension)
import System.IO (Handle, IOMode (WriteMode), hClose, openFile)

toLLVMDef :: Definition TypedExpr VarName VarName -> ModuleBuilder ()
toLLVMDef f@(FunDef _ name _ _ t rt body) =
  void $
    function
      (mkName name)
      [(toLLVMType t, NoParameterName)]
      (toLLVMType rt)
      ((\vars -> block `named` "entry" >> exprToLLVM body vars) >=> ret)
      >> auxCFFIDef f
toLLVMDef (AbsDecl _ name _ _ t rt) =
  void $
    extern
      (mkName name)
      [toLLVMType t]
      (toLLVMType rt)
      >> monomorphicTypeDef t
      >> monomorphicTypeDef rt
-- don't declare now, instead declare a monomorphic one when we see the type used
toLLVMDef TypeDef {} = pure ()

writeLLVM :: Module -> Handle -> IO ()
writeLLVM mod file =
  withContext $
    \ctx ->
      withModuleFromAST ctx mod moduleLLVMAssembly
        >>= \ir -> BS.hPut file ir

toLLVM :: [Definition TypedExpr VarName VarName] -> FilePath -> IO ()
toLLVM monoed source = do
  let sourceFilename = toShort (packChars source)
      ast =
        (buildModule sourceFilename (mapM_ toLLVMDef (traceShowId monoed)))
          { moduleSourceFileName = sourceFilename
          }
      resName = replaceExtension source "ll"
  outFile <- openFile resName WriteMode
  writeLLVM ast outFile
  hClose outFile
  return ()
