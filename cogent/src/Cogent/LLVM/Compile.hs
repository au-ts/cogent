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
{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.Compile (toLLVM) where

-- This module provides the external interface to the LLVM backend for Cogent

import Cogent.Common.Syntax (VarName)
import Cogent.Core as Core (Definition (..), TypedExpr)
import Cogent.LLVM.CCompat (auxCFFIDef)
import Cogent.LLVM.Expr (exprToLLVM, monomorphicTypeDef)
import Cogent.LLVM.Types (toLLVMType)
import Control.Monad (void, (>=>))
import qualified Data.ByteString.Char8 as BS
import Data.ByteString.Internal (packChars)
import Data.ByteString.Short.Internal (toShort)
import LLVM.AST (Module (moduleSourceFileName), mkName)
import LLVM.Context (withContext)
import LLVM.IRBuilder.Instruction (ret)
import LLVM.IRBuilder.Module
import LLVM.IRBuilder.Monad (block, named)
import LLVM.Module (moduleLLVMAssembly, withModuleFromAST)
import System.FilePath (replaceExtension)
import System.IO (Handle, IOMode (WriteMode), hClose, openFile)

-- Given a single Cogent definition, emit an LLVM definition
toLLVMDef :: Definition TypedExpr VarName VarName -> ModuleBuilder ()
-- For function declarations, emit a function definition that contains the
-- translated LLVM body inside an entry block
-- Additionally, emit a wrapper function which allows the original to be called
-- from C code
toLLVMDef f@(FunDef _ name _ _ t rt body) =
  void $
    function
      (mkName name)
      [(toLLVMType t, NoParameterName)]
      (toLLVMType rt)
      ((\vars -> block `named` "entry" >> exprToLLVM body vars) >=> ret)
      >> auxCFFIDef f
-- For abstract declarations, emit an extern definition and also create
-- monomorphised typedefs for any abstract types that appear in the function
-- signature
toLLVMDef (AbsDecl _ name _ _ t rt) =
  void $
    extern
      (mkName name)
      [toLLVMType t]
      (toLLVMType rt)
      >> monomorphicTypeDef t
      >> monomorphicTypeDef rt
-- Don't declare typedefs now, instead declare a monomorphic one when we see the
-- type actually used
toLLVMDef TypeDef {} = pure ()

-- Write an LLVM module to a file handle
writeLLVM :: Module -> Handle -> IO ()
writeLLVM mod file =
  withContext $
    \ctx ->
      withModuleFromAST ctx mod moduleLLVMAssembly
        >>= \ir -> BS.hPut file ir

-- Take a list of Cogent definitions and output the resultant module to a file
toLLVM :: [Definition TypedExpr VarName VarName] -> FilePath -> IO ()
toLLVM monoed source = do
  let sourceFilename = toShort (packChars source)
      ast =
        (buildModule sourceFilename (mapM_ toLLVMDef monoed))
          { moduleSourceFileName = sourceFilename
          }
      resName = replaceExtension source "ll"
  outFile <- openFile resName WriteMode
  writeLLVM ast outFile
  hClose outFile
  return ()
