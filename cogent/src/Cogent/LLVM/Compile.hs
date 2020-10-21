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
import Cogent.LLVM.CCompat (wrapC, wrapLLVM)
import Cogent.LLVM.CHeader (createCHeader)
import Cogent.LLVM.Custom (function)
import Cogent.LLVM.Expr (exprToLLVM, monomorphicTypeDef)
import Cogent.LLVM.Types (toLLVMType)
import Cogent.Util (toCName)
import Control.Monad (void, (>=>))
import qualified Data.ByteString.Char8 as BS
import Data.ByteString.Internal (packChars)
import Data.ByteString.Short.Internal (toShort)
import LLVM.AST (Module (moduleSourceFileName), mkName, moduleTargetTriple)
import LLVM.Context (withContext)
import LLVM.IRBuilder.Instruction (ret)
import LLVM.IRBuilder.Module (ModuleBuilder, buildModule)
import LLVM.IRBuilder.Monad (block, named)
import LLVM.Module (moduleLLVMAssembly, withModuleFromAST)
import LLVM.Target (getDefaultTargetTriple)
import System.FilePath (replaceExtension)
import System.IO (Handle, IOMode (WriteMode), hClose, openFile)

-- Given a single Cogent definition, emit an LLVM definition
toLLVMDef :: Definition TypedExpr VarName VarName -> ModuleBuilder ()
-- For function declarations, emit a function definition that contains the
-- translated LLVM body inside an entry block
-- Additionally, emit a wrapper function which allows the original to be called
-- from C code
toLLVMDef (FunDef _ name _ _ t rt body) =
  void $
    function
      -- append .llvm to end of fn name for non-wrapped version
      (mkName (toCName name ++ ".llvm"))
      [(toLLVMType t, [])]
      (toLLVMType rt)
      ((\vars -> block `named` "entry" >> exprToLLVM body vars) >=> ret)
      >> wrapLLVM (toCName name) t rt
-- For abstract declarations, emit an extern definition and also create
-- monomorphised typedefs for any abstract types that appear in the function
-- signature
toLLVMDef (AbsDecl _ name _ _ t rt) =
  wrapC (toCName name) t rt
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
        >>= BS.hPut file

-- Take a list of Cogent definitions and output the resultant module to a file
toLLVM :: [Definition TypedExpr VarName VarName] -> FilePath -> IO ()
toLLVM monoed source = do
  target <- getDefaultTargetTriple
  let sourceFilename = toShort (packChars source)
      ast =
        (buildModule sourceFilename (mapM_ toLLVMDef monoed))
          { moduleSourceFileName = sourceFilename
          , moduleTargetTriple = Just target
          }
      resName = replaceExtension source "ll"
      hName = replaceExtension source "h"
      base = replaceExtension source ""
  outFile <- openFile resName WriteMode
  writeLLVM ast outFile
  hClose outFile
  writeFile hName (createCHeader monoed base)
  return ()
