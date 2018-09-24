--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

-- | Haskell FFI generator
--
-- Generates Hs functions which in turn calls generated C functions


module Cogent.Haskell.FFIGen (
  ffiHs
) where

import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Haskell.HscGen
import qualified Cogent.Haskell.HscSyntax as Hsc

import Control.Monad.Identity
import Control.Monad.Trans.Reader
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
import Text.PrettyPrint

type FFIFuncs = M.Map FunName (CType, CType)

type Gen a = ReaderT FFIFuncs Identity a

ffiHs :: FFIFuncs -> String -> String -> [CExtDecl] -> String -> Doc
ffiHs m name hscname decls log = 
  let mod = flip runReader m $ ffiModule name hscname decls
   in text "{-" $+$ text log $+$ text "-}" $+$ prettyPrim mod


ffiModule :: String -> String -> [CExtDecl] -> Gen (Module ())
ffiModule name hscname decls = do
  hs_decls <- catMaybes <$> mapM ffiDefinition decls
  let mhead = ModuleHead () (ModuleName () name) Nothing Nothing
      pragmas = [LanguagePragma () [Ident () "ForeignFunctionInterface"]]
      imps = [ ImportDecl () (ModuleName () "Foreign") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Foreign.C.Types") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () hscname) True False False Nothing (Just (ModuleName () "FFI")) Nothing
             ]
  return $ Module () (Just mhead) pragmas imps hs_decls

ffiDefinition :: CExtDecl -> Gen (Maybe (Decl ()))
ffiDefinition (CDecl (CExtFnDecl rt name [(t,_)] _)) = do
  m <- ask
  let (name',(t',rt')) = case M.lookup name m of
                           Nothing -> (name, (t,rt))
                           Just ts -> ("ffi_" ++ name, ts)
      hs_t  = hsc2hsType $ hscType t'
      hs_rt = hsc2hsType $ hscType rt'
  return . Just $ 
    ForImp () (CCall ())
              (Just $ PlayRisky ())
              (Just name')
              (Ident () $ "cogent_" ++ name')
              (TyFun () hs_t hs_rt)
ffiDefinition _ = return Nothing

hsc2hsType :: Hsc.Type -> Type ()
hsc2hsType (Hsc.TyCon n ts)
  = mkTyCon (TyCon () $ Qual () (ModuleName () "FFI") (Ident () n))
            (map hsc2hsType ts)
hsc2hsType (Hsc.TyVar v) = TyVar () (Ident () v)
hsc2hsType (Hsc.TyTuple ts) = TyTuple () Boxed $ map hsc2hsType ts

mkTyCon :: Type () -> [Type ()] -> Type ()
mkTyCon t xs = foldl (TyApp ()) t xs
