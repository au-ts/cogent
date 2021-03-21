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
import Cogent.Util (concatMapM)
import qualified Cogent.Haskell.HscSyntax as Hsc

import Control.Monad.Identity
import Control.Monad.Trans.Reader
import qualified Data.Map as M
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
import Text.PrettyPrint

import Debug.Trace

type FFIFuncs = M.Map FunName (CType, CType)

type Gen a = ReaderT (FFIFuncs, [FunName]) Identity a

ffiHs :: FFIFuncs -> String -> String -> [CExtDecl] -> String -> (String, Module ())
ffiHs m name hscname decls log 
    = let mod = flip runReader (m, map ("ffi_" ++) $ M.keys m) $ ffiModule name hscname decls
        in (render $ text "{-" $+$ text log $+$ text "-}" $+$ prettyPrim mod, mod)


ffiModule :: String -> String -> [CExtDecl] -> Gen (Module ())
ffiModule name hscname decls = do
  hs_decls <- concatMapM ffiDefinition decls
  let mhead = ModuleHead () (ModuleName () name) Nothing Nothing
      pragmas = [LanguagePragma () [Ident () "ForeignFunctionInterface"]]
      imps = [ ImportDecl () (ModuleName () "Foreign") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Foreign.C.Types") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Util") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () hscname) False False False Nothing (Just (ModuleName () "FFI")) Nothing
             , ImportDecl () (ModuleName () (hscname ++ "_Abs")) False False False Nothing (Just (ModuleName () "FFI")) Nothing
             ]
  return $ Module () (Just mhead) pragmas imps hs_decls

ffiDefinition :: CExtDecl -> Gen [Decl ()]
ffiDefinition (CDecl (CExtFnDecl rt name [(t,_)] _)) = do
  (m, ffis) <- ask
  if name `elem` ffis then return []  -- This is an FFI function for another function.
  else do  -- Origin Cogent functions
    let (name',(t',rt')) = case M.lookup name m of
                             Nothing -> (name, (t,rt))
                             Just ts -> ("ffi_" ++ name, ts)
        hs_t  = hsc2hsType $ hscType t'
        hs_rt = hsc2hsType $ hscType rt'
    return [ ForImp () (CCall ())
               (Just $ PlayRisky ())
               (Just name')
               (Ident () $ "cogent_" ++ name)
               (TyFun () hs_t (inIO hs_rt))
           -- NOTE: The return type of these functions are barely @IO ()@ and thus don't meet
           --       what @FinalizerPtr a = FunPtr (Ptr a -> IO ())@ wants. / zilinc
           -- , ForImp () (CCall ())
           --     (Nothing)
           --     (Just $ '&':name')
           --     (Ident () $ "p_cogent_" ++ name)
           --     (mkTyCon (TyCon () (UnQual () (Ident () "FunPtr"))) [TyFun () hs_t (inIO hs_rt)])
           ]
ffiDefinition _ = return []

hsc2hsType :: Hsc.Type -> Type ()
hsc2hsType (Hsc.TyCon n ts)
  = mkTyCon (TyCon () $ UnQual () (Ident () n))
            (map hsc2hsType ts)
hsc2hsType (Hsc.TyVar v) = TyVar () (Ident () v)
hsc2hsType (Hsc.TyTuple ts) = TyTuple () Boxed $ map hsc2hsType ts

mkTyCon :: Type () -> [Type ()] -> Type ()
mkTyCon t xs = foldl (TyApp ()) t xs

inIO :: Type () -> Type ()
inIO t = mkTyCon (TyCon () (UnQual () (Ident () "IO"))) [t]

