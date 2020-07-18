--
--

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}

-- | Haskell PBT generator
--
-- Generates Hs functions which are used in Property-Based Testing

module Cogent.Haskell.PBTGen (
  pbtHs
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

import Cogent.Haskell.GenDSL
import Cogent.Haskell.Shallow
import Prelude as P
import Data.Tuple
import Data.Function
import Data.Generics.Schemes (everything)

type FFIFuncs = M.Map FunName (CType, CType)

type Gen a = ReaderT (FFIFuncs, [FunName]) Identity a

pbtHs :: FFIFuncs -> String -> String -> [CExtDecl] -> [PBTInfo] -> String -> String
pbtHs m name hscname decls pbtinfos log = render $
  let mod = flip runReader (m, map ("prop_" ++) $ M.keys m) $ propModule name hscname decls pbtinfos
   in text "{-" $+$ text log $+$ text "-}" $+$ prettyPrim mod

propModule :: String -> String -> [CExtDecl] -> [PBTInfo] -> Gen (Module ())
propModule name hscname decls pbtinfos =
  let moduleHead = ModuleHead () (ModuleName () name) Nothing Nothing
      exts = []
      imps = [ ImportDecl () (ModuleName () "Prelude") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Test.QuickCheck" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Test.QuickCheck.Monadic" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Data.Tree" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Data.Word" ) False False False Nothing Nothing Nothing
             -- custom corres
             , ImportDecl () (ModuleName () "Corres" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () hscname) False False False Nothing (Just (ModuleName () "FFI")) Nothing
             , ImportDecl () (ModuleName () (hscname ++ "_Abs")) False False False Nothing (Just (ModuleName () "FFI")) Nothing
             ]
      hs_decls = (P.concatMap propDecls pbtinfos) -- decls ++ (P.concatMap genDecls decls)
  in 
  return $ Module () (Just moduleHead) exts imps hs_decls

-- -----------------------------------------------------------------------
-- Cogent PBT: Refinement statement property generator
-- -----------------------------------------------------------------------
propDecls :: PBTInfo -> [Decl ()]
propDecls PBTInfo{..} = 
        --let FunInfo{..} = finfo
        --    FunTypes{..} = ftyps
        --    FunRels{..} = frels
        let fnName = "prop_" ++ fname
            toName = "Property"
            to     = TyCon   () (mkQName toName)
            sig    = TypeSig () [mkName fnName] to
            dec    = FunBind () [Match () (mkName fnName) [] 
                                 (UnGuardedRhs () $ mkPropBody fname finfo ) Nothing]
            in [sig, dec]

mkPropBody :: String -> FunInfo -> Exp ()
mkPropBody n FunInfo{ispure=True, nondet=nd} =  
    let f  = function "forAll"
        fs = [ function $ "gen_"++n
             , lamE [pvar $ mkName "ic"] (letE binds body) ]
            where ia = app (function $ "abs_"++n) (var $ mkName "ic")
                  oc = app (function n)           (var $ mkName "ic")
                  oa = app (function $ "hs_"++n)  ia
                  binds = [ FunBind () [Match () (mkName "oc") [] (UnGuardedRhs () $ oc  ) Nothing]
                          , FunBind () [Match () (mkName "oa") [] (UnGuardedRhs () $ oa  ) Nothing] ]
                  body  = appFun (function $ "corres"++(if nd==False then "'" else "")) 
                                 [ function $ "rel_"++n
                                 , var $ mkName "oa"
                                 , var $ mkName "oc" ]
        in appFun f fs
mkPropBody n FunInfo{ispure=False, nondet=nd} =
    let f  = function "forAllM"
        fs = [ function $ "gen_"++n
             , lamE [pvar $ mkName "ic"] (doE binds)  
             ]
           where ia = app (function $ "abs_"++n) (var $ mkName "ic")
                 oc = app (function n)           (var $ mkName "ic")
                 oa = app (function $ "hs_"++n)  ia
                 binds = [ genStmt (pvar $ mkName "oc") oc 
                         , genStmt (pvar $ mkName "oa") (app (function "return") oa) 
                         , qualStmt body ]
                 body  = appFun (function $ "corresM"++(if nd==False then "'" else "")) 
                                [ function $ "rel_"++n
                                , var $ mkName "oa"
                                , var $ mkName "oc" ]
        in app (function "monadicIO") (appFun f fs)



-- -----------------------------------------------------------------------
-- Cogent PBT: Generator for Test data generators
-- -----------------------------------------------------------------------
genDecls :: FuncInfo -> [Decl ()]
genDecls FuncInfo{name=n, ispure=_, nondet=_, ictype=icT} = 
        let fnName = "gen_" ++n
            toName = "Gen " ++ (case icT of
                                    Pointer -> "Word32"
                                    CList -> "[Word32]"
                                    Tree -> "Tree Word32"
                                    _ -> show icT )
            to     = TyCon   () (mkQName toName)
            sig    = TypeSig () [mkName fnName] to
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ 
                        mkGenBody n icT) Nothing]
            -- cls    = ClassDecl () () [] ()
            in [sig, dec]

mkGenBody :: String -> ICType -> Exp ()
mkGenBody name Pointer = function "arbitrary"
mkGenBody name CList = function "arbitrary"
mkGenBody name Tree = function "arbitrary"
mkGenBody name _ = function "arbitrary"

{-
    let f  = function "gen"
        fs = [ function $ "gen_"++name
             , lamE [pvar $ mkName "ic"] (doE binds)  
             ]
           where ia = app (function $ "abs_"++name) (var $ mkName "ic")
                 oc = app (function name)           (var $ mkName "ic")
                 oa = app (function $ "hs_"++name)  ia
                 binds = [ genStmt (pvar $ mkName "oc") oc 
                         , genStmt (pvar $ mkName "oa") (app (function "return") oa) 
                         , qualStmt body
                         ]
                 body  = appFun (function $ "corres_"++name) [ function $ "rel_"++name
                                                             , var $ mkName "oa"
                                                             , var $ mkName "oc" 
                                                             ]
        in app (function "monadicIO") (appFun f fs)
        -}


















      {-
      in hsModule & header .
           prettyPrintStyleMode 
            (style {lineLength = 220, ribbonsPerLine = 0.1}) 
            (defaultMode {caseIndent = 2})
  return $ Module () (Just mhead) pragmas imps hs_decls
            -}





{-
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
           ]
ffiDefinition _ = return []
-}

-- -----------------------------------------------------------------------
-- Cogent PBT: Haskell embedding extra generators 
-- -----------------------------------------------------------------------
{-
funPBTGen :: [FuncInfo] -> String -> String -> String
funPBTGen fs modName log = 
  let header = (("{-\n" ++ log ++ "\n-}\n") ++)
      moduleHead = ModuleHead () (ModuleName () modName) Nothing Nothing
      exts = []
      imps = [ ImportDecl () (ModuleName () "Prelude") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Test.QuickCheck" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Test.QuickCheck.Monadic" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Data.Tree" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Data.Word" ) False False False Nothing Nothing Nothing
             -- custom corres
             , ImportDecl () (ModuleName () "Corres" ) False False False Nothing Nothing Nothing
             ]
      decls = (P.concatMap propDecls fs) 
              ++ (P.concatMap genDecls fs)
      hsModule = Module () (Just moduleHead) exts imps decls
      in hsModule & header .
           prettyPrintStyleMode 
            (style {lineLength = 220, ribbonsPerLine = 0.1}) 
            (defaultMode {caseIndent = 2})
            -}

