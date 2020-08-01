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


import Cogent.Isabelle.ShallowTable (TypeStr(..), st)
import qualified Cogent.Core as CC 
import Cogent.Core (TypedExpr(..))
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Haskell.HscGen
import Cogent.Util (concatMapM)
import qualified Cogent.Haskell.HscSyntax as Hsc

-- import Control.Monad.Identity
-- import Control.Monad.Trans.Reader
import qualified Data.Map as M
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.SrcLoc
import Text.PrettyPrint

import Debug.Trace

import Cogent.Haskell.GenDSL
import Cogent.Haskell.Shallow as SH
import Prelude as P
import Data.Tuple
import Data.Function
import Data.Maybe
import Data.List (find)
import Data.Generics.Schemes (everything)

import Control.Monad.RWS hiding (Product, Sum, mapM)
import Data.Vec as Vec hiding (sym)
import Cogent.Util (Stage(..), delimiter, secondM, toHsTypeName, concatMapM, (<<+=))




-- type FFIFuncs = M.Map FunName (CType, CType)
-- FFIFuncs       -- FFI functions, mapping func name to input/output type
-- -> String         -- Hsc file name
      -- -> [CExtDecl]     -- C decls (UNUSED ATM)

-- type Gen a = ReaderT (FFIFuncs, [FunName]) Identity a

pbtHs :: String         -- Module Name
      -> String         -- Hsc Module Name (for imports)
      -> [PBTInfo]      -- List of PBT info for the Cogent Functions
      -> [CC.Definition TypedExpr VarName b]  -- ^ A list of Cogent definitions
      -> [CC.CoreConst TypedExpr]             -- ^ A list of Cogent constants
      -> String         -- Log header 
      -> String         
pbtHs name hscname pbtinfos decls consts log = render $
  let mod = propModule name hscname pbtinfos decls
    -- flip runReader (m, map ("prop_" ++) $ M.keys m) $ propModule name hscname decls pbtinfos
    in text "{-" $+$ text log $+$ text "-}" $+$ prettyPrim mod

-- -> Gen (Module ()) 
propModule :: String -> String -> [PBTInfo] -> [CC.Definition TypedExpr VarName b] -> Module ()
propModule name hscname pbtinfos decls =
  let (cogDecls, w) = evalRWS (runSG $ do 
                                          shallowTypesFromTable
                                          genDs <- (concatMapM (\x -> genDecls' x decls) pbtinfos)
                                          absDs <- (concatMapM (\x -> absFDecl x decls) pbtinfos)
                                          -- genDecls x decls shallowTypesFromTable
                                          --cs <- concatMapM shallowConst consts
                                          --ds <- shallowDefinitions decls
                                          return $ genDs ++ absDs -- cs ++ ds
                              )
                              (ReaderGen (st decls) [] True [])
                              (StateGen 0 M.empty)
      moduleHead = ModuleHead () (ModuleName () name) Nothing Nothing
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
      hs_decls = (P.concatMap propDecls pbtinfos) ++ cogDecls-- ++ (P.concatMap (\x -> genDecls x decls) pbtinfos)
  in 
  Module () (Just moduleHead) exts imps hs_decls

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
genDecls :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> [Decl ()]
genDecls PBTInfo{..} defs = 
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            icT = fromJust $ P.lookup "IC" ityps
            --FunWelF{..} = fwelf
-- FuncInfo{name=n, ispure=_, nondet=_, ictype=icT} = 
        --let 
            fnName = "gen_" ++fname
            toName = "Gen" -- ++icT
            to     = TyCon   () (mkQName toName)
            sig    = TypeSig () [mkName fnName] to
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ 
                        mkGenBody fname icT) Nothing]
            -- cls    = ClassDecl () () [] ()
            in [sig, dec]

mkGenBody :: String -> Type () -> Exp ()
mkGenBody name icT = function "arbitrary"

genDecls' :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
genDecls' PBTInfo{..} defs = do
        -- icT' <- extractTyp defs fname 
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            icT = fromJust $ P.lookup "IC" ityps
            --FunWelF{..} = fwelf
-- FuncInfo{name=n, ispure=_, nondet=_, ictype=icT} = 
        --let 
            fnName = "gen_" ++fname
            toName = "Gen " -- ++icT
            to     = TyCon   () (mkQName toName)
            sig    = TypeSig () [mkName fnName] to
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ 
                        mkGenBody fname icT) Nothing]
            -- cls    = ClassDecl () () [] ()
          in return $ [sig, dec] --, icT']



absFDecl :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
absFDecl PBTInfo{..} defs =  do
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            -- icT = fromJust $ P.lookup "IC" ityps
            iaT = fromJust $ P.lookup "IA" ityps
            fnName = "abs_" ++fname
        (icT, _, absE) <- getFnTyp fname iaT defs
        let ti     = icT
            to     = iaT
            sig    = TypeSig () [mkName fnName] (TyFun () ti to)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "ic"] (UnGuardedRhs () absE) Nothing]
        return $ [sig, dec] --, icT']



-- ^^ Match on absT, e.g. TyTuple, to determine what abstraction we are performing
--    concT will give us the fields (if any)
--    core functionality

    -- ( M.Map String (Type ()) )
 
getFnTyp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> SG (Type (), Type (), Exp ()) 
getFnTyp fname iaTyp defs = do 
    let d = fromJust $ find defFilt defs
    (icT, iaT, absE) <- getFnTyp' d iaTyp
    pure $ (icT, iaT, absE)
        where 
            defFilt :: (CC.Definition e a b) -> Bool
            defFilt x = (CC.getDefinitionId x) == fname

getFnTyp' :: (CC.Definition TypedExpr VarName b) -> Type () -> SG ( (Type (), Type (), Exp ()) )
getFnTyp' (CC.FunDef _ fn ps _ ti to _) iaT = local (typarUpd typar) $ do
    ti' <- shallowType ti
    absE <- mkAbsFBody ti iaT
    pure $ ({-TyCon () (mkQName "Unknown") -} ti', iaT, absE)
    where
        typar = map fst $ Vec.cvtToList ps
getFnTyp' (CC.AbsDecl _ fn ps _ ti to) iaT = local (typarUpd typar) $ do
    ti' <- shallowType ti
    absE <- mkAbsFBody ti iaT
    pure $ ( {-TyCon () (mkQName "Unknown")-} ti', iaT, absE)
    where
        typar = map fst $ Vec.cvtToList ps
getFnTyp' (CC.TypeDef tn _ _) iaT = pure $ (TyCon () (mkQName "Unknown"), iaT, function $ "undefined")


-- | mkAbsFBody 
-- |    - direct mapping
-- |    - Abstract Input Type is the input type of the Haskell abstract spec
-- |    - Concrete Input Type is the input type of the concrete function (Cogent HS embedding)
--
mkAbsFBody :: CC.Type t a -> Type () -> SG (Exp ())
mkAbsFBody concT (TyParen _ t   ) = mkAbsFBody concT t 
-- ^^ Type surrounded by parens, recurse on inside type

mkAbsFBody concT (TyTuple _ _ tfs) = unwrapRTup concT
-- ^^ IA is Tuple, fs is [(FieldName, (Type t b, Bool))]
--

mkAbsFBody concT (TyCon _ cn    ) = pure $ function $ "undefined"
mkAbsFBody concT (TyList _ t    ) = pure $ function $ "undefined" 


unwrapRTup :: CC.Type t a -> SG (Exp ())
unwrapRTup concT = case concT of 
    (CC.TRecord _ fs _) -> do
             --vs <- mapM (\x -> fst x) fs
             --vs <- concatMapM fst fs
             (tn,_) <- nominalType concT
             let rec' = mkConE $ mkName "ic"
                 bs = P.map (\v -> mkName $ snm $ fst v) fs
                 p' = PRec () (UnQual () $ mkName tn) --[PFieldWildcard ()] -- bs
                        (P.zipWith (\(f,_) b -> PFieldPat () (UnQual () . mkName $ snm f) (pvar b)) fs bs)
             pure $ mkLetE [(p',rec')] $ tuple $ map var bs
    (CC.TCon tn ts _)   -> pure $ function $ "undefined"
    (CC.TSum ts)        -> pure $ function $ "undefined"
    (CC.TProduct t1 t2) -> pure $ var $ mkName "ic"

    -- ^^ Cogent Tuple, unwrap with letE, 
    _                   -> pure $ function $ "undefined"










{-
genDecls :: PBTInfo -> [Decl ()]
genDecls PBTInfo{..} = 
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            icT = fromJust $ P.lookup "IC" ityps
            --FunWelF{..} = fwelf
-- FuncInfo{name=n, ispure=_, nondet=_, ictype=icT} = 
        --let 
            fnName = "gen_" ++fname
            toName = "Gen" ++icT
            to     = TyCon   () (mkQName toName)
            sig    = TypeSig () [mkName fnName] to
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ 
                        mkGenBody fname icT) Nothing]
            -- cls    = ClassDecl () () [] ()
            in [sig, dec]

mkGenBody :: String -> String -> Exp ()
mkGenBody name icT = function "arbitrary"
-}












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
