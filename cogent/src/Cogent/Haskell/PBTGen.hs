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
import Cogent.Compiler (__impossible)
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

import Control.Arrow (second, (***))
import Control.Applicative
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Control.Monad.RWS hiding (Product, Sum, mapM)
import Data.Vec as Vec hiding (sym)
import Cogent.Util (Stage(..), delimiter, secondM, toHsTypeName, concatMapM, (<<+=))
import Cogent.Isabelle.Shallow (isRecTuple)

-- type FFIFuncs = M.Map FunName (CType, CType)
-- FFIFuncs       -- FFI functions, mapping func name to input/output type
-- -> String         -- Hsc file name
      -- -> [CExtDecl]     -- C decls (UNUSED ATM)

-- type Gen a = ReaderT (FFIFuncs, [FunName]) Identity a

pbtHs :: String         -- Module Name
      -> String         -- Hsc Module Name (for imports)
      -> [PBTInfo]      -- List of PBT info for the Cogent Functions
      -> [CC.Definition TypedExpr VarName b]  -- A list of Cogent definitions
      -> [CC.CoreConst TypedExpr]             -- A list of Cogent constants
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
                                          rrelDs <- (concatMapM (\x -> rrelDecl x decls) pbtinfos)
                                          -- genDecls x decls shallowTypesFromTable
                                          --cs <- concatMapM shallowConst consts
                                          --ds <- shallowDefinitions decls
                                          return $ absDs ++ rrelDs ++ genDs  -- cs ++ ds
                              )
                              (ReaderGen (st decls) [] True [])
                              (StateGen 0 M.empty)
      moduleHead = ModuleHead () (ModuleName () name) Nothing Nothing
      exts = P.map (\s -> LanguagePragma () [Ident () s])
                   [ "DisambiguateRecordFields"
                   , "DuplicateRecordFields"
                   , "NamedFieldPuns"
                   , "NoImplicitPrelude"
                   , "PartialTypeSignatures"
                   , "PartialTypeSignatures"
                   , "TemplateHaskell"
                   ]
      importVar s = IVar () $ Ident  () s
      importSym s = IVar () $ Symbol () s
      importAbs s = IAbs () (NoNamespace ()) $ Ident () s
      import_bits = P.map importSym [".&.", ".|."] ++
                    P.map importVar ["complement", "xor", "shiftL", "shiftR"]
      import_word = P.map importAbs ["Word8", "Word16", "Word32", "Word64"]
      import_prelude = P.map importVar ["not", "div", "mod", "fromIntegral", "undefined", "return"] ++
                       P.map importSym [".", "+", "-", "*", "&&", "||", ">", ">=", "<", "<=", "==", "/="] ++
                       P.map importAbs ["Char", "String", "Int", "Show", "Maybe"] ++
                       [IThingAll () $ Ident () "Bool"]
      imps = [ ImportDecl () (ModuleName () "Test.QuickCheck" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Test.QuickCheck.Monadic" ) False False False Nothing Nothing Nothing 
              -- ImportDecl () (ModuleName () "Prelude") True False False Nothing (Just (ModuleName () "P")) Nothing
             
             --, ImportDecl () (ModuleName () "Data.Tree" ) False False False Nothing Nothing Nothing
             --, ImportDecl () (ModuleName () "Data.Word" ) False False False Nothing Nothing Nothing
             -- custom corres
             , ImportDecl () (ModuleName () "Corres" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () hscname) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Lens.Micro") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Lens.Micro.TH") False False False Nothing Nothing Nothing
             -- , ImportDecl () (ModuleName () (hscname ++ "_Abs")) False False False Nothing (Just (ModuleName () "FFI")) Nothing
             , ImportDecl () (ModuleName () "Prelude"  ) False False False Nothing Nothing (Just $ ImportSpecList () False import_prelude)
             , ImportDecl () (ModuleName () "Data.Bits") False False False Nothing Nothing (Just $ ImportSpecList () False import_bits)
             , ImportDecl () (ModuleName () "Data.Tuple.Select") True False False Nothing (Just $ ModuleName () "Tup") Nothing
             , ImportDecl () (ModuleName () "Data.Tuple.Update") True False False Nothing (Just $ ModuleName () "Tup") Nothing
             , ImportDecl () (ModuleName () "Data.Word") False False False Nothing Nothing (Just $ ImportSpecList () False import_word)
             ]
            -- TODO: need to have a list of record names
      hs_decls = (map mkLens ["R4"]) ++ (P.concatMap propDecls pbtinfos) ++ cogDecls
                                -- ++ (P.concatMap (\x -> genDecls x decls) pbtinfos)
            where mkLens t = SpliceDecl () $ app (function "makeLenses") 
                                (TypQuote () (UnQual () (mkName t)))
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

mkPropBody :: String -> FunDefs -> Exp ()
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
mkGenBody name icT = function "undefined" -- "arbitrary"

-- Dummy func for Gen functions (test data generators)
genDecls' :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
genDecls' PBTInfo{..} defs = do
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            icT' = fromJust $ P.lookup "IC" ityps
            icT = fromJust $ P.lookup "IA" ityps
        -- (icT, _, absE) <- genAbsFTypsAndExp fname iaT defs
        let fnName = "gen_" ++fname
            --toName = "Gen " ++ show icT' -- ++icT
            --to     = TyCon   () (mkQName toName)
            --sig    = TypeSig () [mkName fnName] to
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ 
                        mkGenBody fname icT) Nothing]
            hs_dec    = FunBind () [Match () (mkName $ "hs_"++fname) [] (UnGuardedRhs () $ 
                        function "undefined") Nothing]
            -- cls    = ClassDecl () () [] ()
          in return $ [dec, hs_dec] --[sig, dec] --, icT']

-- Abstraction Function Generator
absFDecl :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
absFDecl PBTInfo{..} defs = do
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            -- icT = fromJust $ P.lookup "IC" ityps
            iaT = fromJust $ P.lookup "IA" ityps
            fnName = "abs_" ++fname
        (icT, _, absE) <- genAbsFTypsAndExp fname iaT defs
        let ti     = icT
            to     = iaT
            sig    = TypeSig () [mkName fnName] (TyFun () ti to)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "ic"] (UnGuardedRhs () absE) Nothing]
        return $ [sig, dec]

-- Refinement Relation Generator
rrelDecl :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
rrelDecl PBTInfo{..} defs = do
        let FunRRel{rrel=_, otyps=otyps} = frrel
            oaT = fromJust $ P.lookup "OA" otyps
            fnName = "rel_" ++fname
        (ocT, _, rrelE) <- getFnOutTyp fname oaT defs
        let to     = mkTyConT $ mkName "Bool"
            ti     = TyFun () oaT $ TyFun () ocT to
            sig    = TypeSig () [mkName fnName] (ti)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "oa", pvar $ mkName "oc"] (UnGuardedRhs () rrelE) Nothing]
        return $ [sig, dec]
 
-- Get Function Type and Expression
-- ------------------------------------------
-- @fname@ is the name of the function
-- @iaTyp@ is the abstract input type
-- @defs@ is the list of Cogent definitions
--
genAbsFTypsAndExp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> SG (Type (), Type (), Exp ()) 
genAbsFTypsAndExp fname iaTyp defs = do 
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (icT, iaT, absE) <- genAbsFTypsAndExp' def iaTyp
    pure $ (icT, iaT, absE)

-- Helper: get function type and expression
genAbsFTypsAndExp' :: (CC.Definition TypedExpr VarName b) -> Type () -> SG ( (Type (), Type (), Exp ()) )
genAbsFTypsAndExp' def iaT | (CC.FunDef _ fn ps _ ti to _) <- def 
    = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
        ti' <- shallowType ti
        absE <- mkAbsFBody ti ti' iaT
        pure $ ({-TyCon () (mkQName "Unknown") -} ti', iaT, absE)

genAbsFTypsAndExp' def iaT | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    absE <- mkAbsFBody ti ti' iaT
    pure $ ( {-TyCon () (mkQName "Unknown")-} ti', iaT, absE)

genAbsFTypsAndExp' def iaT | (CC.TypeDef tn _ _) <- def 
    = pure $ (TyCon () (mkQName "Unknown"), iaT, function $ "undefined")

getFnOutTyp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> SG (Type (), Type (), Exp ()) 
getFnOutTyp fname oaTyp defs = do 
    let d = fromJust $ find defFilt defs
    (ocT, oaT, rrelE) <- getFnOutTyp' d oaTyp
    pure $ (ocT, oaT, rrelE)
        where 
            defFilt :: (CC.Definition e a b) -> Bool
            defFilt x = (CC.getDefinitionId x) == fname

getFnOutTyp' :: (CC.Definition TypedExpr VarName b) -> Type () -> SG ( (Type (), Type (), Exp ()) )
getFnOutTyp' (CC.FunDef _ fn ps _ ti to _) oaT = local (typarUpd typar) $ do
    to' <- shallowType to
    rrelE <- mkRrelBody to oaT
    pure $ ({-TyCon () (mkQName "Unknown") -} to', oaT, rrelE)
    where
        typar = map fst $ Vec.cvtToList ps
getFnOutTyp' (CC.AbsDecl _ fn ps _ ti to) oaT = local (typarUpd typar) $ do
    to' <- shallowType to
    rrelE <- mkRrelBody to oaT
    pure $ ( {-TyCon () (mkQName "Unknown")-} to', oaT, rrelE)
    where
        typar = map fst $ Vec.cvtToList ps
getFnOutTyp' (CC.TypeDef tn _ _) oaT = pure $ (TyCon () (mkQName "Unknown"), oaT, function $ "undefined")

-- TODO: clean up
-- ---------------------------------
-- | mkAbsFBody 
-- |    - direct mapping
-- |    - Abstract Input Type is the input type of the Haskell abstract spec
-- |    - Concrete Input Type is the input type of the concrete function (Cogent HS embedding)
-- ^^ Type surrounded by parens, recurse on inside type
-- ^^ IA is Tuple, fs is [(FieldName, (Type t b, Bool))]
{- match on haskell types -> default access using Lens
    every type has a lens
-}
-- TODO: probably want to gleam some info about the iaTyp
-- TODO: clear up function name
-- TODO: Prim and Strings, Sum 
-- TODO: probably want to gleam some info about the icTyp
-- TODO: clear up function name
-- TODO: Prim and Strings, Sum 
-- @cogIcTyp@ is the original cogent type
-- @icTyp@ is the hs embedding of cogent type 
-- @iaTyp@ is the user supplied type we are trying to abstract to
-- Handle when IC is tuple --> Lens view for each field
-- return map where field name maps to view expression
--


-- ----------------------------------------------------------------------------------------------------
mkAbsFBody :: CC.Type t a -> Type () -> Type () -> SG (Exp ())
mkAbsFBody cogIcTyp icTyp iaTyp 
    = let tyL = analyseTypes cogIcTyp icTyp 0 "None"
          lens = mkLensView tyL Nothing
          binds = P.zip (map (\x -> pvar . mkName . fst $ x) lens) (map snd lens)
          body = case iaTyp of
                   (TyTuple _ _ ftys) -> tuple $ map (\(toTyp, varToPut) 
                                                          -> if (isInt toTyp) then app (function "fromIntegral") (var . mkName . fst $ varToPut)
                                                             else (var . mkName . fst $ varToPut)
                                                     ) $ P.zip ftys lens  
{- TODO: handle more abstractions
        (TyParen _ insideTy) -> mkAbsFBody'' cogIcTyp icTyp insideTy
        (TyTuple _ _ tfs) -> mkTupFrom'' cogIcTyp icTyp iaTyp
        (TyUnboxedSum _ tfs) -> mkTupFrom'' cogIcTyp icTyp iaTyp
        (TyList _ ty) -> __impossible "TODO: Abstacting to List"
        (TyFun _ iTy oTy) -> __impossible "TODO: Abstacting to function"
        (TyApp _ lTy rTy) -> __impossible "TODO: Abstacting to Constructor w/ application"
        (TyVar _ name) -> __impossible "TODO: Abstacting to a type variable"
        (TyCon _ name) -> __impossible "TODO: Abstacting to a named type or type constructor"
        (TyInfix _ lTy name rTy) -> __impossible "TODO: Abstacting to a infix type constructor"
        otherwise -> __impossible "Bad abstraction"

 -}
                   _ -> __impossible "TODO"
       in pure $ mkLetE binds body

isInt :: Type () -> Bool
isInt (TyCon _ (UnQual _ (Ident _ n))) = any (\x -> n == x) ["Int"]

-- from Layout return list of pairs: variable name for bind and the view expression
-- key = var name ++ depth tag
-- val = 
-- mkLensView {} (infixApp (mkName "ic") viewInfixExp
-- ----------------------------------------------------------------------------------------------------
mkLensView :: TyLayout -> Maybe (Exp ()) -> [(String, (Exp ()))]
mkLensView tyL prev 
    = let hsTy = tyL ^. hsTyp
          ty = tyL ^. typ
          fld = tyL ^. fieldMap
          -- field map is a tree with int leaves -> only build vars for leaves
       in concat $ map (\(k, v) 
              -> case ty of 
                   HsPrim 
                     -> case v of                          -- ic ^. bag . _1
                          (Left depth) -> case prev of 
                                            Just x -> [ (k++(replicate depth (P.head "'")), x)]
                                            Nothing -> [(k++(replicate depth (P.head "'")), (var (mkName "ic")))]
                          (Right next) -> __impossible "boom"
                   HsTuple -> case v of 
                                   (Left depth) -> __impossible "boom"
                                   (Right next) -> case prev of 
                                                     Just x -> mkLensView next $ Just $ infixApp x viewInfixExp' (mkAccess' k)
                                                     Nothing -> mkLensView next $ Just $ infixApp (var (mkName "ic")) viewInfixExp (mkAccess' k)
                   -- HsRecord | HsList
                   _ -> case v of 
                      (Left depth) -> __impossible "boom"
                      (Right next) -> case prev of 
                                        Just x -> mkLensView next $ Just $ infixApp x viewInfixExp' (mkAccess' k)
                                        Nothing -> mkLensView next $ Just $ infixApp (var (mkName "ic")) viewInfixExp (mkAccess' k)
          ) (M.toList fld) 


-- ----------------------------------------------------------------------------------------------------
analyseTypes :: CC.Type t a -> Type () -> Int -> String -> TyLayout
analyseTypes cogIcTyp icTyp depth fieldName
    = case icTyp of
        (TyParen _ t   ) -> analyseTypes cogIcTyp t depth fieldName
        (TyTuple _ _ tfs) 
            -> TyLayout icTyp HsTuple (getTupFields cogIcTyp tfs)
            where getTupFields cogTy tfs 
                    = let fs = getFields cogTy
                        in M.fromList [ let k = "_"++show (i+1)
                                          in (k , Right (analyseTypes (fst (snd (fs!!i))) (tfs!!i) (depth+1) k))
                                      | i <- [0..(P.length tfs)-1]
                                      ]
        (TyCon _ cn) 
            -- check for prims
            -> TyLayout icTyp HsPrim (getConFields cn)
            where getConFields cn 
                    = let p = case cn of (UnQual _ n) -> find (\x -> mkName x == n) prims
                                         _ -> Nothing
                    in M.fromList $ case p of 
                                      Just x -> [(fieldName, Left depth)] 
                                      -- no prims found
                                      Nothing -> []
        (TyApp _ l r) 
            {-
             - cogIcTyp will tell you the field names 
             - icTyp will tell you the concrete version of the type 
             - since the shallow embedding creates a type constructor and 
             - icTyp is the type created using that constructor for this specific function
             -}
            -> let (name, fieldTypes) = let (conHead:conParams) = unfoldAppCon icTyp 
                                         in ( case conHead of 
                                                (TyCon _ (UnQual _ (Ident _ n))) -> n
                                                _ -> __impossible $ "Bad Constructor name"++show l++"--"++show r
                                            , conParams
                                            )
                   fields = getFields cogIcTyp
                in TyLayout l HsRecord $ M.fromList [ ( (fst (fields!!i))
                                                      , let f = fields!!i
                                                      -- should hit a prim eventually
                                                         in Right (analyseTypes (fst (snd f)) (fieldTypes!!i) (depth+1) (fst f))
                                                      )
                                                    | i <- [0..(P.length fields)-1]
                                                    ]
        (TyList _ ty) 
            -> let elemCogTy = case cogIcTyp of 
                                 (CC.TArray t _ _ _) -> t
                                 _ -> __impossible "Compiler should not produce such an embedding"
                in TyLayout icTyp HsList $ M.fromList [ ( "1" , Right (analyseTypes elemCogTy ty (depth+1) "1")) ]
        (TyFun _ iTy oTy) -> __impossible "TODO: Abstacting from function"
        (TyVar _ name) -> __impossible "TODO: Abstacting from a type variable"
        (TyInfix _ lTy name rTy) -> __impossible "TODO: Abstacting from a infix type constructor"
        (TyUnboxedSum _ tfs) -> __impossible "Compiler should never produce TyUnboxedSum embedding"
        otherwise -> __impossible "Bad abstraction"

-- ----------------------------------------------------------------------------------------------------
viewInfixExp :: QOp ()
viewInfixExp = op $ mkName "^."

viewInfixExp' :: QOp ()
viewInfixExp' = op $ mkName "."

mkAccess :: Int -> Exp ()
mkAccess i = var $ mkName $ "_"++show i

mkAccess' :: String -> Exp ()
mkAccess' i = var $ mkName i
    
mkAccess'' :: String -> Exp ()
mkAccess'' i = var $ mkName $ "_"++show i

prims = ["Word8","Word16","Word32","Word64","Bool", "String"]

getFields :: CC.Type t a -> [(String, (CC.Type t a, Bool))]
getFields (CC.TRecord _ fs _) = fs
getFields (CC.TSum alts) = alts
getFields (CC.TProduct l r) = [("1", (l,False)), ("2", (r,False))]
getFields _ = __impossible "TODO"

-- unfolding Constructor Application
unfoldAppCon :: Type () -> [Type ()]
unfoldAppCon t = case t of 
                   (TyApp _ l r) -> unfoldAppCon l ++ unfoldAppCon r
                   (TyCon _ n) -> [t]
-- ----------------------------------------------------------------------------------------------------


-- | mkRrelBody 
-- | dummy func ATM
-- --------------------------------------------------
mkRrelBody :: CC.Type t a -> Type () -> SG (Exp ())
mkRrelBody concT absT = pure $ function $ "undefined"
