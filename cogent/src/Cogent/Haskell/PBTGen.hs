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
import Data.List (find, partition, group, sort)
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
      (ls, cogD) = partition (\x -> case x of 
                                      (SpliceDecl _ _) -> True
                                      _ -> False) cogDecls
      hs_decls = (rmdups ls) ++ (P.concatMap propDecls pbtinfos) ++ cogD
                                -- ++ (P.concatMap (\x -> genDecls x decls) pbtinfos)
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
absFDecl :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG ([Decl ()])
absFDecl PBTInfo{..} defs = do
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            -- icT = fromJust $ P.lookup "IC" ityps
            iaT = fromJust $ P.lookup "IA" ityps
            fnName = "abs_" ++fname
        (icT, _, absE, conNames) <- genAbsFTypsAndExp fname iaT defs
        let ti     = icT
            to     = iaT
            sig    = TypeSig () [mkName fnName] (TyFun () ti to)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "ic"] (UnGuardedRhs () absE) Nothing]
            mkLens t = SpliceDecl () $ app (function "makeLenses") 
                                (TypQuote () (UnQual () (mkName t)))
        return $ (map mkLens conNames)++[sig, dec]

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
genAbsFTypsAndExp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> SG (Type (), Type (), Exp (), [String]) 
genAbsFTypsAndExp fname iaTyp defs = do 
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (icT, iaT, absE, conNames) <- genAbsFTypsAndExp' def iaTyp
    pure $ (icT, iaT, absE, conNames)

-- Helper: get function type and expression
genAbsFTypsAndExp' :: (CC.Definition TypedExpr VarName b) -> Type () -> SG ( (Type (), Type (), Exp (), [String]) )
genAbsFTypsAndExp' def iaT | (CC.FunDef _ fn ps _ ti to _) <- def 
    = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
        ti' <- shallowType ti
        (absE, conNames) <- mkAbsFBody ti ti' iaT
        pure $ ({-TyCon () (mkQName "Unknown") -} ti', iaT, absE, conNames)

genAbsFTypsAndExp' def iaT | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (absE, conNames) <- mkAbsFBody ti ti' iaT
    pure $ ( {-TyCon () (mkQName "Unknown")-} ti', iaT, absE, conNames)

genAbsFTypsAndExp' def iaT | (CC.TypeDef tn _ _) <- def 
    = pure $ (TyCon () (mkQName "Unknown"), iaT, function $ "undefined", [])

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

-- ----------------------------------------------------------------------------------------------------
mkAbsFBody :: CC.Type t a -> Type () -> Type () -> SG (Exp (), [String])
mkAbsFBody cogIcTyp icTyp iaTyp 
    = let tyL = analyseTypes cogIcTyp icTyp 0 "None"
          lens = mkLensView tyL Nothing
          binds = P.zip (map (\x -> pvar . mkName . fst $ x) lens) (map snd lens)
          body = packAbsCon iaTyp (map fst lens) 0
       in pure $ (mkLetE binds body, getConNames tyL []) 

-- generate exp for packing the constructor that is returned by absf
-- 1st = type
-- 2nd = list of vars to put in the constructor
-- 3rd = position in structure
-- vars are pack left to right from the list
-- removing vars from list as they are added in the recursion
-- TODO: unify the vars with the outgoing matching type
-- TODO: pair varsToPut with types for that var
packAbsCon :: Type () -> [String] -> Int -> Exp ()
packAbsCon (TyParen _ insideTy) varsToPut pos = packAbsCon insideTy varsToPut pos
packAbsCon (TyTuple _ _ ftys) varsToPut pos 
    -- give each subtype is appropriate var
    = tuple $ let vs = if | P.length ftys == P.length varsToPut -> varsToPut
                          | otherwise -> take (P.length ftys) varsToPut
                in [ packAbsCon (ftys!!i) vs i | i <- [0..(P.length ftys)-1] ]
packAbsCon (TyCon _ name) varsToPut pos 
    = case (checkIsPrim name) of 
        -- transform if needs coercion
        Just x -> if | isInt' name 
                        -> app (function "fromIntegral") $ mkVar $ varsToPut!!pos
                     | otherwise 
                        -> mkVar $ varsToPut!!pos
        Nothing -> mkVar $ varsToPut!!pos
packAbsCon iaTyp varsToPut pos 
    | (TyApp _ lTy rTy) <- iaTyp
    = let (name, fieldTypes) = let (conHead:conParams) = unfoldAppCon iaTyp 
                                 in ( case conHead of 
                                            (TyCon _ (UnQual _ (Ident _ n))) -> n
                                            _ -> "Unknown"
                                    , conParams
                                    )
        -- TODO:
        -- Constructors with application, some need to be handled differently -> Set | Map | List -> try to build `from` list and tups
        -- e.g Map String String -> if "Map" the app (function "M.fromList")
        -- if -- | name == "Map" -> undefined 
              -- | name == "Set" -> app (function "S.fromList") $ mkVar $ varsToPut!!pos
             --  | otherwise 
                -- -> 
        in appFun (mkVar name) $ let vs = if | P.length fieldTypes == P.length varsToPut -> varsToPut
                                                      | otherwise -> take (P.length fieldTypes) varsToPut
                                               in [ packAbsCon (fieldTypes!!i) vs i | i <- [0..(P.length fieldTypes)-1] ]
                where 
packAbsCon (TyList _ ty) varsToPut pos = mkVar $ varsToPut!!pos
packAbsCon iaTyp varsToPut prev | _ <- iaTyp = __impossible $ "Bad Abstraction"++" --> "++"Hs: "++show iaTyp
-- ----------------------------------------------------------------------------------------------------

-- ----------------------------------------------------------------------------------------------------

-- | mkLensView
-- ---------------
-- TODO: clean up comment
-- from Layout return list of pairs: variable name for bind and the view expression
-- key = var name ++ depth tag
-- val = 
-- ----------------------------------------------------------------------------------------------------
mkLensView :: HsEmbedLayout -> Maybe (Exp ()) -> [(String, (Exp ()))]
mkLensView tyL prev 
    = let hsTy = tyL ^. hsTyp
          ty = tyL ^. grTag
          fld = tyL ^. fieldMap
          -- field map is a tree with int leaves -> only build vars for leaves
       in concat $ map ( \(k, v) -> case ty of 
           HsPrim -> case v of
              (Left depth) -> [ ( k ++ replicate depth (P.head "'")
                                , case prev of Just x -> x
                                               Nothing -> mkVar "ic" 
                                )
                              ]
              (Right next) -> __impossible $ show k ++ " " ++ show v
           _ -> case v of
              (Left depth) -> __impossible $ show k ++ " " ++ show v
              (Right next) -> mkLensView next $ Just $ mkViewInfixE "ic" ty prev k
       ) (M.toList fld) 

-- | analyseTypes
-- ---------------
-- | Builds the structure used for generating the body of absf
-- ----------------------------------------------------------------------------------------------------
analyseTypes :: CC.Type t a -> Type () -> Int -> String -> HsEmbedLayout
analyseTypes cogIcTyp (TyParen _ t   ) depth fieldName = analyseTypes cogIcTyp t depth fieldName
analyseTypes cogIcTyp icTyp depth fieldName 
    | (TyTuple _ _ tfs) <- icTyp = HsEmbedLayout icTyp HsTuple $ getTupFields cogIcTyp tfs
    where getTupFields cogTy tfs 
            = let fs = getFields cogTy
                in M.fromList [ let k = "_"++show (i+1)
                                  in (k , Right (analyseTypes (fst (snd (fs!!i))) (tfs!!i) (depth+1) k))
                              | i <- [0..(P.length tfs)-1]
                              ]
analyseTypes cogIcTyp icTyp depth fieldName 
    | (TyCon _ cn) <- icTyp = HsEmbedLayout icTyp HsPrim (getConFields cn)
    where getConFields cn = M.fromList $ case (checkIsPrim cn) of 
                          Just x -> [(fieldName, Left depth)] 
                          Nothing -> []
analyseTypes cogIcTyp icTyp depth fieldName 
    | (TyApp _ l r) <- icTyp 
    = let (maybeConName:fieldTypes) = unfoldAppCon icTyp
          cogFields = getFields cogIcTyp
          conName = case maybeConName of 
                      (TyCon _ (UnQual _ (Ident _ n))) -> n
                      _ -> __impossible $ "Bad Constructor name"++show l++"--"++show r
          groupTag = case cogIcTyp of 
                       (CC.TRecord _ fs _) -> HsRecord
                       (CC.TSum alts) -> HsVariant
        in HsEmbedLayout l groupTag $ 
            M.fromList [ ( (fst (cogFields!!i))
                         , let f = cogFields!!i
                             in Right (analyseTypes (fst (snd f)) (fieldTypes!!i) (depth+1) (fst f))
                         )
                       | i <- [0..(P.length cogFields)-1]
                       ]
analyseTypes cogIcTyp icTyp depth fieldName 
    | (TyList _ ty) <- icTyp 
    = let elemCogTy = case cogIcTyp of 
                     (CC.TArray t _ _ _) -> t
                     _ -> __impossible $ "Bad Abstraction"++" --> "++"Hs: "++show icTyp
        in HsEmbedLayout icTyp HsList $ M.fromList [ ( "1" , Right (analyseTypes elemCogTy ty (depth+1) "1")) ]
analyseTypes cogIcTyp icTyp depth fieldName 
    | _ <- icTyp 
    = __impossible $ "Bad Abstraction"++" --> "++"Hs: "++show icTyp

{-
 - TODO: 
 -      For the sake of completeness ... ensure these can never really occur
 -
        (TyFun _ iTy oTy) -> __impossible "TODO: Abstacting from function"
        (TyVar _ name) -> __impossible "TODO: Abstacting from a type variable"
        (TyInfix _ lTy name rTy) -> __impossible "TODO: Abstacting from a infix type constructor"
        (TyUnboxedSum _ tfs) -> __impossible "Compiler should never produce TyUnboxedSum embedding"
        otherwise -> __impossible "Bad abstraction"
-}

-- Helpers
-- ----------------------------------------------------------------------------------------------------

mkViewInfixE :: String -> GroupTag -> Maybe (Exp ()) -> String -> Exp ()
mkViewInfixE varToView tag prev accessor
    = let viewE = case tag of 
                    HsVariant -> mkOp "^?"
                    _ -> mkOp "^."
        in case prev of 
             Just x -> infixApp x (mkOp ".") $ mkVar accessor
             Nothing -> infixApp (mkVar varToView) viewE $ mkVar accessor

mkFromIntE :: Type () -> Exp () -> Exp ()
mkFromIntE ty prev = 
    if | isFromIntegral ty -> infixApp prev (mkOp "$") (function "fromIntegral")
       | otherwise -> prev

mkVar :: String -> Exp ()
mkVar = var . mkName

mkOp :: String -> QOp ()
mkOp = op . mkName


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
                   _ -> [t]

prims = ["Word8","Word16","Word32","Word64","Bool","String"]
        ++ ["Int"]

checkIsPrim :: QName () -> Maybe String
checkIsPrim x = case x of 
    (UnQual _ (Ident _ n)) -> find (\x -> x == n) prims
    _ -> Nothing

isInt' :: QName () -> Bool
isInt' (UnQual _ (Ident _ n)) = checkTy n ["Int"]
isInt' _ = False

isInt :: Type () -> Bool
isInt (TyCon _ (UnQual _ (Ident _ n))) = checkTy n ["Int"]

isFromIntegral :: Type () -> Bool
isFromIntegral (TyCon _ (UnQual _ (Ident _ n))) 
    = any (==n) ["Word8","Word16","Word32","Word64"]

checkTy :: String -> [String] -> Bool
checkTy n xs = any (\x -> n == x) xs

rmdups :: (Ord a) => [a] -> [a]
rmdups = map P.head . group . sort

getConNames :: HsEmbedLayout -> [String] -> [String]
getConNames tyL acc 
    = let hsTy = tyL ^. hsTyp
          ty = tyL ^. grTag
          fld = tyL ^. fieldMap
        in concatMap (\(_,f) -> case f of 
            Left _ -> acc
            Right next -> case ty of 
                               HsPrim -> acc
                               HsRecord -> getConNames next acc++conNames hsTy
                               HsVariant -> getConNames next acc++conNames hsTy
                               _ -> getConNames next acc
                where conNames hsTy = let (c:cs) = unfoldAppCon hsTy
                                        in case c of 
                                             (TyCon _ (UnQual _ (Ident _ n))) -> [n]
                                             _ -> []
        ) $ M.toList fld

-- ----------------------------------------------------------------------------------------------------


-- | mkRrelBody 
-- | dummy func ATM
-- --------------------------------------------------
mkRrelBody :: CC.Type t a -> Type () -> SG (Exp ())
mkRrelBody concT absT = pure $ function $ "undefined"
