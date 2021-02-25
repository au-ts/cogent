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
                       P.map importSym ["+", "-", "*", "&&", "||", ">", ">=", "<", "<=", "==", "/="] ++
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
        return $ [sig, dec] --, icT']

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
        absE <- mkAbsFBody'' ti ti' iaT
        pure $ ({-TyCon () (mkQName "Unknown") -} ti', iaT, absE)

genAbsFTypsAndExp' def iaT | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    absE <- mkAbsFBody ti iaT
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

-- | mkAbsFBody 
-- |    - direct mapping
-- |    - Abstract Input Type is the input type of the Haskell abstract spec
-- |    - Concrete Input Type is the input type of the concrete function (Cogent HS embedding)
-- ^^ Type surrounded by parens, recurse on inside type
-- ^^ IA is Tuple, fs is [(FieldName, (Type t b, Bool))]



{- match on haskell types -> default access using Lens
    every type has a lens
-}
mkAbsFBody'' :: CC.Type t a -> Type () -> Type () -> SG (Exp ())
mkAbsFBody'' cogIcTyp icTyp iaTyp 
    = case iaTyp of 
        (TyTuple _ _ tfs) -> mkTupFrom'' cogIcTyp icTyp iaTyp
        otherwise -> __impossible "boom"
    
mkTupFrom'' :: CC.Type t a -> Type () -> Type () -> SG (Exp ())
mkTupFrom'' cogIcTyp icTyp iaTyp 
    = do
        accessorMap <- mkAbsFBobyWithLens cogIcTyp icTyp iaTyp 
        let iaFieldNames = map (\v -> mkName $ (snm $ fst v)++"'") $ M.toList accessorMap
            iaBindPats = map (\v -> pvar . mkName $ (snm $ fst v)++"'") $ M.toList accessorMap
            iaBindExps = map snd $ M.toList accessorMap
            body = tuple $ map var iaFieldNames
            binds = P.zip iaBindPats iaBindExps
        pure $ mkLetE binds body
            

-- @cogIcTyp@ is the original cogent type
-- @icTyp@ is the hs embedding of cogent type 
-- @iaTyp@ is the user supplied type we are trying to abstract to
mkAbsFBobyWithLens :: CC.Type t a -> Type () -> Type () -> SG (M.Map String (Exp ()))
mkAbsFBobyWithLens cogIcTyp hsIcTyp hsIaTyp 
    = case hsIcTyp of
        (TyParen _ t   ) -> mkAbsFBobyWithLens cogIcTyp t hsIaTyp
        (TyTuple _ _ tfs) -> handleIcTup cogIcTyp hsIcTyp hsIaTyp
        (TyCon _ cn    ) -> handleIcCon cogIcTyp hsIcTyp hsIaTyp
        (TyApp _ conT fsT) -> handleIcApp cogIcTyp hsIcTyp hsIaTyp
        (TyList _ t    ) -> __impossible "TODO"
        otherwise -> __impossible "TODO"


-- Handle when IC is tuple --> Lens view for each field
-- return map where field name maps to view expression
handleIcTup :: CC.Type t a -> Type () -> Type () -> SG (M.Map String (Exp ()))
handleIcTup cogIcTyp (TyTuple _ _ tfs) hsIaTyp 
    -- for each tuple field create view
    = let 
        icVarName = var $ mkName "ic"
       in case cogIcTyp of 
           (CC.TRecord _ fs _) -> pure $ M.fromList $ mkGetter icVarName $ P.zip (map fst fs) tfs
           (CC.TSum tags) -> undefined
           (CC.TProduct l r) -> undefined

handleIcApp :: CC.Type t a -> Type () -> Type () -> SG (M.Map String (Exp ()))
handleIcApp cogIcTyp (TyApp _ conT fsT) hsIaTyp 
    -- for each tuple field create view
    = let 
        icVarName = var $ mkName "ic"
       in case cogIcTyp of 
           (CC.TRecord _ fs _) -> pure $ M.fromList $ mkGetter' icVarName $ map fst fs
           (CC.TSum tags) -> undefined
           (CC.TProduct l r) -> undefined


handleIcCon :: CC.Type t a -> Type () -> Type () -> SG (M.Map String (Exp ()))
handleIcCon cogIcTyp (TyCon _ cn) hsIaTyp 
    = undefined


mkGetter :: Exp () -> [(FieldName, Type ())] -> [(String, Exp ())]
mkGetter varToView fields 
    = [ let (fn, ty) = fields !! i 
         in (fn, infixApp varToView viewInfixExp (mkAccess i)) 
            | i <- [0..(P.length fields)-1]
      ]

mkGetter' :: Exp () -> [FieldName] -> [(String, Exp ())]
mkGetter' varToView fields 
    = [ (fn, infixApp varToView viewInfixExp (mkAccess' fn)) 
        | fn <- fields
      ]

viewInfixExp :: QOp ()
viewInfixExp = op $ mkName "^."

mkAccess :: Int -> Exp ()
mkAccess i = var $ mkName $ "_"++show i

mkAccess' :: String -> Exp ()
mkAccess' i = var $ mkName i
    


-- checking the provided Abstract type
mkAbsFBody :: CC.Type t a -> Type () -> SG (Exp ())
mkAbsFBody icTyp (TyParen _ t   ) = mkAbsFBody icTyp t
mkAbsFBody icTyp (TyTuple _ _ tfs) = mkTupFrom icTyp "ic"
mkAbsFBody icTyp (TyCon _ cn    ) = __impossible "Bad abstraction"
mkAbsFBody icTyp (TyList _ t    ) = __impossible "Bad abstraction"

-- Convert Cogent type to Tuple
mkTupFrom :: CC.Type t a -> String -> SG (Exp ())
mkTupFrom icTyp name 
    -- | TVar (Fin t)
    -- | TVarBang (Fin t)
    -- | TVarUnboxed (Fin t)
    -- | TCon TypeName [Type t b] (Sigil ()) -- Layout will be nothing for abstract types
    -- | TFun (Type t b) (Type t b)
    -- | TPrim PrimInt
    -- | TString
    | (CC.TSum tags) <- icTyp = undefined
    | (CC.TProduct l r) <- icTyp = undefined
    | (CC.TRecord _ fs _) <- icTyp = do 
        let icName = mkConE $ mkName name
            iaFieldNames = map (\v -> mkName $ snm $ fst v) fs
            iaBindPats = map (\v -> pvar . mkName $ snm $ fst v) fs
            body = tuple $ map var iaFieldNames
        shGetFields <- P.mapM (\x -> shGetter' icTyp (map fst fs) x icName) [0..P.length iaBindPats]
        let
            binds = P.zip iaBindPats shGetFields
        pure $ mkLetE binds body
    -- | TUnit
    -- | TRPar     RecParName (RecContext (Type t b))
    -- | TRParBang RecParName (RecContext (Type t b))
-- #ifdef BUILTIN_ARRAYS
    -- | TArray (Type t b) (LExpr t b) (Sigil (DataLayout BitRange)) (Maybe (LExpr t b))  -- the hole
    -- | TRefine (Type t b) (LExpr t b)


-- | Like shallowGetter functions but for Cogent Type
-- --------------------------------------------------
shGetter :: CC.Type t a -> [FieldName] -> FieldIndex -> Exp () -> SG (Exp ())
shGetter rec fnms idx rec' = do
  tuples <- view recoverTuples
  return $ if | tuples, isRecTuple fnms -> appFun (mkQVarE "Tup" . mkName $ "sel" ++ show (idx+1)) [rec']
              | otherwise -> appFun (var . mkName . snm $ getRecordFieldName' rec idx) [rec']


shGetter' :: CC.Type t a -> [FieldName] -> FieldIndex -> Exp () -> SG (Exp ()) 
shGetter' rec fnms idx rec' = do
  tuples <- view recoverTuples
  if | tuples, isRecTuple fnms -> shGetter rec fnms idx rec'
     | otherwise -> do
         let t@(CC.TRecord _ fs _) = rec
         vs <- mapM (\_ -> freshInt <<+= 1) fs
         (tn,_) <- nominalType t
         let bs = P.map (\v -> mkName $ internalVar ++ show v) vs
             p' = PRec () (UnQual () $ mkName tn)
                       (P.zipWith (\(f,_) b -> PFieldPat () (UnQual () . mkName $ snm f) (pvar b)) fs bs)
         pure $ mkLetE [(p',rec')] $ var (bs !! idx)

getRecordFieldName' :: CC.Type t a -> FieldIndex -> FieldName
getRecordFieldName' rec idx | CC.TRecord _ fs _ <- rec = P.map fst fs !! idx
getRecordFieldName' _ _ = __impossible "input should be of record type"












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
             pure $ mkLetE [(p',rec')] $ tuple $ map (\x -> app (function "fromIntegral") (var x)) bs
    (CC.TCon tn ts _)   -> pure $ function $ "undefined"
    (CC.TSum ts)        -> pure $ function $ "undefined"
    (CC.TProduct t1 t2) -> pure $ var $ mkName "ic"

    -- ^^ Cogent Tuple, unwrap with letE, 
    _                   -> pure $ function $ "undefined"



unwrapRTup' :: CC.Type t a -> String -> (CC.Definition TypedExpr VarName b) -> SG (Exp ())
unwrapRTup' concT varN def | (CC.TRecord _ fs _) <- concT = do
      let rec' = mkConE $ mkName varN
          bs = P.map (\v -> mkName $ snm $ fst v) fs
          p1 = pvar . mkName $ snm "p1"  -- taken field
          p2 = pvar . mkName $ snm "p2"  -- new record
          -- rect@(CC.TRecord _ fs _) = concT
      p1' <- shGetter' concT (map fst fs) 0 rec'  -- SH.shallowGetter typedExpr (map fst fs) 0 rec'
      p2' <- shGetter' concT (map fst fs) 1 rec'
      pure $ mkLetE [(p1, p1'), (p2, p2')] $ tuple $ map var bs

unwrapRTup' concT varN def | (CC.TCon tn ts _) <- concT = pure $ function $ "undefined" 
unwrapRTup' concT varN def | (CC.TSum ts) <- concT = pure $ function $ "undefined"
unwrapRTup' concT varN def | (CC.TProduct t1 t2) <- concT = pure $ function $ "undefined"
unwrapRTup' concT varN def = pure $ var $ mkName varN






-- | mkRrelBody 
-- | dummy func ATM
-- --------------------------------------------------
mkRrelBody :: CC.Type t a -> Type () -> SG (Exp ())
mkRrelBody concT absT = pure $ function $ "undefined"
