{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}

-- | Haskell PBT generator
--
-- Generates Hs functions which are used in Property-Based Testing

module Cogent.Haskell.PBT.Gen (
  pbtHs
) where

import Cogent.Isabelle.ShallowTable (TypeStr(..), st)
import qualified Cogent.Core as CC
import Cogent.Core (TypedExpr(..))
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Haskell.HscGen
import Cogent.Haskell.ParseDSL
import Cogent.Util ( concatMapM, Stage(..), delimiter, secondM, toHsTypeName, concatMapM, (<<+=) )
import Cogent.Compiler (__impossible)
import qualified Cogent.Haskell.HscSyntax as Hsc
import qualified Data.Map as M
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.SrcLoc
import Text.PrettyPrint
import Debug.Trace
import Cogent.Haskell.PBT.DSL.Types
import Cogent.Haskell.PBT.Types
import Cogent.Haskell.GenDSL
import Cogent.Haskell.Shallow as SH
import Prelude as P
import Data.Tuple
import Data.Function
import Data.Maybe
import Data.Either
import Data.List (find, partition, group, sort)
import Data.Generics.Schemes (everything)
import Control.Arrow (second, (***), (&&&))
import Control.Applicative
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Control.Monad.RWS hiding (Product, Sum, mapM)
import Data.Vec as Vec hiding (sym)
import Cogent.Isabelle.Shallow (isRecTuple)

-- type FFIFuncs = M.Map FunName (CType, CType)
-- FFIFuncs       -- FFI functions, mapping func name to input/output type
-- -> String         -- Hsc file name
      -- -> [CExtDecl]     -- C decls (UNUSED ATM)

-- type Gen a = ReaderT (FFIFuncs, [FunName]) Identity a

pbtHs :: String         -- Module Name
      -> String         -- Hsc Module Name (for imports)
      -> [PbtDescStmt]      -- List of PBT info for the Cogent Functions
      -> [CC.Definition TypedExpr VarName b]  -- A list of Cogent definitions
      -> [CC.CoreConst TypedExpr]             -- A list of Cogent constants
      -> String         -- Log header 
      -> String
pbtHs name hscname pbtinfos decls consts log = render $
  let mod = propModule name hscname pbtinfos decls
    -- flip runReader (m, map ("prop_" ++) $ M.keys m) $ propModule name hscname decls pbtinfos
    in text "{-" $+$ text log $+$ text "-}" $+$ prettyPrim mod

-- -> Gen (Module ()) 
propModule :: String -> String -> [PbtDescStmt] -> [CC.Definition TypedExpr VarName b] -> Module ()
propModule name hscname pbtinfos decls =
  let (cogDecls, w) = evalRWS (runSG $ do
                                          shallowTypesFromTable
                                          genDs <- concatMapM (\x -> genDecls'' x decls) pbtinfos
                                          absDs <- concatMapM (\x -> absFDecl' x decls) pbtinfos
                                          rrelDs <- concatMapM (\x -> rrelDecl' x decls) pbtinfos
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
             , ImportDecl () (ModuleName () "Lens.Micro.TH") False False False Nothing Nothing (Just $ ImportSpecList () False (map importVar ["makeLenses"]))
             , ImportDecl () (ModuleName () "Control.Lens.Combinators") False False False Nothing Nothing (Just $ ImportSpecList () False (map importVar ["makePrisms"]))
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
      hs_decls = rmdups ls ++ P.concatMap propDecls' pbtinfos ++ cogD
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

propDecls' :: PbtDescStmt -> [Decl ()]
propDecls' desc 
    = let fn    = desc ^. funcname
          ds    = mkPropBody' fn $ desc ^. decls
          fnName = "prop_" ++ fn
          toName = "Property"
          to     = TyCon   () (mkQName toName)
          sig    = TypeSig () [mkName fnName] to
          dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ ds ) Nothing]
        in [sig, dec]

findExprsInDecl :: PbtKeyword -> [PbtDescDecl] -> [PbtDescExpr]
findExprsInDecl x ds = let res = fromJust $ find (\d -> case (d ^. kword) of x -> True; _ -> False) ds
                         in res ^. kexprs

-- find ic/ia/oc/oa type and expression
findKvarsInDecl :: PbtKeyword -> PbtKeyvars -> [PbtDescDecl] -> (PbtKeyvars, Maybe (Type ()), Maybe (Exp ()))
findKvarsInDecl x y ds 
    = let decl = case (find (\d -> (d ^. kword) == x) ds) of 
                   Just x -> x
                   Nothing -> __impossible $ "The decl: "++show x++ " was not specified"
          exprs = filter (\e -> case (e ^. kvar) of 
                             Just y' -> y' == y; _ -> False
                  ) $ decl ^. kexprs
          in ( y
               -- find ty
             , (exprs ^.. each . kexp . _Just . _Left) ^? ix 0
               -- find mapping exp associated with this keyvar
             , (exprs ^.. each . kexp . _Just . _Right) ^? ix 0 )

checkBoolE :: [PbtDescExpr] -> Bool
checkBoolE a = case ((a ^.. each . kexp . _Just . _Left) ^? ix 0) of 
                     Just x -> boolResult x
                     _ -> False

mkPropBody' :: String -> [PbtDescDecl] -> Exp ()
mkPropBody' n ds
    = let isPure = checkBoolE $ findExprsInDecl Pure ds
          isNond = checkBoolE $ findExprsInDecl Nond ds
          ia = app (function $ "abs_"++n) (var $ mkName "ic")
          oc = app (function n)           (var $ mkName "ic")
          oa = app (function $ "hs_"++n)  ia
          binds = [ FunBind () [Match () (mkName "oc") [] (UnGuardedRhs () oc  ) Nothing]
                  , FunBind () [Match () (mkName "oa") [] (UnGuardedRhs () oa  ) Nothing] ]
          binds' =  [ genStmt (pvar $ mkName "oc") oc
                    , genStmt (pvar $ mkName "oa") (app (function "return") oa)
                    , qualStmt body ]
          body  = appFun (function $ (if isPure then "corres" else "corresM")++(if not isNond then "'" else ""))
                         [ function $ "rel_"++n , var $ mkName "oa" , var $ mkName "oc" ]
          f  = if isPure then function "forAll" else function "forAllM"
          fs = [ function $ "gen_"++n
               , lamE [pvar $ mkName "ic"] (if isPure then letE binds body else doE binds') ]
        in if isPure then appFun f fs
           else app (function "monadicIO") $ appFun f fs
          
-- TODO: Delete !!!
mkPropBody :: String -> FunDefs -> Exp ()
mkPropBody n FunInfo{ispure=True, nondet=nd} =
    let f  = function "forAll"
        fs = [ function $ "gen_"++n
             , lamE [pvar $ mkName "ic"] (letE binds body) ]
            where ia = app (function $ "abs_"++n) (var $ mkName "ic")
                  oc = app (function n)           (var $ mkName "ic")
                  oa = app (function $ "hs_"++n)  ia
                  binds = [ FunBind () [Match () (mkName "oc") [] (UnGuardedRhs () oc  ) Nothing]
                          , FunBind () [Match () (mkName "oa") [] (UnGuardedRhs () oa  ) Nothing] ]
                  body  = appFun (function $ "corres"++(if not nd then "'" else ""))
                                 [ function $ "rel_"++n
                                 , var $ mkName "oa"
                                 , var $ mkName "oc" ]
        in appFun f fs
-- TODO: Delete !!!
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
                 body  = appFun (function $ "corresM"++(if not nd then "'" else ""))
                                [ function $ "rel_"++n
                                , var $ mkName "oa"
                                , var $ mkName "oc" ]
        in app (function "monadicIO") (appFun f fs)

-- -----------------------------------------------------------------------
-- Cogent PBT: Generator for Test data generators
-- -----------------------------------------------------------------------
-- TODO: fix up DSL to handle this
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
        -- (icT, _, absE) <- mkAbsFExp fname iaT defs
        let fnName = "gen_" ++fname
            --toName = "Gen " ++ show icT' -- ++icT
            --to     = TyCon   () (mkQName toName)
            --sig    = TypeSig () [mkName fnName] to
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $
                        mkGenBody fname icT) Nothing]
            hs_dec    = FunBind () [Match () (mkName $ "hs_"++fname) [] (UnGuardedRhs () $
                        function "undefined") Nothing]
            -- cls    = ClassDecl () () [] ()
          in return [dec, hs_dec] --[sig, dec] --, icT']

genDecls'' :: PbtDescStmt -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
genDecls'' stmt defs = do
        let (_, icTy, icExp) = findKvarsInDecl Absf Ic $ stmt ^. decls
            fnName = "gen_" ++ stmt ^. funcname
            genCon = TyCon () (mkQName "Gen")
            tyOut = TyApp () genCon $ case icTy of 
                                        Just x -> TyParen () x
                                        Nothing -> TyCon () $ mkQName "Unknown"
            -- sig    = TypeSig () [mkName fnName] tyOut
            -- TODO: better gen_* body
            --       - what else do you need for arbitrary?
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $
                        function "undefined") Nothing]
            -- TODO: this is a dummy HS spec function def -> replace with something better
            hs_dec    = FunBind () [Match () (mkName $ "hs_"++(stmt ^. funcname)) [] (UnGuardedRhs () $
                           function "undefined") Nothing]
          in return [dec, hs_dec]

-- Abstraction Function Generator
absFDecl :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
absFDecl PBTInfo{..} defs = do
        let FunAbsF{absf=_, ityps=ityps} = fabsf
            -- icT = fromJust $ P.lookup "IC" ityps
            iaT = fromJust $ P.lookup "IA" ityps
            fnName = "abs_" ++fname
        (icT, _, absE, conNames) <- mkAbsFExp fname iaT defs
        let ti     = icT
            to     = iaT
            sig    = TypeSig () [mkName fnName] (TyFun () ti to)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "ic"] (UnGuardedRhs () absE) Nothing]
        return $ map mkLens (takeWhile (\x -> notElem x hsSumTypes) conNames)++[sig, dec]


-- Abstraction Function Generator
absFDecl' :: PbtDescStmt -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
absFDecl' stmt defs = do
        let (_, iaTy, iaExp) = findKvarsInDecl Absf Ia $ stmt ^. decls
            fnName = "abs_" ++ stmt ^. funcname
            iaT = case iaTy of 
                      Just x -> x
                      Nothing -> __impossible "specify ia type please"
        (icT, _, absE, conNames) <- mkAbsFExp (stmt ^. funcname) iaT defs
        let e = case iaExp of 
                  Just x -> x
                  -- TODO: ^^ any automation we can add in here? e.g. fromIntegral
                  --          --> just allow any haskell func defn
                  {-
                   let upack = determineUnpack' icT 0 "None"
                                tyns = getAllTypeNames upack []
                              in if | any (\x -> x `elem` ["Word8","Word16","Word32","Word64"])
                              -}
                  Nothing -> absE
        let ti     = icT
            to     = iaT
            sig    = TypeSig () [mkName fnName] (TyFun () ti to)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "ic"] (UnGuardedRhs () e) Nothing]
        return $ map mkLens (takeWhile (\x -> notElem x hsSumTypes) conNames)++[sig, dec]

-- TODO: delete
-- Refinement Relation Generator
rrelDecl :: PBTInfo -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
rrelDecl PBTInfo{..} defs = do
        let FunRRel{rrel=_, otyps=otyps} = frrel
            oaT = fromJust $ P.lookup "OA" otyps
            fnName = "rel_" ++fname
        (ocT, _, rrelE, conNames) <- mkRrelExp fname oaT defs
        -- (ocT, _, rrelE) <- mkAbsFExp fname oaT defs
        let to     = mkTyConT $ mkName "Bool"
            ti     = TyFun () oaT $ TyFun () ocT to
            sig    = TypeSig () [mkName fnName] ti
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "oa", pvar $ mkName "oc"] (UnGuardedRhs () rrelE) Nothing]
        return $ map mkLens (takeWhile (\x -> notElem x hsSumTypes) conNames)++[sig, dec]

-- Refinement Relation Generator
rrelDecl' :: PbtDescStmt -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
rrelDecl' stmt defs = do
        let (_, oaTy, oaExp) = findKvarsInDecl Rrel Oa $ stmt ^. decls
            fnName = "rel_" ++ stmt ^. funcname
            oaT = case oaTy of 
                      Just x -> x
                      Nothing -> __impossible $ "specify oa type please, stmt: "++ show stmt
        (ocT, _, rrelE, conNames) <- mkRrelExp (stmt ^. funcname) oaT defs
        let to     = mkTyConT $ mkName "Bool"
            ti     = TyFun () oaT $ TyFun () ocT to
            sig    = TypeSig () [mkName fnName] ti
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "oa", pvar $ mkName "oc"] (UnGuardedRhs () rrelE) Nothing]
        return $ map mkLens (takeWhile (\x -> notElem x hsSumTypes) conNames)++[sig, dec]

mkLens :: String -> Decl ()
mkLens t
    = let fname = if | P.head t == 'R' -> "makeLenses"
                     | P.head t == 'V' -> "makePrisms"
                     | otherwise -> "undefined"
       in SpliceDecl () $ app (function fname) (TypQuote () (UnQual () (mkName t)))

-- Get Function Type and Expression
-- ------------------------------------------
-- @fname@ is the name of the function
-- @iaTyp@ is the abstract input type
-- @defs@ is the list of Cogent definitions
--
-- ------------------------------------------------------
mkAbsFExp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> SG (Type (), Type (), Exp (), [String])
mkAbsFExp fname iaTyp defs = do
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (icT, iaT, absE, conNames) <- mkAbsFExp' def iaTyp
    pure (icT, iaT, absE, conNames)

-- Helper: get function type and expression
mkAbsFExp' :: CC.Definition TypedExpr VarName b -> Type () -> SG (Type (), Type (), Exp (), [String])
mkAbsFExp' def iaT | (CC.FunDef _ fn ps _ ti to _) <- def
    = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
        ti' <- shallowType ti
        (absE, conNames) <- mkAbsFBody ti ti' iaT
        pure (ti', iaT, absE, conNames)

mkAbsFExp' def iaT | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (absE, conNames) <- mkAbsFBody ti ti' iaT
    pure ( ti', iaT, absE, conNames)

mkAbsFExp' def iaT | (CC.TypeDef tn _ _) <- def
    = pure (TyCon () (mkQName "Unknown"), iaT, function $ "undefined", [])
-- ------------------------------------------------------

-- ------------------------------------------------------
mkRrelExp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> SG (Type (), Type (), Exp (), [String])
mkRrelExp fname oaTyp defs = do
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (ocT, oaT, rrelE, conNames) <- mkRrelExp' def oaTyp
    pure (ocT, oaT, rrelE, conNames)

-- Helper: get function type and expression
mkRrelExp' :: CC.Definition TypedExpr VarName b -> Type () -> SG (Type (), Type (), Exp (), [String])
mkRrelExp' def oaT | (CC.FunDef _ fn ps _ ti to _) <- def
    = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
        to' <- shallowType to
        (rrel, conNames) <- mkRrelBody to to' oaT
        pure (to', oaT, rrel, conNames)

mkRrelExp' def oaT | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    to' <- shallowType to
    (absE, conNames) <- mkRrelBody to to' oaT
    pure ( to', oaT, absE, conNames)

mkRrelExp' def oaT | (CC.TypeDef tn _ _) <- def
    = pure (TyCon () (mkQName "Unknown"), oaT, function $ "undefined", [])

-- ------------------------------------------------------


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
    = let icLayout = determineUnpack cogIcTyp icTyp 0 "None"
          lens = map fst $ mkLensView icLayout "ic" Unknown Nothing
          binds = map ((\x -> pvar . mkName . fst $ x) &&& snd) lens
          body = packAbsCon iaTyp (map fst lens) 0
       in pure (mkLetE binds body, getConNames icLayout [])

-- | mkRrelBody 
-- | dummy func ATM
-- --------------------------------------------------
mkRrelBody :: CC.Type t a -> Type () -> Type () -> SG (Exp (), [String])
mkRrelBody cogOcTyp ocTyp oaTyp
    = let ocLy = determineUnpack cogOcTyp ocTyp 0 "None"
          oaLy = determineUnpack' oaTyp 0 "None"
          ocLens' = mkLensView ocLy "oc" Unknown Nothing
          oaLens' = mkLensView oaLy "oa" Unknown Nothing
          ocLens = map fst ocLens'
          oaLens = map fst oaLens'
          ls = oaLens ++ ocLens
          cNames = getConNames ocLy [] ++ getConNames oaLy []
          binds = map ((\x -> pvar . mkName . fst $ x) &&& snd) ls
          tys = map snd ocLens' 
          ocVars = map fst ocLens
          oaVars = map fst oaLens
          body = mkCmpExp (zip3 oaVars ocVars tys) Nothing
       in pure (mkLetE binds body, cNames)

-- generate exp for packing the constructor that is returned by absf
-- 1st = type
-- 2nd = list of vars to put in the constructor
-- 3rd = position in structure
-- vars are pack left to right from the list
-- removing vars from list as they are added in the recursion
-- TODO: unify the vars with the outgoing matching type
-- TODO: pair varsToPut with types for that var
-- ----------------------------------------------------------------------------------------------------
packAbsCon :: Type () -> [String] -> Int -> Exp ()
packAbsCon (TyParen _ insideTy) varsToPut pos = packAbsCon insideTy varsToPut pos
packAbsCon (TyTuple _ _ ftys) varsToPut pos
    -- give each subtype is appropriate var
    = tuple $ let vs = if P.length ftys == P.length varsToPut then varsToPut else take (P.length ftys) varsToPut
                in [ packAbsCon (ftys!!i) vs i | i <- [0..P.length ftys-1] ]
packAbsCon (TyCon _ name) varsToPut pos
    = case checkIsPrim name of
        -- transform if needs coercion
        Just x -> if isInt' name then app (function "fromIntegral") $ mkVar $ varsToPut!!pos else mkVar $ varsToPut!!pos
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
        in appFun (mkVar name) $ let vs = if P.length fieldTypes == P.length varsToPut then varsToPut else take (P.length fieldTypes) varsToPut
                                               in [ packAbsCon (fieldTypes!!i) vs i | i <- [0..P.length fieldTypes-1] ]
                where
packAbsCon (TyList _ ty) varsToPut pos = mkVar $ varsToPut!!pos
packAbsCon iaTyp varsToPut prev | _ <- iaTyp = __impossible $ "Bad Abstraction"++" --> "++"Hs: "++show iaTyp
-- ----------------------------------------------------------------------------------------------------

-- default to equality now
-- ----------------------------------------------------------------------------------------------------
mkCmpExp :: [(String, String, (Type (), GroupTag))] -> Maybe (Exp ()) -> Exp ()
mkCmpExp [] prev 
    = case prev of 
        Just x -> x
        Nothing -> __impossible "boom!"
mkCmpExp (v:vs) prev 
    = case prev of 
        Just x -> mkCmpExp vs $ Just $ infixApp x (mkOp "&&") $ mkEqExp v
        Nothing -> mkCmpExp vs $ Just $ mkEqExp v

mkEqExp :: (String, String, (Type (), GroupTag)) -> Exp ()
mkEqExp (oa, oc, (ty, grp)) 
    = let op = case grp of 
                 HsVariant -> "<&>"
                 _ -> "&"
          mkInfixEq x y = infixApp x (mkOp "==") y
        in if isFromIntegral ty 
            then mkInfixEq (mkVar oa) $ paren $ infixApp (mkVar oc) (mkOp op) (function "fromIntegral")
            else mkInfixEq (mkVar oa) (mkVar oc) 
-- ----------------------------------------------------------------------------------------------------

-- | mkLensView
-- ---------------
-- TODO: clean up comment
-- from Layout return list of pairs: variable name for bind and the view expression
-- key = var name ++ depth tag
-- val = 
-- ----------------------------------------------------------------------------------------------------
mkLensView :: HsEmbedLayout -> String -> GroupTag -> Maybe (Exp ()) -> [((String, Exp ()), (Type (), GroupTag))]
mkLensView layout varToView prevGroup prev
    = let hsTy = layout ^. hsTyp
          group = layout ^. grTag
          fld = layout ^. fieldMap
          -- field map is a tree with int leaves -> only build vars for leaves
       in concatMap ( \(k, v) -> case group of
        HsPrim -> case v of
           (Left depth) -> [ (( k ++ replicate depth (P.head "'")
                             , case prev of Just x -> x
                                            Nothing -> mkVar varToView
                             )
                             , (hsTy, prevGroup)
                             )
                           ]
           (Right next) -> __impossible $ show k ++ " " ++ show v
        _ -> case v of
           (Left depth) -> __impossible $ show k ++ " " ++ show v
           (Right next) -> mkLensView next varToView group $ Just $ mkViewInfixE varToView group prev k
       ) $ M.toList fld

-- | determineUnpack
-- ---------------
-- | Builds the structure used for generating the body of absf
-- ----------------------------------------------------------------------------------------------------
determineUnpack :: CC.Type t a -> Type () -> Int -> String -> HsEmbedLayout
determineUnpack cogIcTyp (TyParen _ t   ) depth fieldName = determineUnpack cogIcTyp t depth fieldName
determineUnpack cogIcTyp icTyp depth fieldName
    | (TyTuple _ _ tfs) <- icTyp = HsEmbedLayout icTyp HsTuple $ getTupFields cogIcTyp tfs
    where getTupFields cogTy tfs
            = let fs = getFields cogTy
                in M.fromList [ let k = "_"++show (i+1)
                                  in (k , Right (determineUnpack (fst (snd (fs!!i))) (tfs!!i) (depth+1) k))
                              | i <- [0..P.length tfs-1]
                              ]
determineUnpack cogIcTyp icTyp depth fieldName
    | (TyCon _ cn) <- icTyp = HsEmbedLayout icTyp HsPrim (getConFields cn)
    where getConFields cn = M.fromList $ case checkIsPrim cn of
                          Just x -> [(fieldName, Left depth)]
                          Nothing -> []
determineUnpack cogIcTyp icTyp depth fieldName
    | (TyApp _ l r) <- icTyp
    = let (maybeConName:fieldTypes) = unfoldAppCon icTyp
          cogFields = getFields cogIcTyp
          conName = case maybeConName of
                      (TyCon _ (UnQual _ (Ident _ n))) -> n
                      _ -> __impossible $ "Bad Constructor name"++show l++"--"++show r
          groupTag = case cogIcTyp of
                       (CC.TRecord _ fs _) -> HsRecord
                       (CC.TSum alts) -> HsVariant
          accessors = getAccessor conName groupTag fieldTypes (Just (map fst cogFields))
        in HsEmbedLayout l groupTag $
            M.fromList [ let a = accessors!!i
                             f = cogFields!!i
                           in ( a
                              , Right (determineUnpack (fst (snd f)) (fieldTypes!!i) (depth+1) a)
                              )
                       | i <- [0..P.length cogFields-1]
                       ]
determineUnpack cogIcTyp icTyp depth fieldName
    | (TyList _ ty) <- icTyp
    = let elemCogTy = case cogIcTyp of
                     (CC.TArray t _ _ _) -> t
                     _ -> __impossible $ "Bad Abstraction"++" --> "++"Hs: "++show icTyp
        in HsEmbedLayout icTyp HsList $ M.fromList [ ( "1" , Right (determineUnpack elemCogTy ty (depth+1) "1")) ]
determineUnpack cogIcTyp icTyp depth fieldName
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


-- | determineUnpack'
-- ---------------
-- | Builds the structure used for generating the body of rrel
-- ----------------------------------------------------------------------------------------------------
determineUnpack' :: Type () -> Int -> String -> HsEmbedLayout
determineUnpack' (TyParen _ t   ) depth fieldName = determineUnpack' t depth fieldName
determineUnpack' hsTyp depth fieldName | (TyTuple _ _ tfs) <- hsTyp
    = HsEmbedLayout hsTyp HsTuple $
        M.fromList [ let k = "_"++show (i+1)
                       in (k , Right (determineUnpack' (tfs!!i) (depth+1) k))
                   | i <- [0..P.length tfs-1]
                   ]
determineUnpack' hsTyp depth fieldName | (TyCon _ cn) <- hsTyp
    = HsEmbedLayout hsTyp HsPrim $
        M.fromList $ case checkIsPrim cn of
                          Just x -> [(fieldName, Left depth)]
                          Nothing -> []
determineUnpack' hsTyp depth fieldName | (TyApp _ l r) <- hsTyp
    = let (maybeConName:fieldTypes) = unfoldAppCon hsTyp
          conName = case maybeConName of
                      (TyCon _ (UnQual _ (Ident _ n))) -> n
                      _ -> __impossible $ "Bad Constructor name"++show l++"--"++show r
          groupTag = if elem conName hsSumTypes then HsVariant else HsRecord
          -- TODO: unsure if this works - when would oa be a custom record?
          --       Makes more sense to restrict oa to either a prim or a built in hs type rather then allowing
          --       them to define there own records
          fldNames = getAccessor conName groupTag fieldTypes Nothing
        in HsEmbedLayout l groupTag $
            M.fromList [ (  fldNames!!i
                         , Right (determineUnpack' (fieldTypes!!i) (depth+1) (fldNames!!i))
                         )
                       | i <- [0..P.length fieldTypes-1]
                       ]
determineUnpack' hsTyp depth fieldName | (TyList _ ty) <- hsTyp
    = HsEmbedLayout hsTyp HsList $
        M.fromList [ ( "1" , Right (determineUnpack' hsTyp (depth+1) "1")) ]
determineUnpack' hsTyp depth fieldName | _ <- hsTyp = __impossible $ "Bad Abstraction"++" --> "++"Hs: "++show hsTyp


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
    if isFromIntegral ty then infixApp prev (mkOp "$") (function "fromIntegral") else prev

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

getAccessor :: String -> GroupTag -> [Type ()] -> Maybe [String] -> [String]
getAccessor conName groupTag ts fieldNames
    = let fs = case fieldNames of
                 Just x -> x
                 Nothing -> filter (/="None") .
                    map (\x -> case x of
                                (TyCon _ (UnQual _ (Ident _ n))) -> n
                                _ -> "None"
                         ) $ ts
        in case groupTag of
            HsRecord -> fs
            HsVariant -> if | conName == "Maybe" && P.length fs == 1 -> map (const "_Just") fs
                            | conName == "Either" && P.length fs == 2 -> ["_Left", "_Right"]
                            | otherwise -> map (\x -> "_" ++ conName ++ "_" ++ x) fs

prims = ["Word8","Word16","Word32","Word64","Bool","String"]
        ++ ["Int"]

hsSumTypes = ["Maybe","Either"]

checkIsPrim :: QName () -> Maybe String
checkIsPrim x = case x of
    (UnQual _ (Ident _ n)) -> find (== n) prims
    _ -> Nothing

isInt' :: QName () -> Bool
isInt' (UnQual _ (Ident _ n)) = checkTy n ["Int"]
isInt' _ = False

isInt :: Type () -> Bool
isInt (TyCon _ (UnQual _ (Ident _ n))) = checkTy n ["Int"]

isBool :: Type () -> Bool
isBool (TyCon _ (UnQual _ (Ident _ n))) = checkTy n ["Bool"]

boolResult :: Type () -> Bool
boolResult (TyCon _ (UnQual _ (Ident _ n))) = read n
boolResult _ = False

isFromIntegral :: Type () -> Bool
isFromIntegral (TyCon _ (UnQual _ (Ident _ n)))
    = n `elem` ["Word8","Word16","Word32","Word64"]

--isFromIntegral' :: [Type ()] -> Bool
--isFromIntegral' ts = foldl isFromIntegral ts

checkTy :: String -> [String] -> Bool
checkTy n xs = n `elem` xs

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

{-
getAllTypeNames :: HsEmbedLayout -> [(String,String)] -> [(String, String)]
getAllTypeNames tyL acc
    = let hsTy = tyL ^. hsTyp
          ty = tyL ^. grTag
          fld = tyL ^. fieldMap
        in concatMap (\(k,f) -> case f of
            Left _ -> acc
            Right next -> case ty of
                               HsPrim -> acc++tyName hsTy
                               HsRecord -> getAllTypeNames next acc++tyName hsTy
                               HsVariant -> getAllTypeNames next acc++tyName hsTy
                               _ -> getAllTypeNames next acc
                where tyName hsTy = map (\x -> case x of
                                                 (TyCon _ (UnQual _ (Ident _ n))) -> [(k,n)]
                                                 _ -> []
                                                 ) P.tail $ unfoldAppCon hsTy
        ) $ M.toList fld
        -}

-- ----------------------------------------------------------------------------------------------------


