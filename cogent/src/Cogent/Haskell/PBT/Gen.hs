{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}




-- | Haskell PBT generator
--
-- Generates Hs functions which are used in Property-Based Testing

module Cogent.Haskell.PBT.Gen (
  pbtHs
) where

import Cogent.Haskell.PBT.Builders.Absf
import Cogent.Haskell.PBT.Builders.Rrel
import Cogent.Haskell.PBT.Builders.Welf
import Cogent.Haskell.PBT.DSL.Types
import Cogent.Haskell.PBT.Util
import Cogent.Haskell.Shallow as SH
import qualified Cogent.Haskell.HscSyntax as Hsc

import Cogent.Isabelle.ShallowTable (TypeStr(..), st)
import qualified Cogent.Core as CC
import Cogent.Core (TypedExpr(..))
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Haskell.HscGen
import Cogent.Util ( concatMapM, Stage(..), delimiter, secondM, toHsTypeName, concatMapM, (<<+=) )
import Cogent.Compiler (__impossible)

import qualified Data.Map as M
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.SrcLoc
import Text.PrettyPrint
import Debug.Trace
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

pbtHs :: (String, String, String)   -- (HS PBT Module Name, HS Shallow Module Name, HS Shallow Module Name w/ Tuples)
      -> String         -- HS FFI Module Name 
      -> String         -- HSC FFI Module Name 
      -> [PbtDescStmt]  -- List of PBT info for the Cogent Functions
      -> [CC.Definition TypedExpr VarName b]     -- A list of Cogent definitions
      -- -> [CC.CoreConst TypedExpr]             -- A list of Cogent constants
      -> (Module (), Hsc.HscModule)              -- FFI HS module & FFI HSC module
      -> String         -- Log header 
      -> String
pbtHs names hsffiName hscffiName pbtinfos decls ffimods log = render $
  let mod = propModule names hsffiName hscffiName pbtinfos decls ffimods
    in text "{-" $+$ text log $+$ text "-}" $+$ prettyPrim mod

propModule :: (String, String, String) 
           -> String 
           -> String 
           -> [PbtDescStmt] 
           -> [CC.Definition TypedExpr VarName b] 
           -> (Module (), Hsc.HscModule) 
           -> Module ()
propModule (name, shallowName, shallowNameTup) hsffiName hscffiName pbtinfos cogentdecls ffimods =
  let (cogDecls, w) = evalRWS (runSG $ do
                                          shallowTypesFromTable
                                          genDs <- concatMapM (\x -> genDecls x ffimods cogentdecls) pbtinfos
                                          absDs <- concatMapM (\x -> absFDecl x ffimods cogentdecls) pbtinfos
                                          rrelDs <- concatMapM (\x -> rrelDecl x ffimods cogentdecls) pbtinfos
                                          return $ absDs ++ rrelDs ++ genDs  -- cs ++ ds
                              )
                              (ReaderGen (st cogentdecls) [] True [])
                              (StateGen 0 M.empty)
      isImpure = any (==False) $ map (\x -> checkBoolE Pure x) $ map (\x -> x ^. decls) $ pbtinfos
      moduleHead = ModuleHead () (ModuleName () name) Nothing Nothing
      exts = P.map (\s -> LanguagePragma () [Ident () s])
                   [ "DisambiguateRecordFields"
                   , "DuplicateRecordFields"
                   , "NamedFieldPuns"
                   , "MultiWayIf"
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
      import_ints = P.map importAbs ["Int8", "Int16", "Int32", "Int64"]
      import_prelude = P.map importVar ["not", "div", "mod", "fromIntegral", "undefined", "return", "fromEnum", "otherwise", "repeat"] ++
                       P.map importSym ["$", ".", "+", "-", "*", "^", "&&", "||", ">", ">=", "<", "<=", "==", "/="] ++
                       P.map importAbs ["Char", "String", "Int", "Integer", "Show", "Maybe", "IO"] ++
                       [IThingAll () $ Ident () "Bool"]
      import_ffiutil = P.map importVar ["new"]
      import_ffiunsafe = P.map importVar ["unsafeLocalState"] 
      import_ffistorable = P.map importVar ["peek"] 
      import_ffiarray = P.map importVar ["peekArray", "newArray", "pokeArray", "mallocArray"] 
      import_ffialloc = P.map importVar ["free"]
      imps = [ ImportDecl () (ModuleName () "Test.QuickCheck" ) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Test.QuickCheck.Monadic" ) False False False Nothing Nothing Nothing
              -- ImportDecl () (ModuleName () "Prelude") True False False Nothing (Just (ModuleName () "P")) Nothing

             --, ImportDecl () (ModuleName () "Data.Tree" ) False False False Nothing Nothing Nothing
             --, ImportDecl () (ModuleName () "Data.Word" ) False False False Nothing Nothing Nothing
             -- custom corres
             , ImportDecl () (ModuleName () "Corres" ) False False False Nothing Nothing Nothing
             -- TODO: does not set fields with underscore 
             -- , ImportDecl () (ModuleName () shallowName) False False False Nothing (Just $ ModuleName () "Sh") Nothing
             , ImportDecl () (ModuleName () shallowNameTup) False False False Nothing (Just $ ModuleName () "ShT") Nothing
             -- TODO: only import types that are being used in testing
             -- , ImportDecl () (ModuleName () hscffiName) False False False Nothing (Just $ ModuleName () "FFIT") Nothing
             , ImportDecl () (ModuleName () hsffiName) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () (hsffiName++"_Types")) False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Lens.Micro") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Lens.Micro.TH") False False False Nothing Nothing (Just $ ImportSpecList () False (map importVar ["makeLenses"]))
             , ImportDecl () (ModuleName () "Control.Lens.Combinators") False False False Nothing Nothing (Just $ ImportSpecList () False (map importVar ["makePrisms"]))
             -- , ImportDecl () (ModuleName () (hscname ++ "_Abs")) False False False Nothing (Just (ModuleName () "FFI")) Nothing
             , ImportDecl () (ModuleName () "Prelude"  ) False False False Nothing Nothing (Just $ ImportSpecList () False import_prelude)
             , ImportDecl () (ModuleName () "Data.Bits") False False False Nothing Nothing (Just $ ImportSpecList () False import_bits)
             , ImportDecl () (ModuleName () "Data.Int") False False False Nothing Nothing (Just $ ImportSpecList () False import_ints)
             , ImportDecl () (ModuleName () "Data.Maybe") False False False Nothing Nothing Nothing
             , ImportDecl () (ModuleName () "Data.Array.IArray") False False False Nothing Nothing Nothing
             -- , ImportDecl () (ModuleName () "Data.Tuple.Select") True False False Nothing (Just $ ModuleName () "Tup") Nothing
             -- , ImportDecl () (ModuleName () "Data.Tuple.Update") True False False Nothing (Just $ ModuleName () "Tup") Nothing
             , ImportDecl () (ModuleName () "Data.Word") False False False Nothing Nothing (Just $ ImportSpecList () False import_word)
             ] ++ if not isImpure then []
                  else [ ImportDecl () (ModuleName () "Foreign.Marshal.Utils") False False False Nothing Nothing 
                            (Just $ ImportSpecList () False import_ffiutil)
                       ,  ImportDecl () (ModuleName () "Foreign.Marshal.Unsafe") False False False Nothing Nothing 
                            (Just $ ImportSpecList () False import_ffiunsafe) 
                       ,  ImportDecl () (ModuleName () "Foreign.Storable") False False False Nothing Nothing 
                            (Just $ ImportSpecList () False import_ffistorable)
                       ,  ImportDecl () (ModuleName () "Foreign.Marshal.Array") False False False Nothing Nothing 
                            (Just $ ImportSpecList () False import_ffiarray)
                       ,  ImportDecl () (ModuleName () "Foreign.Marshal.Alloc") False False False Nothing Nothing 
                            (Just $ ImportSpecList () False import_ffialloc)
                       ,  ImportDecl () (ModuleName () "Foreign.C.Types") False False False Nothing Nothing Nothing
                       ,  ImportDecl () (ModuleName () "Foreign.Ptr") False False False Nothing Nothing Nothing ] 
            -- TODO: need to have a list of record names
      (ls, cogD) = partition (\x -> case x of
                                      (SpliceDecl _ _) -> True
                                      _ -> False) cogDecls
      hs_decls = rmdups ls ++ (P.concatMap propDecls pbtinfos) 
                    ++ (P.concatMap specDecls pbtinfos) ++ cogD
                    ++ mkQCAll
                                -- ++ (P.concatMap (\x -> genDecls x decls) pbtinfos)
  in
  Module () (Just moduleHead) exts imps hs_decls

-- | top level builder for prop_* :: Property function 
-- -----------------------------------------------------------------------
propDecls :: PbtDescStmt -> [Decl ()]
propDecls desc
    = let fn    = desc ^. funcname
          ds    = mkPropBody fn $ desc ^. decls
          fnName = "prop_" ++ fn
          toName = "Property"
          to     = TyCon   () (mkQName toName)
          sig    = TypeSig () [mkName fnName] to
          dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () ds ) Nothing]
        in [sig, dec]

mkQCAll :: [Decl ()]
mkQCAll = let thReturn = SpliceDecl () $ app (function "return") eList
              qcAllE = function "$quickCheckAll"
            in [ thReturn
               , FunBind () [Match () (mkName "main") [] (UnGuardedRhs () qcAllE ) Nothing] ]

-- | builder for function body of prop_* :: Property
-- -----------------------------------------------------------------------
mkPropBody :: String -> [PbtDescDecl] -> Exp ()
mkPropBody n ds
    = let isPure = checkBoolE Pure ds
          isNond = checkBoolE Nond ds
          oc = app (function $ if isPure then n else "cogent_"++n) (var $ mkName "ic")
          ia = app (function $ "abs_"++n) (var $ mkName "ic")
          oa = app (function $ "hs_"++n)  (var . mkName $ "ia")
          binds = [ FunBind () [Match () (mkName "oc") [] (UnGuardedRhs () oc  ) Nothing]
                  , FunBind () [Match () (mkName "oa") [] (UnGuardedRhs () oa  ) Nothing] ]
          binds' =  [ genStmt (pvar $ mkName "oc") oc
                    , genStmt (pvar $ mkName "ia") ia
                    , genStmt (pvar $ mkName "oa") (app (function "return") oa)
                    , qualStmt body ]
          body  = appFun (function $ (if isPure then "corres" else "corresM")++(if isNond then "" else "'"))
                         [ function $ "rel_"++n , var $ mkName "oa" , var $ mkName "oc" ]
          f  = if isPure then function "forAll" else function "forAllM"
          fs = [ function $ "gen_"++n
               , lamE [pvar $ mkName "ic"] (if isPure then letE binds body else app (function "run") (doE binds')) ]
        in if isPure then appFun f fs
           else app (function "monadicIO") $ appFun f fs


-- | builder for haskell specification function
-- -----------------------------------------------------------------------
specDecls :: PbtDescStmt -> [Decl ()]
specDecls desc 
    = let iaTy = (findKIdentTyExp Spec Ia $ desc ^. decls) ^. _1
          (oaTy, exp) = findKIdentTyExp Spec Oa $ desc ^. decls
          iaT = fromMaybe ( fromMaybe (__impossible "ia type not specified!") $
                    (findKIdentTyExp Absf Ia $ desc ^. decls) ^. _1
                ) iaTy
          oaT = fromMaybe ( fromMaybe (__impossible "oa type not specified!") $
                    (findKIdentTyExp Rrel Oa $ desc ^. decls) ^. _1
                ) oaTy
          e = specExpr iaT oaT exp
          fname = mkName $ "hs_"++(desc ^. funcname)
          sig  = TypeSig () [fname] (TyFun () iaT oaT)
          dec = FunBind () [Match () fname [(pvar . mkName) "ia"] (UnGuardedRhs () $ e) Nothing]
        in [sig, dec]

specExpr :: Type () -> Type () -> Maybe (Exp ()) -> Exp ()
specExpr iaTyp oaTyp userE
    = let iaLy = determineUnpack' iaTyp Unknown 0 "None"
          -- oaLy = determineUnpack' oaTyp Unknown 0 "None"
          iaLens' = mkLensView iaLy "ia" Unknown Nothing
          -- oaLens' = mkLensView oaLy "oa" Unknown Nothing
          iaLens = map fst iaLens'
          -- oaLens = map fst oaLens'
          ls = iaLens --oaLens ++
          cNames = getConNames iaLy [] -- ++ getConNames oaLy []
          binds = map ((\x -> pvar . mkName . fst $ x) &&& snd) ls
          tys = map snd iaLens'
          iaVars = map fst iaLens
          -- oaVars = map fst oaLens
          body = fromMaybe (function "undefined") userE
       in mkLetE binds body
