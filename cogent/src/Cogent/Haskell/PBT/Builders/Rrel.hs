{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE PatternGuards #-}


-- | Haskell PBT generator
--
-- Generates Hs functions which are used in Property-Based Testing

module Cogent.Haskell.PBT.Builders.Rrel (
    rrelDecl
  , determineUnpack'
) where

import Cogent.Haskell.PBT.Builders.Absf

import Cogent.Isabelle.ShallowTable (TypeStr(..), st)
import qualified Cogent.Core as CC
import Cogent.Core (TypedExpr(..))
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Haskell.HscGen
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
import Cogent.Haskell.PBT.Util
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


-- | Top level Builder for Refinement Relation
-- -----------------------------------------------------------------------
rrelDecl :: PbtDescStmt -> (Module (), Hsc.HscModule) -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
rrelDecl stmt (ffiDefs, ffiTypes) defs = do
        let (oaTy, _) = findKIdentTyExp Rrel Oa $ stmt ^. decls
            isPure = checkBoolE Pure $ stmt ^. decls
            fnName = "rel_" ++ stmt ^. funcname
            oaT = case oaTy of
                      Just x -> x
                      Nothing -> fromMaybe (__impossible "no oa type given in PBT file") $ 
                                    (findKIdentTyExp Spec Oa $ stmt ^. decls) ^. _1
            (_, userE) = findKIdentTyExp Rrel Pred $ stmt ^. decls
        (ocT, _, rrelE, conNames) <- mkRrelExp (stmt ^. funcname) oaT defs userE 
            -- TODO: Pass this down
            -- $ if isPure then Nothing else Just $ (ffiDefs, ffiTypes)
        let to     = mkTyConT $ mkName "Bool"
            -- TODO: replace oc with C types if not pure
            ti     = TyFun () oaT $ TyFun () ocT to
            sig    = TypeSig () [mkName fnName] ti
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "oa", pvar $ mkName "oc"] (UnGuardedRhs () rrelE) Nothing]
        return $ map mkLens (takeWhile (`notElem` hsSumTypes) conNames)++[sig, dec]

-- | Builder for Refinement Relation body expression, also returns function input/output type
-- -----------------------------------------------------------------------
mkRrelExp :: String 
          -> Type () 
          -> [CC.Definition TypedExpr VarName b] 
          -> Maybe (Exp ()) 
          -> SG (Type (), Type (), Exp (), [String])
mkRrelExp fname oaTyp defs userE = do
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (ocT, oaT, rrelE, conNames) <- mkRrelExp' def oaTyp userE
    pure (ocT, oaT, rrelE, conNames)

mkRrelExp' :: CC.Definition TypedExpr VarName b -> Type () -> Maybe (Exp ()) -> SG (Type (), Type (), Exp (), [String])
mkRrelExp' def oaT userE | (CC.FunDef _ fn ps _ ti to _) <- def
    = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
        to' <- shallowType to
        (rrel, conNames) <- mkRrelBody to to' oaT userE
        pure (to', oaT, rrel, conNames)
mkRrelExp' def oaT userE | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    to' <- shallowType to
    (absE, conNames) <- mkRrelBody to to' oaT userE
    pure ( to', oaT, absE, conNames)
mkRrelExp' def oaT _ | (CC.TypeDef tn _ _) <- def
    = pure (TyCon () (mkQName "Unknown"), oaT, function "undefined", [])

-- | Builder for refinement relation body. For pointwise equality (default), builds a 
-- | let expression which binds lens views to variables that and then compared with
-- | equality in a && chain.
-- -----------------------------------------------------------------------
-- | @cogOcTyp@ is the cogent type of the concrete output
-- | @ocTyp@ is the Haskell type of the concrete output
-- | @oaTyp@ is the Haskell type of the abstract output
mkRrelBody :: CC.Type t a -> Type () -> Type () -> Maybe (Exp ()) -> SG (Exp (), [String])
mkRrelBody cogOcTyp ocTyp oaTyp userE
    = let ocLy = determineUnpack cogOcTyp ocTyp Unknown 0 "1"
          oaLy = determineUnpack' oaTyp Unknown 0 "1"
          ocLens' = trace (show ocLy) $ mkLensView ocLy "oc" Unknown Nothing
          oaLens' = trace (show oaLy) $ mkLensView oaLy "oa" Unknown Nothing
          ocLens = map fst ocLens'
          oaLens = map fst oaLens'
          ls = oaLens ++ ocLens
          cNames = getConNames ocLy [] ++ getConNames oaLy []
          binds = map ((\x -> pvar . mkName . fst $ x) &&& snd) ls
          tys = map snd ocLens'
          ocVars = map fst ocLens
          oaVars = map fst oaLens
          body = fromMaybe (mkCmpExp (zip3 oaVars ocVars tys) Nothing) userE
       in pure (mkLetE binds body, cNames)

-- | Builder for comparison expression used in refinement relation
-- -----------------------------------------------------------------------
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
        in mkInfixEq (mkVar oa) (mkVar oc)

        -- now done in lens view itself
--        if isFromIntegral ty
--            then mkInfixEq (mkVar oa) $ paren $ infixApp (mkVar oc) (mkOp op) (function "fromIntegral")
--            else 

