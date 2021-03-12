{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}




-- | Haskell PBT generator
--
-- Generates Hs functions which are used in Property-Based Testing

module Cogent.Haskell.PBT.Builders.Welf (
    genDecls''
) where

import Cogent.Haskell.PBT.Builders.Absf
import Cogent.Haskell.PBT.Builders.Rrel

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
import Cogent.Haskell.PBT.Types
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

-- | top level builder for gen_* :: Gen function 
-- -----------------------------------------------------------------------
genDecls'' :: PbtDescStmt -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
genDecls'' stmt defs = do
        let (_, _, predExp) = findKvarsInDecl Welf Pred $ stmt ^. decls
        (icT, genfExp) <- mkGenFExp (stmt ^. funcname) defs predExp
        let fnName = "gen_" ++ stmt ^. funcname
            genCon = TyCon () (mkQName "Gen")
            tyOut = TyApp () genCon $ TyParen () icT
            sig    = TypeSig () [mkName fnName] tyOut
            -- TODO: better gen_* body
            --       - what else do you need for arbitrary?
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ genfExp) Nothing]
            -- TODO: this is a dummy HS spec function def -> replace with something better
            hs_dec    = FunBind () [Match () (mkName $ "hs_"++(stmt ^. funcname)) [] (UnGuardedRhs () $
                           function "undefined") Nothing]
          in return [sig, dec, hs_dec]

-- gen function only has output type (wrapped in Gen monad)
mkGenFExp :: String -> [CC.Definition TypedExpr VarName b] -> Maybe (Exp ()) -> SG (Type (), Exp ())
mkGenFExp fname defs predE = do
    let def = fromMaybe (__impossible "function name (of function under test) cannot be found in cogent program"
              ) $ find (\x -> CC.getDefinitionId x == fname) defs
    mkGenFExp' def predE

mkGenFExp' :: CC.Definition TypedExpr VarName b -> Maybe (Exp ()) -> SG (Type (), Exp ())
mkGenFExp' def predE | (CC.FunDef _ fn ps _ ti to _) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (genfExp) <- mkGenFBody ti ti' predE
    pure (ti', genfExp)
mkGenFExp' def predE | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (genfExp) <- mkGenFBody ti ti' predE
    pure (ti', genfExp)
mkGenFExp' def _ | (CC.TypeDef tn _ _) <- def = pure (TyCon () (mkQName "Unknown"), function "undefined")

mkGenFBody :: CC.Type t a -> Type () -> Maybe (Exp ()) -> SG (Exp ())
mkGenFBody cogIcTyp icTyp predExp = 
    let icLayout = determineUnpack cogIcTyp icTyp Unknown 0 "None"
        genStmts = mkArbitraryGenStmt icLayout Unknown
        binds = map (snd . fst) genStmts
        body = packConWithLayout (Right icLayout) Nothing
        -- packAbsCon icTyp (map (fst . fst) genStmts) 0
      in return $ doE $ binds ++ [qualStmt (app (function "return") body)]


-- TODO: will need to match user built lens with generated lens

{-

          e = case predExp of 
                      Just x -> infixApp genfn predOp $ predFunc x
                      Nothing -> genfn
        in pure (e, [])
        where genfn = function "arbitrary" -- "arbitrary"
              predOp = op $ mkName "suchThat"
              predFunc x = lamE [pvar $ mkName "ic"] x
              -}

{-
          lens = map fst $ mkLensView icLayout "ic" Unknown Nothing
          binds = map ((\x -> pvar . mkName . fst $ x) &&& snd) lens
          body = packAbsCon iaTyp (map fst lens) 0
       in pure (mkLetE binds body, getConNames icLayout [])
       -}



mkArbitraryGenStmt :: HsEmbedLayout -> GroupTag -> [((String, Stmt ()), (Type (), GroupTag))]
mkArbitraryGenStmt layout prevGroup
    = let hsTy = layout ^. hsTyp
          group = layout ^. grTag
          prevGroup = layout ^. prevGrTag
          fld = layout ^. fieldMap
       in concatMap ( \(k, v) -> case group of
            HsPrim -> case v of
               (Left depth) -> [ ( let n = k ++ replicate depth (P.head "'")
                                     in ( n
                                        , genStmt (pvar (mkName n)) $ function "arbitrary" )
                                 , (hsTy, prevGroup) )
                               ]
               (Right next) -> __impossible $ show k ++ " " ++ show v
            _ -> case v of
               (Left depth) -> __impossible $ show k ++ " " ++ show v
               (Right next) -> mkArbitraryGenStmt next group -- $ Just $ mkViewInfixE varToView group prev k
       ) $ M.toList fld


packConWithLayout :: Either Int HsEmbedLayout -> Maybe String -> Exp ()
packConWithLayout layout fieldKey
    = case layout of 
    Left depth -> var $ mkName $ (fromMaybe (__impossible "no field key!") fieldKey) ++ replicate depth (P.head "'")
    Right nextLayout -> let hsTy = nextLayout ^. hsTyp
                            group = nextLayout ^. grTag
                            prevGroup = nextLayout ^. prevGrTag
                            fld = nextLayout ^. fieldMap 
                          in case group of
        HsPrim -> let (k,v) = P.head $ M.toList fld
                    in packConWithLayout v (Just k)
        HsList -> __impossible "should not be a list"
        Unknown -> __impossible "unknown type found!"
        HsTuple -> tuple $ map (\(k,v) -> packConWithLayout v (Just k)) $ M.toList fld 
        _ -> let (name, flds) = let (conHead:conParams) = unfoldAppCon hsTy
                                               in ( case conHead of
                                                          (TyCon _ (UnQual _ (Ident _ n))) -> n
                                                          _ -> "Unknown"
                                                  , M.toList fld )
                      in appFun (mkVar name) $ map (\(k,v) -> packConWithLayout v (Just k)) $ flds



-- TODO: 
--      - want to scan user exp and get field name ++ depth
--          - might be useful for shorthand direct mappings (e.g. count'') -> leverage the algorithm
--          - assume only infix exp in which we transverse down rhs until we reach the last field
--      - then look at user predicate -> want to just replace lens view with just fieldname ++depth tag


{-
-- scan user predicate -> must be infix -> must have lens view as base of expression
scanUserInfixExp :: Exp () -> Maybe (Exp ()) -> (String, Exp ())
scanUserInfixExp (InfixApp () lhs op rhs) prev 
    = case op of 
        (QVarOp () (UnQual () (Symbol () symStr)))
            -> if | symStr /= "^." -> 
                  | otherwise -> (
                  -}


-- scan (^.) expressions -> always follow rhs b/c we want to extract the
-- fields names and discover the depth of it in the layout of the type
-- i.e. name ++ replicate depth $ P.head "'"
{-
scanUserInfixView :: Exp () -> Int -> [String]
scanUserInfixView (Paren () e) depth = scanUserInfixView e 
scanUserInfixView (InfixApp () _ op rhs) depth 
    = case op of 
        (QVarOp () (UnQual () (Symbol () symStr)))
            -> if | symStr == "^." -> scanUserInfixView rhs (depth+1)
                  | symStr == "." -> scanUserInfixView rhs (depth+1)
                  | otherwise -> scanUserInfixView rhs (depth+1)
                  -}


{-

-- this needs to take a predicate and turn it into a generator
-- this is naive method so far
-- TODO: advanced method
--  -> convert predicate into functions, this is refinement in a way
--  -> see figuring out
mkGenBody :: Type () -> Maybe (Exp ()) -> Exp ()
mkGenBody icTyp predExp = case predExp of 
                      Just x -> infixApp genfn predOp $ predFunc x
                      Nothing -> genfn
    where genfn = function "arbitrary" -- "arbitrary"
          predOp = op $ mkName "suchThat"
          predFunc x = lamE [pvar $ mkName "ic"] x
          -}





{-
getCogFunInputTyp :: String -> [CC.Definition TypedExpr VarName b] -> SG (CC.Type t b, Type ())
getCogFunInputTyp funcname defs =
    let fnDef = fromJust $ find (\x -> CC.getDefinitionId x == funcname) defs
      in getCogFunInputTyp' fnDef

getCogFunInputTyp' :: CC.Definition TypedExpr VarName b -> SG (CC.Type t b, Type ())
getCogFunInputTyp' (CC.FunDef _ fn ps _ ti to _) = do
    s <- shallowType ti
    let ti' = ti
    return $ (ti', s)
getCogFunInputTyp' (CC.AbsDecl _ fn ps _ ti to) = do
    s <- shallowType ti
    let ti' = ti
    return $ (ti', s)
getCogFunInputTyp' _ = __impossible "could not get input type"

-}
