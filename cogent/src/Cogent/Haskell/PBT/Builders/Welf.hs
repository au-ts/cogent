{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}




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
import Cogent.Haskell.PBT.Util
import Cogent.Haskell.Shallow as SH
import Prelude as P
import Data.Tuple
import Data.Function
import Data.Maybe
import Data.Either
import Data.List (find, partition, group, sort, sortOn)
import Data.List.Extra (trim)
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
            userMapOpExp = findKIdentExp Welf Ic $ stmt ^. decls
        (icT, genfExp) <- mkGenFExp (stmt ^. funcname) defs predExp userMapOpExp
        let fnName = "gen_" ++ stmt ^. funcname
            genCon = TyCon () (mkQName "Gen")
            tyOut = TyApp () genCon $ TyParen () icT
            sig    = TypeSig () [mkName fnName] tyOut
            -- TODO: better gen_* body
            --       - what else do you need for arbitrary?
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ genfExp) Nothing]
            -- TODO: this is a dummy HS spec function def -> replace with something better
            -- hs_dec    = FunBind () [Match () (mkName $ "hs_"++(stmt ^. funcname)) [] (UnGuardedRhs () $
              --              function "undefined") Nothing]
          in return [sig, dec]

-- gen function only has output type (wrapped in Gen monad)
mkGenFExp :: String -> [CC.Definition TypedExpr VarName b] -> Maybe (Exp ()) -> (Maybe (Exp ()), Maybe (Exp ())) -> SG (Type (), Exp ())
mkGenFExp fname defs predE userE = do
    let def = fromMaybe (__impossible "function name (of function under test) cannot be found in cogent program"
              ) $ find (\x -> CC.getDefinitionId x == fname) defs
    mkGenFExp' def predE userE

mkGenFExp' :: CC.Definition TypedExpr VarName b -> Maybe (Exp ()) -> (Maybe (Exp ()), Maybe (Exp ())) -> SG (Type (), Exp ())
mkGenFExp' def predE userE | (CC.FunDef _ fn ps _ ti to _) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (genfExp) <- mkGenFBody ti ti' predE userE
    pure (ti', genfExp)
mkGenFExp' def predE userE | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (genfExp) <- mkGenFBody ti ti' predE userE
    pure (ti', genfExp)
mkGenFExp' def _ _ | (CC.TypeDef tn _ _) <- def = pure (TyCon () (mkQName "Unknown"), function "undefined")

mkGenFBody :: CC.Type t a -> Type () -> Maybe (Exp ()) -> (Maybe (Exp ()), Maybe (Exp ())) -> SG (Exp ())
mkGenFBody cogIcTyp icTyp predExp (userLhsE, userRhsE) = 
    let icLayout = determineUnpack cogIcTyp icTyp Unknown 0 "None"
        userPred = case predExp of 
                     -- here we turn the user predicate for welf into a lambda function 
                     -- with infix views replaced with vars that are bound to arbitrary
                     Just x -> let vars = scanUserInfixE x 0
                                 in mkVarToExpWithLam (replaceVarsInUserInfixE x 0 vars) vars
                     Nothing -> M.empty
        userMapOp = case userLhsE of 
                        Just lhs -> case userRhsE of 
                            Just rhs -> let vars = scanUserInfixE lhs 0
                                            lhs' = replaceVarsInUserInfixE lhs 0 vars
                                          in M.fromList $ map (\(k,v) -> (k,(lhs', rhs))) $ M.toList vars
                            Nothing -> M.empty
                        Nothing -> M.empty
        genStmts = mkArbitraryGenStmt icLayout Unknown userPred
        bindsMap = (map fst genStmts)
        binds' = map (\(x,y) -> case M.lookup x userMapOp of 
                                  Just (lhs, rhs) -> ( x
                                                     , genStmt (pvar (mkName x)) rhs )
                                  Nothing -> (x,y)) bindsMap
        binds = (map snd binds') 
        -- TODO: find matching var user is refering to and drop that in
        body = packConWithLayout (Right icLayout) Nothing
      in return $ doE $ binds ++ [qualStmt (app (function "return") body)]


-- | builder for map of vars to lambda expressions
-- -----------------------------------------------------------------------
mkVarToExpWithLam :: Exp () -> M.Map String String -> M.Map String (Exp ())
mkVarToExpWithLam e vars = M.fromList $ map (\(k,v) -> (k, lamE [pvar (mkName "x")] (replaceWithX e 0 k))) $ M.toList vars

-- | builder for arbitrary stmts used in the do expression of the Gen function
-- -----------------------------------------------------------------------
mkArbitraryGenStmt :: HsEmbedLayout -> GroupTag -> M.Map String (Exp ()) -> [((String, Stmt ()), (Type (), GroupTag))]
mkArbitraryGenStmt layout prevGroup userPredMap
    = let hsTy = layout ^. hsTyp
          group = layout ^. grTag
          prevGroup = layout ^. prevGrTag
          fld = layout ^. fieldMap
          fs = sortOn fst $ M.toList fld
          (preds, nextPreds) = partition (\(k,v) -> isJust $ (M.lookup k fld)) 
                                           (sortOn fst $ M.toList userPredMap)
          genFn = function "chooseAny"
          predFilter = op $ mkName "suchThat"
       in reverse $ (concatMap (\(k,v) -> case v of
           (Left depth) -> [ ( let n = k ++ replicate depth (P.head "'")
                                   e = fromMaybe (genFn) $ 
                                         (M.lookup n userPredMap) <&> (\x -> infixApp genFn predFilter x)
                                 in ( n, genStmt (pvar (mkName n)) e )
                             , (hsTy, prevGroup) ) ]
           (Right next) -> mkArbitraryGenStmt next group (M.fromList $ preds++(
                    if P.length nextPreds /= 0 then [P.head nextPreds] else [])
                )
       ) fs)

-- | builder for Constructor packing with just structure layout type
-- -----------------------------------------------------------------------
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

-- | Replace lens/prisms ((^.)|(^?)) nodes in the Exp AST with vars
-- | that are bound such that the expression is semantically equivalent
-- -----------------------------------------------------------------------
replaceVarsInUserInfixE :: Exp () -> Int -> M.Map String String -> Exp ()
replaceVarsInUserInfixE (Paren () e) depth vars = replaceVarsInUserInfixE e depth vars
replaceVarsInUserInfixE exp depth vars
    | (InfixApp () lhs op rhs) <- exp 
    = let opname = getOpStr op
        in if | any (==opname) ["^.", "^?"] -> replaceInfixViewE exp depth vars
              | otherwise -> InfixApp () (replaceVarsInUserInfixE lhs depth vars) op (replaceVarsInUserInfixE rhs depth vars)
replaceVarsInUserInfixE exp depth vars = exp

-- | Actual transform of AST (lens/prisms -> var) occurs here
-- -----------------------------------------------------------------------
replaceInfixViewE :: Exp () -> Int -> M.Map String String -> Exp ()
replaceInfixViewE (Paren () e) depth vars = Paren () $ replaceInfixViewE e depth vars
replaceInfixViewE (InfixApp () lhs op rhs) depth vars 
    --   ok just to handle rhs because of fixity
    = replaceInfixViewE rhs (depth+1) vars
replaceInfixViewE (Var _ (UnQual _ (Ident _ name))) depth vars
    -- TODO: how to handle multiple
    = let (newName, _) = P.head $ filter (\(k,v) -> v == name) $ M.toList vars
        in Var () (UnQual () (Ident () newName))
replaceInfixViewE exp depth vars = exp

-- | Transform Exp AST by changing @var@ name to just "x" (for anon functions)
-- -----------------------------------------------------------------------
replaceWithX :: Exp () -> Int -> String -> Exp ()
replaceWithX (Paren () e) depth var
    = Paren () $ replaceWithX e depth var
replaceWithX (InfixApp () lhs op rhs) depth var
    --   ok just to handle rhs because of fixity
    = InfixApp () (replaceWithX lhs (depth+1) var) op (replaceWithX rhs (depth+1) var)
replaceWithX exp depth var | (Var _ (UnQual _ (Ident _ name))) <- exp
    -- TODO: how to handle multiple
    = if (name == var) then Var () (UnQual () (Ident () ("x"))) else exp
replaceWithX exp depth vars = exp

-- | scan user infix expression -> looking for lens/prisms in exp,
-- | and use the structure of the lens/prism to create the unique identifier var
-- | and place it in a map.
-- | We know it will produce the same var as if the type was scanned with 
-- | HsEmbedLayout type. 
-- -----------------------------------------------------------------------
scanUserInfixE :: Exp () -> Int -> M.Map String String
scanUserInfixE (Paren () e) depth = scanUserInfixViewE e depth
scanUserInfixE exp depth 
    | (InfixApp () lhs op rhs) <- exp 
    = let opname = getOpStr op
        in if | any (==opname) ["^.", "^?"] -> scanUserInfixViewE exp depth
              | otherwise -> M.union (scanUserInfixE lhs depth) (scanUserInfixE rhs depth)
scanUserInfixE exp depth =  scanUserInfixViewE exp depth

-- | scan (^.|^?) expressions 
-- | want to extract fieldname & depth as this is enought to build the 
-- | fieldname pattern for view binds i.e. name ++ replicate depth $ P.head "'"
-- | in the map, fieldname ++ postfix maps to depth in expression
-- | depth only increases when recursing down RHS
-- -----------------------------------------------------------------------
scanUserInfixViewE :: Exp () -> Int -> M.Map String String
scanUserInfixViewE (Paren () e) depth = scanUserInfixViewE e depth
scanUserInfixViewE (InfixApp () lhs op rhs) depth 
    = if getOpStr op == "." 
       then M.union (scanUserInfixViewE lhs (depth)) (scanUserInfixViewE rhs (depth+1))
       else M.union (scanUserInfixViewE lhs (depth)) (scanUserInfixViewE rhs (depth))
scanUserInfixViewE (Var _ (UnQual _ (Ident _ name))) depth 
    = if (any (==trim name ) ["ic","ia","oc","oa"]) then M.empty
      else M.singleton (mkViewBindVarN name (depth+1)) (name)
scanUserInfixViewE _ depth = M.empty

-- | Builder for unique var identifier - this pattern is also follow by HsEmbedLayout
-- -----------------------------------------------------------------------
mkViewBindVarN :: String -> Int -> String
mkViewBindVarN fieldname depth = fieldname ++ (replicate depth $ P.head "'")

-- | Return operator string value
-- -----------------------------------------------------------------------
getOpStr :: QOp () -> String
getOpStr (QVarOp _ (UnQual _ (Symbol _ name))) = name
getOpStr _ = ""

testScanUserInfix :: IO ()
testScanUserInfix = do
    putStrLn $ show $ scanUserInfixE exampleUserInfix''' 0
    putStrLn $ show $ replaceVarsInUserInfixE exampleUserInfix''' 0 $ scanUserInfixE exampleUserInfix''' 0

exampleUserInfix''' = (InfixApp
                  ()
                    (InfixApp
                    ()
                      (Var
                      () (UnQual () (Ident () "ia")))
                      (QVarOp
                      () (UnQual () (Symbol () "^.")))
                      (Var
                      () (UnQual () (Ident () "_1"))))
                    (QVarOp
                    () (UnQual () (Ident () "div")))
                    (InfixApp
                    ()
                      (Var
                      () (UnQual () (Ident () "ia")))
                      (QVarOp
                      () (UnQual () (Symbol () "^.")))
                      (Var
                      ()
                        (UnQual () (Ident () "_2")))))
