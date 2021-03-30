{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}


-- | Abstraction Function Builder
-- ----------------------------------------------------------------

module Cogent.Haskell.PBT.Builders.Absf

-- (
   --  absFDecl

-- ) 
where

import Cogent.Haskell.PBT.Util
import qualified Cogent.Haskell.HscSyntax as Hsc

import Cogent.Isabelle.ShallowTable (TypeStr(..), st)
import qualified Cogent.Core as CC
import Cogent.Core (TypedExpr(..))
import Cogent.C.Syntax
import Cogent.Common.Syntax
import qualified Cogent.Haskell.HscGen as Hsc
import Cogent.Util ( concatMapM, Stage(..), delimiter, secondM, toHsTypeName, concatMapM, (<<+=) )
import Cogent.Compiler (__impossible)

import qualified Data.Map as M
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.SrcLoc
import Text.PrettyPrint
import Debug.Trace
import Cogent.Haskell.PBT.DSL.Types
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

-- | Top level Builder for Abstraction Function
-- -----------------------------------------------------------------------
absFDecl :: PbtDescStmt -> (Module (), Hsc.HscModule) -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
absFDecl stmt (ffiDefs, ffiTypes) defs = do
        let (iaTy, iaExp) = findKIdentTyExp Absf Ia $ stmt ^. decls
            isPure = checkBoolE Pure $ stmt ^. decls
            fnName = "abs_" ++ stmt ^. funcname
            iaT = case iaTy of
                      Just x -> x
                      Nothing -> fromMaybe (__impossible "not ia type given in PBT file") $ 
                                    (findKIdentTyExp Spec Ia $ stmt ^. decls) ^. _1
        (icT, _, absE, conNames) <- mkAbsFExp (stmt ^. funcname) iaT defs iaExp $ 
                if isPure then Nothing else Just $ (stmt ^. funcname, ffiDefs, ffiTypes)
        let ti     = if isPure then icT 
                     else (findHsFFIFunc ffiDefs (stmt ^. funcname)) ^. _2
            to     = if isPure then iaT
                     else TyApp () (TyCon () (mkQName "IO")) $ TyParen () $ iaT
            sig    = TypeSig () [mkName fnName] (TyFun () ti to)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "ic"] (UnGuardedRhs () absE) Nothing]
        return $ map mkLens (takeWhile (`notElem` hsSumTypes) conNames)++[sig, dec]


-- | Builder for abstraction function body expression, also returns function input/output type
-- -----------------------------------------------------------------------
-- | @fname@ is the name of the function
-- | @iaTyp@ is the abstract input type
-- | @defs@ is the list of Cogent definitions
mkAbsFExp :: String 
          -> Type () 
          -> [CC.Definition TypedExpr VarName b] 
          -> Maybe (Exp ()) 
          -> Maybe (String, Module (), Hsc.HscModule)
          -> SG (Type (), Type (), Exp (), [String])
mkAbsFExp fname iaTyp defs userE ffimods = do
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (icT, iaT, absE, conNames) <- mkAbsFExp' def iaTyp userE ffimods
    pure (icT, iaT, absE, conNames)

mkAbsFExp' :: CC.Definition TypedExpr VarName b 
           -> Type () 
           -> Maybe (Exp ()) 
           -> Maybe (String, Module (), Hsc.HscModule)
           -> SG (Type (), Type (), Exp (), [String])
mkAbsFExp' def iaT userE ffimods | (CC.FunDef _ fn ps _ ti to _) <- def
    = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
        ti' <- shallowType ti
        (absE, conNames) <- mkAbsFBody ti ti' iaT userE ffimods
        pure (ti', iaT, absE, conNames)
mkAbsFExp' def iaT userE ffimods | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (absE, conNames) <- mkAbsFBody ti ti' iaT userE ffimods
    pure ( ti', iaT, absE, conNames)
mkAbsFExp' def iaT _ _ | (CC.TypeDef tn _ _) <- def
    = pure (TyCon () (mkQName "Unknown"), iaT, function "undefined", [])

-- | Builder for abstraction function body. For direct abstraction (default), builds a 
-- | let expression which binds lens views to variables that and then used 
-- | to pack the outgoing Constructor
-- -----------------------------------------------------------------------
-- | @cogIcTyp@ is the cogent type of the concrete input
-- | @icTyp@ is the Haskell type of the concrete input
-- | @iaTyp@ is the Haskell type of the abstract input (what we are trying to abstract to)
mkAbsFBody :: CC.Type t a 
           -> Type () 
           -> Type () 
           -> Maybe (Exp ()) 
           -> Maybe (String, Module (), Hsc.HscModule)
           -> SG (Exp (), [String])
mkAbsFBody cogIcTyp icTyp iaTyp userIaExp ffimods
    = let icLayout =  determineUnpack cogIcTyp icTyp Unknown 0 "1"
          ic = if isNothing ffimods then "ic" else "ic"
          icCTyLy = ffimods <&>
               (\x -> let (_, ti, _) = findHsFFIFunc (x ^. _2) (x ^. _1) 
                        in determineUnpackFFI icLayout ic "None" "None" 0 ti (x ^. _3) )
          lens = map fst $ fromMaybe (mkLensView icLayout ic Unknown Nothing) $ 
                                icCTyLy <&> (\x -> mkLensView' x "ic" Unknown "unknown" Nothing)
          binds = map ((\x -> pvar . mkName . fst $ x) &&& snd) lens
          binds' = map (\(k, v) -> letStmt [nameBind (mkName k) v] ) $ lens
          peeks = fromMaybe [] $ icCTyLy <&> (\x -> mkPeekStmts x ic Nothing)
          body = fromMaybe (packAbsCon iaTyp (map fst lens) 0) $ userIaExp <&>
                                 (\x -> replaceVarsInUserInfixE x 0 $ scanUserInfixE x 0 "ic")
       in pure $ ( if isNothing ffimods then mkLetE binds body
                 -- TODO: prepend peek for each Ptr type
                 else doE ( (map snd peeks)++binds'++[qualStmt (app (function "return") body)])
               , (getConNames icLayout []) ++ 
                    (fromMaybe [] $ icCTyLy <&> (\x -> getConNames' x [])) )

-- | Builder for packing the constructor of the abstract type.
-- | Given the type of the constructor and a list of vars to put in the constructor,
-- | builds expression of constructor being packed by these vars
-- -----------------------------------------------------------------------
-- | @iaTyp@ is the Haskell type of the abstract input (concrete input is transformed to abstract input)
-- | @varsToPut@ is a list containing the names of the vars to be put in the constructor
-- | TODO: maybe unify the vars with the outgoing matching type
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
        
mkFromIntE :: Type () -> Exp () -> Exp ()
mkFromIntE ty prev =
    if isFromIntegral ty then infixApp prev (mkOp "$") (function "fromIntegral") else prev

isInt' :: QName () -> Bool
isInt' (UnQual _ (Ident _ n)) = checkTy n intPrims
isInt' _ = False

isInt :: Type () -> Bool
isInt (TyCon _ (UnQual _ (Ident _ n))) = checkTy n intPrims

isBool :: Type () -> Bool
isBool (TyCon _ (UnQual _ (Ident _ n))) = checkTy n ["Bool"]

boolResult :: Type () -> Bool
boolResult (TyCon _ (UnQual _ (Ident _ n))) = read n
boolResult _ = False

checkTy :: String -> [String] -> Bool
checkTy n xs = n `elem` xs

