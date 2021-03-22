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
import Cogent.Isabelle.Shallow (isRecTuple)

-- | Top level Builder for Abstraction Function
-- -----------------------------------------------------------------------
absFDecl :: PbtDescStmt -> (Module (), Hsc.HscModule) -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
absFDecl stmt ffimods defs = do
        let (iaTy, iaExp) = findKIdentTyExp Absf Ia $ stmt ^. decls
            fnName = "abs_" ++ stmt ^. funcname
            iaT = case iaTy of
                      Just x -> x
                      Nothing -> fromMaybe (__impossible "not ia type given in PBT file") $ 
                                    (findKIdentTyExp Spec Ia $ stmt ^. decls) ^. _1
        (icT, _, absE, conNames) <- mkAbsFExp (stmt ^. funcname) iaT defs iaExp
        let ti     = icT
            to     = iaT
            sig    = TypeSig () [mkName fnName] (TyFun () ti to)
            dec    = FunBind () [Match () (mkName fnName) [pvar $ mkName "ic"] (UnGuardedRhs () absE) Nothing]
        return $ map mkLens (takeWhile (`notElem` hsSumTypes) conNames)++[sig, dec]

mkLens :: String -> Decl ()
mkLens t
    = let fname = if | P.head t == 'R' -> "makeLenses"
                     | P.head t == 'V' -> "makePrisms"
                     | otherwise -> "undefined"
       in SpliceDecl () $ app (function fname) (TypQuote () (UnQual () (mkName t)))

-- | Builder for abstraction function body expression, also returns function input/output type
-- -----------------------------------------------------------------------
-- | @fname@ is the name of the function
-- | @iaTyp@ is the abstract input type
-- | @defs@ is the list of Cogent definitions
mkAbsFExp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> Maybe (Exp ()) -> SG (Type (), Type (), Exp (), [String])
mkAbsFExp fname iaTyp defs userE = do
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (icT, iaT, absE, conNames) <- mkAbsFExp' def iaTyp userE
    pure (icT, iaT, absE, conNames)

mkAbsFExp' :: CC.Definition TypedExpr VarName b -> Type () -> Maybe (Exp ()) -> SG (Type (), Type (), Exp (), [String])
mkAbsFExp' def iaT userE | (CC.FunDef _ fn ps _ ti to _) <- def
    = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
        ti' <- shallowType ti
        (absE, conNames) <- mkAbsFBody ti ti' iaT userE
        pure (ti', iaT, absE, conNames)
mkAbsFExp' def iaT userE | (CC.AbsDecl _ fn ps _ ti to) <- def = local (typarUpd (map fst $ Vec.cvtToList ps)) $ do
    ti' <- shallowType ti
    (absE, conNames) <- mkAbsFBody ti ti' iaT userE
    pure ( ti', iaT, absE, conNames)
mkAbsFExp' def iaT _ | (CC.TypeDef tn _ _) <- def
    = pure (TyCon () (mkQName "Unknown"), iaT, function "undefined", [])

-- | Builder for abstraction function body. For direct abstraction (default), builds a 
-- | let expression which binds lens views to variables that and then used 
-- | to pack the outgoing Constructor
-- -----------------------------------------------------------------------
-- | @cogIcTyp@ is the cogent type of the concrete input
-- | @icTyp@ is the Haskell type of the concrete input
-- | @iaTyp@ is the Haskell type of the abstract input (what we are trying to abstract to)
mkAbsFBody :: CC.Type t a -> Type () -> Type () -> Maybe (Exp ()) -> SG (Exp (), [String])
mkAbsFBody cogIcTyp icTyp iaTyp userIaExp
    = let icLayout =  determineUnpack cogIcTyp icTyp Unknown 0 "1"
          lens =  map fst $ mkLensView icLayout "ic" Unknown Nothing
          binds =  map ((\x -> pvar . mkName . fst $ x) &&& snd) lens
          body = fromMaybe (packAbsCon iaTyp (map fst lens) 0) $ userIaExp
       in pure (mkLetE binds body, getConNames icLayout [])

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


-- | Builder for the lens view expression that extracts the fields from complex types
-- -----------------------------------------------------------------------
-- | @layout@ is a tree like structure containing info about the layout of fields in a constructor
-- | @varToView@ is the var that the view transform is being applied to
-- | @prevGroup@ is the previous kind of type, which is essentially what type are we in right now in the recursion
-- | @prev@ previous expression, which is the tail rec var being built up
mkLensView :: HsEmbedLayout -> String -> GroupTag -> Maybe (Exp ()) -> [((String, Exp ()), (Type (), GroupTag))]
mkLensView layout varToView prevGroup prev
    = let hsTy = layout ^. hsTyp
          group =  layout ^. grTag
          fld = layout ^. fieldMap
          -- field map is a tree with int leaves -> only build vars for leaves
       in concatMap ( \(k, v) -> case v of
           (Left depth) -> [ ( ( mkKIdentVarBind (varToView) k depth
                               , fromMaybe (mkVar varToView) prev & (mkFromIntegral hsTy prevGroup) )
                             , (hsTy, prevGroup) )
                           ]
           (Right next) -> mkLensView next varToView group $ Just $ mkViewInfixE varToView group prev k
       ) $ M.toList $ fld
           {-
        _ -> case v of
           (Left depth) -> __impossible $ show k ++ "<==>" ++ show v
           (Right next) -> mkLensView next varToView group $ Just $ mkViewInfixE varToView group prev k


       case group of
        HsPrim ->        
        -}

-- | Builder the actual lens view infix expression 
-- -----------------------------------------------------------------------
-- | @varToView@ is the var that the view transform is being applied to
-- | @tag@ is the kind of type the view is being built for
-- | @prev@ previous expression, which is the tail rec var being built up
-- | @accessor@ the actual variable we want to view 
-- ----------------------------------------------------------------------------------------------------
mkViewInfixE :: String -> GroupTag -> Maybe (Exp ()) -> String -> Exp ()
mkViewInfixE varToView tag prev accessor
    = let viewE = case tag of
                    HsVariant -> mkOp "^?"
                    HsCollection -> mkOp "^.."
                    HsList -> mkOp "^.."
                    _ -> mkOp "^."
        in case prev of
             Just x -> let (op, x') = case tag of 
                                HsCollection -> ("^..", paren x)
                                HsList -> ("^..",  paren x)
                                _ -> (".", x)
                        in infixApp x' (mkOp op) $ mkVar accessor
             Nothing -> trace (show tag ) $ infixApp (mkVar varToView) viewE $ mkVar accessor

mkFromIntE :: Type () -> Exp () -> Exp ()
mkFromIntE ty prev =
    if isFromIntegral ty then infixApp prev (mkOp "$") (function "fromIntegral") else prev

mkFromIntegral :: Type () -> GroupTag -> Exp () -> Exp ()
mkFromIntegral ty group prev =
    if isFromIntegral ty 
    then infixApp prev (mkRevAppOp group) (function "fromIntegral") 
    else prev
    where mkRevAppOp x = case x of 
                        HsVariant -> mkOp "<&>"
                        _ -> mkOp "&"

mkVar :: String -> Exp ()
mkVar = var . mkName

mkOp :: String -> QOp ()
mkOp = op . mkName



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

isFromIntegral :: Type () -> Bool
isFromIntegral (TyCon _ (UnQual _ (Ident _ n)))
    = n `elem` ["Word8","Word16","Word32","Word64"]
isFromIntegral _ = False

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
