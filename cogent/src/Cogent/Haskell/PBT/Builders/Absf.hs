{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}


-- | Abstraction Function Builder
-- ----------------------------------------------------------------

module Cogent.Haskell.PBT.Builders.Absf

-- (
   --  absFDecl'

-- ) 
where

import Cogent.Haskell.PBT.Types



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
mkAbsFExp :: String -> Type () -> [CC.Definition TypedExpr VarName b] -> SG (Type (), Type (), Exp (), [String])
mkAbsFExp fname iaTyp defs = do
    let def = fromJust $ find (\x -> CC.getDefinitionId x == fname) defs
    (icT, iaT, absE, conNames) <- mkAbsFExp' def iaTyp
    pure (icT, iaT, absE, conNames)
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
    = pure (TyCon () (mkQName "Unknown"), iaT, function "undefined", [])

-- | Builder for abstraction function body. For direct abstraction (default), builds a 
-- | let expression which binds lens views to variables that and then used 
-- | to pack the outgoing Constructor
-- -----------------------------------------------------------------------
-- | @cogIcTyp@ is the cogent type of the concrete input
-- | @icTyp@ is the Haskell type of the concrete input
-- | @iaTyp@ is the Haskell type of the abstract input (what we are trying to abstract to)
mkAbsFBody :: CC.Type t a -> Type () -> Type () -> SG (Exp (), [String])
mkAbsFBody cogIcTyp icTyp iaTyp
    = let icLayout = determineUnpack cogIcTyp icTyp 0 "None"
          lens = map fst $ mkLensView icLayout "ic" Unknown Nothing
          binds = map ((\x -> pvar . mkName . fst $ x) &&& snd) lens
          body = packAbsCon iaTyp (map fst lens) 0
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


-- | Builder the lens view expression that extracts the fields from complex types
-- -----------------------------------------------------------------------
-- | @layout@ is a tree like structure containing info about the layout of fields in a constructor
-- | @varToView@ is the var that the view transform is being applied to
-- | @prevGroup@ is the previous kind of type, which is essentially what type are we in right now in the recursion
-- | @prev@ previous expression, which is the tail rec var being built up
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

-- | Builder for the layout type that is used for building the lens view, which encodes structure
-- | and other info used in building the view.
-- | Recurse through both @cogIcTyp@ and @icTyp@ at the same time until we reach a primitive, means
-- | we can gather info on every field in the type.
-- -----------------------------------------------------------------------
-- | @cogIcTyp@ cogent type of the concrete input
-- | @icTyp@ haskell shallow embedding of cogent type
-- | @depth@ depth of recursion
-- | @fieldName@ name of field we are in, since we recurse until we reach a prim, this will tell us the
-- |             field that prim is bound to.
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
-- TODO: For the sake of completeness ... ensure these can never really occur
{-
    (TyFun _ iTy oTy) ->
    (TyVar _ name) -> 
    (TyInfix _ lTy name rTy) ->
    (TyUnboxedSum _ tfs) -> 
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
