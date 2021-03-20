{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.PBT.Util where

import Cogent.Haskell.PBT.DSL.Types
import Cogent.Compiler (__impossible)
import qualified Cogent.Core as CC
import qualified Cogent.Common.Types as CT
import qualified Data.Fin as CD

import Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.Exts as HS
import qualified Data.Map as M
import Data.List (find, isInfixOf)
import Data.Maybe (fromMaybe)
import Debug.Trace

import Lens.Micro
import Lens.Micro.TH

-- | Cogent HS embedding Layout type
-- -----------------------------------------------------------------------
-- | used in analysing the types ic/ia/oc/oa when building abstraction
-- | function and refinement relation
data HsEmbedLayout = HsEmbedLayout
    { _hsTyp :: HS.Type ()
    , _grTag :: GroupTag
    , _prevGrTag :: GroupTag
    , _fieldMap :: M.Map String (Either Int HsEmbedLayout)
    } deriving (Show)

data GroupTag = HsTuple | HsRecord | HsVariant | HsList | HsPrim | HsTyVar | HsTyAbs | Unknown deriving (Show)

makeLenses ''HsEmbedLayout

-- | Helper functions for accessing structure
-- -----------------------------------------------------------------------
findExprsInDecl :: PbtKeyword -> [PbtDescDecl] -> [PbtDescExpr]
findExprsInDecl kw ds = fromMaybe (__impossible "No expression found!") $ 
                          (find (\d -> d ^. kword == kw) ds) <&> (^. kexprs)

-- find ic/ia/oc/oa type and expression
findKIdentTyExp :: PbtKeyword -> PbtKeyidents -> [PbtDescDecl] -> (Maybe (HS.Type ()), Maybe (HS.Exp ()))
findKIdentTyExp kw kid ds
    = let declExprs = fromMaybe [] $ (find (\d -> d ^. kword == kw) ds) <&> (^. kexprs)
          exprs = filter (\e -> case e ^. kident of
                             Just kid' -> kid' == kid; _ -> False
                  ) $ declExprs
          in ( (exprs ^.. each . kexp . _Just . _Left) ^? ix 0    -- find ty
             , (exprs ^.. each . kexp . _Just . _Right) ^? ix 0 ) -- find mapping exp associated with this keyvar


-- find ic/ia/oc/oa map expression, maybe lhs transform on kid and maybe rhs transform on kid.
findKIdentExp :: PbtKeyword -> PbtKeyidents -> [PbtDescDecl] -> (Maybe (HS.Exp ()), Maybe (HS.Exp ()))
findKIdentExp kw kid ds
    = let declExprs = fromMaybe [] $ (find (\d -> (d ^. kword) == kw) ds) <&> (^. kexprs)
          exprs = filter (\e -> case e ^. kident of
                             Just kid' -> kid' == kid; _ -> False
                  ) $ declExprs
          in ( (exprs ^.. each . rhsExp . _Just) ^? ix 0
             , (exprs ^.. each . kexp . _Just . _Right) ^? ix 0 )

-- find ic/ia/oc/oa pred expression -> :| operator, lhs is optional
findAllPreds :: PbtKeyword -> [PbtDescDecl] -> M.Map PbtKeyidents [(Maybe (HS.Exp ()), (HS.Exp ()))]
findAllPreds kw ds
    = let declExprs = fromMaybe [] $ (find (\d -> (d ^. kword) == kw) ds) <&> (^. kexprs)
          exprsIc = filter (\e -> fromMaybe (False) $ 
                                    (e ^. kident) <&> (==Ic)
                         ) $ declExprs
          exprsPred = filter (\e -> fromMaybe (False) $ 
                                    (e ^. kident) <&> (==Pred)
                         ) $ declExprs 
          ics = zip (exprsIc ^.. each . rhsExp) 
                     (exprsIc ^.. each . kexp . _Just . _Right) 
          justPreds = zip ( exprsPred ^.. each . rhsExp) 
                           ( exprsPred ^.. each . kexp . _Just . _Right )
        in M.union (M.singleton Ic ics) (M.singleton Pred justPreds)



-- | mk unique var bind
-- -----------------------------------------------------------------------
mkKIdentVarBind :: String -> String -> Int -> String
mkKIdentVarBind kid name depth = kid++(if "_" `isInfixOf` name then "" else "_")++name++ replicate depth (head "'")

-- | find contexts (given by PbtKeyword) which are just bools
-- -----------------------------------------------------------------------
checkBoolE :: PbtKeyword -> [PbtDescDecl] -> Bool
checkBoolE k decls 
    = case ((findExprsInDecl k decls) ^.. each . kexp . _Just . _Left) ^? ix 0 of
        Just x -> boolResult x
        _ -> False

boolResult :: HS.Type () -> Bool
boolResult (HS.TyCon _ (HS.UnQual _ (HS.Ident _ n))) = read n
boolResult _ = False


-- | determine how to unpack a type
-- -----------------------------------------------------------------------

-- | Builder for the layout type that is used for building the lens view, which encodes structure
-- | and other info used in building the view.
-- | Recurse through both @cogIcTyp@ and @icTyp@ at the same time until we reach a primitive, means
-- | we can gather info on every field in the type.
-- -----------------------------------------------------------------------
-- | @cogTyp@ cogent type of the concrete input
-- | @hsTyp@ haskell shallow embedding of cogent type
-- | @depth@ depth of recursion
-- | @fieldName@ name of field we are in, since we recurse until we reach a prim, this will tell us the
-- |             field that prim is bound to.
determineUnpack :: CC.Type t a -> HS.Type () -> GroupTag -> Int -> String -> HsEmbedLayout
determineUnpack cogTyp hsTyp@(HS.TyParen _ t) prevGroup depth fieldName 
    = determineUnpack cogTyp t prevGroup depth fieldName
determineUnpack cogTyp hsTyp@(HS.TyUnboxedSum _ tfs) prevGroup depth fieldName
    = determineUnpack cogTyp (HS.TyTuple () HS.Unboxed tfs) prevGroup depth fieldName
determineUnpack cogTyp hsTyp@(HS.TyTuple _ _ tfs) prevGroup depth fieldName
    = let fs = getFields cogTyp
        in HsEmbedLayout hsTyp HsTuple prevGroup $ 
            M.fromList [ let k = "_"++show (i+1)
                           in ( k 
                              , Right (determineUnpack (fst (snd (fs!!i))) (tfs!!i) HsTuple (depth+1) k) )
                       | i <- [0..length tfs-1] ]
determineUnpack cogTyp hsTyp@(HS.TyVar _ (HS.Ident _ _)) prevGroup depth fieldName
    = HsEmbedLayout hsTyp HsTyVar prevGroup $ M.singleton fieldName $ Left depth
determineUnpack cogTyp hsTyp@(HS.TyCon _ cn) prevGroup depth fieldName
    = flip (fromMaybe)
        (checkIsPrim cn <&> (\x -> HsEmbedLayout hsTyp HsPrim prevGroup (M.singleton fieldName (Left depth)))) 
        -- TODO: how to handle other Con?
        (HsEmbedLayout hsTyp HsTyAbs prevGroup M.empty) -- (M.singleton (getConIdentName hsTyp) (Left depth)))
determineUnpack cogTyp hsTyp@(HS.TyApp _ l r) prevGroup depth fieldName
    = let (maybeConName:fieldTypes) = unfoldAppCon hsTyp
          cogFields = getFields cogTyp
          conName = getConIdentName maybeConName
          groupTag = toGroupTag cogTyp
          accessors = getAccessor conName groupTag fieldTypes (Just (map fst cogFields))
        in HsEmbedLayout l groupTag prevGroup $
            M.fromList $ if (length cogFields /= 0 && length accessors /= 0 && length fieldTypes /= 0) 
                         then [ (let a = accessors!!i
                                     f =  cogFields!!i
                                    in ( a
                                       , Right (determineUnpack (fst (snd f)) (fieldTypes!!i) groupTag (depth+1) a) ) )
                              | i <- [0..length cogFields-1] ]
                         else [(fieldName, (Left depth))]
determineUnpack cogTyp hsTyp@(HS.TyList _ ty) prevGroup depth fieldName
    = let elemCogTy = case cogTyp of
                     (CC.TArray t _ _ _) -> t; _ -> __impossible $ "Bad Shallow embedding"++show hsTyp
        in HsEmbedLayout hsTyp HsList prevGroup $ 
            M.singleton "list" $ Right (determineUnpack elemCogTy ty HsList (depth+1) "list")
determineUnpack cogTyp hsTyp prevGroup depth fieldName
    = __impossible $ "Unknown Shallow Embedding "++show hsTyp

getFields :: CC.Type t a -> [(String, (CC.Type t a, Bool))]
getFields (CC.TRecord _ fs _) = fs
getFields (CC.TSum alts) = alts
getFields (CC.TProduct l r) = [("1", (l,False)), ("2", (r,False))]
getFields (CC.TCon _ ts _) = if length ts == 0 then []
                             else [((show (i+1)), (ts!!i, False)) | i <- [0..length ts-1]]
getFields (CC.TFun l r) = [("1", (l,False)), ("2", (r,False))]
getFields (CC.TArray t _ _ _) = [("1", (t,False))]
getFields _ = []
       -- TODO: handle C types ???

toGroupTag :: CC.Type t a -> GroupTag
toGroupTag cogTyp 
    = case cogTyp of
       (CC.TRecord _ _ _) -> HsRecord
       (CC.TSum _) -> HsVariant
       (CC.TVar _) -> HsTyVar
       (CC.TVarBang _) -> HsTyVar
       (CC.TVarUnboxed  _ ) -> HsTyVar
       (CC.TCon _ _ _) -> HsPrim
       (CC.TFun _ _) -> Unknown
       (CC.TPrim _) -> HsPrim
       (CC.TString) -> HsPrim
       (CC.TProduct _ _) -> HsTuple
       (CC.TUnit) -> HsPrim
       (CC.TRPar _ _) -> HsRecord
       (CC.TRParBang _ _) -> HsRecord
       (CC.TArray _ _ _ _) -> HsList
       (CC.TRefine _ _ ) -> Unknown
       -- TODO: handle C types

-- unfolding Constructor Application
unfoldAppCon :: HS.Type () -> [HS.Type ()]
unfoldAppCon t = case t of
                   (HS.TyApp _ l r) -> unfoldAppCon l ++ unfoldAppCon r
                   (HS.TyCon _ n) -> [t]
                   _ -> [t]

getAccessor :: String -> GroupTag -> [HS.Type ()] -> Maybe [String] -> [String]
getAccessor conName groupTag ts fieldNames
    = let fs = case fieldNames of
                 Just x -> x
                 Nothing -> filter (/=unknownCon) . map getConIdentName $ ts
        in case groupTag of
            HsVariant -> if | conName == "Maybe" && length fs == 1 -> map (const "_Just") fs
                            | conName == "Either" && length fs == 2 -> ["_Left", "_Right"]
                            | otherwise -> map (\x -> "_" ++ conName ++ "_" ++ x) fs
            _ -> fs

checkIsPrim :: HS.QName () -> Maybe String
checkIsPrim x = case x of
    (HS.UnQual _ (HS.Ident _ n)) -> find (== n) prims
    _ -> Nothing

getConIdentName :: HS.Type () -> String
getConIdentName (HS.TyCon _ (HS.UnQual _ (HS.Ident _ n))) = n
                       -- TODO: handle other types of Con
getConIdentName _ = unknownCon

unknownCon :: String
unknownCon = "Unknown"


unknownConTy :: HS.Type ()
unknownConTy = HS.TyCon () $ HS.UnQual () $ HS.Ident () unknownCon

prims = ["Word8","Word16","Word32","Word64","Bool","String"] ++ intPrims
intPrims = ["Int", "Int8", "Int16", "Int32", "Int64", "Integer"]
hsSumTypes = ["Maybe","Either"]
