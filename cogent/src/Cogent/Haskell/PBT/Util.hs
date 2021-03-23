{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.PBT.Util where

import Cogent.Haskell.PBT.DSL.Types
import qualified Cogent.Haskell.HscSyntax as Hsc
import Cogent.Compiler (__impossible)
import qualified Cogent.Core as CC
import Cogent.Haskell.FFIGen (hsc2hsType)

import Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.Exts as HS
import qualified Data.Map as M
import Data.List (find, isInfixOf, isSuffixOf)
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

data HsFFILayout = HsFFILayout
    { _cTyp :: HS.Type ()
    , _groupTag :: GroupTag
    , _prevGroupTag  :: GroupTag
    , _cFieldMap :: M.Map String (Either String HsFFILayout)
    } deriving (Show)

data GroupTag = HsTuple | HsRecord | HsVariant | HsList | 
                HsPrim | HsTyVar | HsTyAbs | HsCollection | Unknown 
              deriving (Show, Eq)

makeLenses ''HsEmbedLayout
makeLenses ''HsFFILayout

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
-- TODO: this can be merged with determineUnpack'
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
        -- TODO: Abs Types cannot be dealt with so easily
        (if {- | any (\x -> x `isInfixOf` (getName cn)) hsCollectionTypes 
                           ->  HsEmbedLayout hsTyp HsCollection prevGroup $ M.singleton "each" (Left depth) -}
            | prevGroup == HsVariant -> HsEmbedLayout hsTyp HsVariant prevGroup M.empty
            | prevGroup == HsCollection -> HsEmbedLayout hsTyp HsCollection prevGroup M.empty
            | prevGroup == HsList -> HsEmbedLayout hsTyp HsList prevGroup M.empty
            | otherwise -> HsEmbedLayout hsTyp HsTyAbs prevGroup $ M.singleton fieldName (Left depth))
determineUnpack cogTyp hsTyp@(HS.TyApp _ l r) prevGroup depth fieldName
    = let (maybeConName:fieldTypes) = unfoldAppCon hsTyp
          cogFields = getFields cogTyp
          conName = getConIdentName maybeConName
          groupTag = if any (\x -> x `isInfixOf` conName) hsCollectionTypes 
                           then HsCollection 
                           else toGroupTag cogTyp
          accessors = getAccessor conName groupTag fieldTypes (Just (map fst cogFields))
        in HsEmbedLayout l groupTag prevGroup $
            M.fromList $ if not (null cogFields) && not (null accessors) && not (null fieldTypes) 
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


-- | Builder for the layout type that is used for building the lens view. Similar to determineUnpack
-- | but without the cogent type supplied.
-- -- -----------------------------------------------------------------------
-- | @hsTyp@ haskell type
-- | @depth@ depth of recursion
-- | @fieldName@ name of field we are in, since we recurse until we reach a prim, this will tell us the
-- |             field that prim is bound to.
determineUnpack' :: HS.Type () -> GroupTag -> Int -> String -> HsEmbedLayout
determineUnpack' hsTyp@(HS.TyParen _ t) prevGroup depth fieldName 
    = determineUnpack' t prevGroup depth fieldName
determineUnpack' hsTyp@(HS.TyUnboxedSum _ tfs) prevGroup depth fieldName 
    = determineUnpack' (HS.TyTuple () HS.Unboxed tfs) prevGroup depth fieldName
determineUnpack' hsTyp@(HS.TyTuple _ _ tfs) prevGroup depth fieldName 
    = HsEmbedLayout hsTyp HsTuple prevGroup $
        M.fromList [ let k = "_"++show (i+1)
                       in (k , Right (determineUnpack' (tfs!!i) HsTuple (depth+1) k))
                   | i <- [0..length tfs-1] ]
determineUnpack' hsTyp@(HS.TyCon _ cn) prevGroup depth fieldName
    = flip (fromMaybe)
        (checkIsPrim cn <&> (\x -> HsEmbedLayout hsTyp HsPrim prevGroup (M.singleton fieldName (Left depth))))
        -- TODO: how to handle other Con?
        -- TODO: Abs Types cannot be dealt with so easily
        (if {- | any (\x -> x `isInfixOf` (getName cn)) hsCollectionTypes 
                           ->  HsEmbedLayout hsTyp HsCollection prevGroup $ M.singleton "each" (Left depth) -}
            | prevGroup == HsVariant -> HsEmbedLayout hsTyp HsVariant prevGroup M.empty
            | prevGroup == HsCollection -> HsEmbedLayout hsTyp HsCollection prevGroup M.empty
            | prevGroup == HsList -> HsEmbedLayout hsTyp HsList prevGroup M.empty
            | otherwise -> HsEmbedLayout hsTyp HsTyAbs prevGroup $ M.singleton fieldName (Left depth))
determineUnpack' hsTyp@(HS.TyApp _ l r) prevGroup depth fieldName
    = let (maybeConName:fieldTypes) = unfoldAppCon hsTyp
          conName = getConIdentName maybeConName
          groupTag = toGroupTag' conName
          -- TODO: unsure if ^^ works - when would oa be a custom record?
          --       Makes more sense to restrict oa to either a prim or a built in hs type rather then allowing
          --       them to define there own records
          accessors = getAccessor conName groupTag fieldTypes Nothing
        in HsEmbedLayout l groupTag prevGroup $
            M.fromList $ if not (null accessors) && not (null fieldTypes) then 
                           [ ( accessors!!i
                             , Right (determineUnpack' (fieldTypes!!i) groupTag (depth+1) (accessors!!i)))
                           | i <- [0..length fieldTypes-1] ]
                       else [(fieldName, Left depth)]
determineUnpack' hsTyp@(HS.TyList _ ty) prevGroup depth fieldName
    = HsEmbedLayout hsTyp HsList prevGroup $
        M.singleton "list" $ Right (determineUnpack' hsTyp HsList (depth+1) "1")
determineUnpack' hsTyp prevGroup depth fieldName 
    = __impossible $ "Unknown Shallow Embedding "++show hsTyp


-- | Unpacking Helpers
-- -----------------------------------------------------------------------
getFields :: CC.Type t a -> [(String, (CC.Type t a, Bool))]
getFields (CC.TRecord _ fs _) = fs
getFields (CC.TSum alts) = alts
getFields (CC.TProduct l r) = [("_1", (l,False)), ("_2", (r,False))]
getFields (CC.TCon _ ts _) = if null ts then []
                             else [(("_"++show (i+1)), (ts!!i, False)) | i <- [0..length ts-1]]
getFields (CC.TFun l r) = [("_1", (l,False)), ("_2", (r,False))]
getFields (CC.TArray t _ _ _) = [("_1", (t,False))]
getFields _ = __impossible "unknown fields"

toGroupTag :: CC.Type t a -> GroupTag
toGroupTag cogTyp 
    = case cogTyp of
       (CC.TRecord _ _ _) -> HsRecord
       (CC.TSum _) -> HsVariant
       (CC.TVar _) -> HsTyVar
       (CC.TVarBang _) -> HsTyVar
       (CC.TVarUnboxed  _ ) -> HsTyVar
       (CC.TCon _ _ _) -> HsTyAbs
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

toGroupTag' :: String -> GroupTag
toGroupTag' conName = if | isSumType conName -> HsVariant 
                         | isCollection conName -> HsCollection
                         | otherwise -> HsRecord 

-- unfolding Constructor Application
unfoldAppCon :: HS.Type () -> [HS.Type ()]
unfoldAppCon t = case t of
                   (HS.TyApp _ l r) -> unfoldAppCon l ++ unfoldAppCon r
                   (HS.TyCon _ n) -> [t]
                   _ -> [t]

getAccessor :: String -> GroupTag -> [HS.Type ()] -> Maybe [String] -> [String]
getAccessor conName groupTag ts fieldNames
    = let fs = fromMaybe (filter (/=unknownCon) . map getConIdentName $ ts
               ) $ fieldNames
        in trace (show fieldNames) $ case groupTag of
            HsVariant -> if | conName == "Maybe" && length fs == 1 -> map (const "_Just") fs
                            | conName == "Either" && length fs == 2 -> ["_Left", "_Right"]
                            | otherwise -> map (\x -> "_" ++ conName ++ "_" ++ x) fs
            HsCollection -> ["each"]
            HsList -> ["each"]
            HsTyAbs -> if any (\x -> x `isInfixOf` conName) hsCollectionTypes then ["each"]
                       else ["unknown"]
            _ -> fs

checkIsPrim :: HS.QName () -> Maybe String
checkIsPrim x = case x of
    (HS.UnQual _ (HS.Ident _ n)) -> find (== n) prims
    _ -> Nothing

getName :: HS.QName () -> String
getName x = case x of
    (HS.UnQual _ (HS.Ident _ n)) -> n
    _ -> "unknown"

getConIdentName :: HS.Type () -> String
getConIdentName (HS.TyCon _ (HS.UnQual _ (HS.Ident _ n))) = n
                       -- TODO: handle other types of Con
getConIdentName _ = unknownCon

isCollection :: String -> Bool
isCollection x = x `elem` hsCollectionTypes

isSumType :: String -> Bool
isSumType x = x `elem` hsSumTypes

unknownCon :: String
unknownCon = "Unknown"

unknownConTy :: HS.Type ()
unknownConTy = HS.TyCon () $ HS.UnQual () $ HS.Ident () unknownCon

prims = ["Word8","Word16","Word32","Word64","Bool","String"] ++ intPrims
intPrims = ["Int", "Int8", "Int16", "Int32", "Int64", "Integer"]

hsSumTypes = ["Maybe", "Either"]
hsCollectionTypes = ["List", "Array", "Set", "Map"]


-- | find FFI function
-- -----------------------------------------------------------------------
findHsFFIFunc :: HS.Module () -> String -> (String, HS.Type (), HS.Type ())
findHsFFIFunc (HS.Module _ _ _  _ decls) fname 
    = fromMaybe (__impossible "cant find matching FFI!") $
         (find (\d -> case d of (HS.ForImp _ _ _ _ (HS.Ident _ n) tys) -> fname `isSuffixOf` n; _ -> False) decls <&> 
            (\(HS.ForImp _ _ _ _ (HS.Ident _ n) x) -> let t = getTiTo x in (n, fst t, snd t)))
    where getTiTo (HS.TyFun _ ti to) = (ti, to)
          getTiTo _ = __impossible "cant find ffi types"

-- seach for data type decl with constructor name matching given name
-- map of Data con names to map of field names to their Type 
-- should be a singleton since Ctypes are just simple records.
findFFITypeByName :: Hsc.HscModule -> String -> M.Map String (M.Map String (HS.Type ()))
findFFITypeByName (Hsc.HscModule _ _ decls) name 
    = fromMaybe (M.empty) $
         (find (\d -> case d of 
                        (Hsc.HsDecl (Hsc.DataDecl cname _ cs)) -> cname == name ;
                        _ -> False
               ) decls <&>
            (\(Hsc.HsDecl (Hsc.DataDecl cname _ cs)) 
                -> M.fromList $
                map (\(Hsc.DataCon n x) -> (n, M.fromList (map (\(cn,t) -> (cn, (hsc2hsType t))) x))) cs))


-- replace pure hs embedding layout record with C type layout details (but keeping bind names)
-- expects unfolded ty
determineUnpackFFI :: HsEmbedLayout -> String -> String -> String -> HS.Type () -> M.Map String (M.Map String (HS.Type ())) -> HsFFILayout
determineUnpackFFI layout varToUnpack oldK fieldName ffiTy ffiFields
    = let hsTy = layout ^. hsTyp
          group = layout ^. grTag
          prevGroup = layout ^. prevGrTag
          fld' = M.toList $ layout ^. fieldMap
          cTy = let ts = filter (\x -> all (/= getConIdentName x) ["Ptr", "IO"]) $ unfoldFFITy ffiTy
                  in if length ts /= 1 then __impossible "boom!" else head ts
          cFields = M.toList $ let cn = getConIdentName cTy
                      in fromMaybe M.empty $ M.lookup cn ffiFields
          fld = if length fld' == length cFields
                    then fld'
                    -- must be variant -> append tag field from cFields
                    -- these odd extra fields in variants can just be referred to by these name without any ticks e.g. oc_tag
                    -- perhaps allow user to supply the list of odd fields
                    else fld' ++ ( map (\(k,v) -> (k, Left 0)) $ filter (\(k,v) -> "tag" `isInfixOf` getConIdentName v) cFields)
        in HsFFILayout ffiTy group prevGroup $ M.fromList $ 
            [ let (k,v) = fld!!i
                  (ck,cv) = cFields!!i
                in case v of 
               (Left depth) -> ( mkKIdentVarBind varToUnpack k depth
                               , Left $ fieldName)
               (Right next) -> ( ck
                               , Right $ determineUnpackFFI next varToUnpack k ck cv ffiFields )
            | i <- [0..length fld-1] ]
        
{-

            concatMap (\(k,v) -> case v of
               (Left depth) -> [( fieldName
                               , Left $ mkKIdentVarBind varToUnpack oldK depth )]
               (Right next) -> -- TODO: instead, map over c fields here 
                                [ ( ck
                                  , Right $ determineUnpackFFI next varToUnpack k ck cv ffiFields )
                                | (ck, cv) <- M.toList cFields ]
                                

        ) $ M.toList fld -}{-if (M.size fld == M.size cFields) then zip (M.toList fld) (M.toList cFields) 
            -- must be variant -> remove tag field from cFields
            else 
            -}

unfoldFFITy :: HS.Type () -> [HS.Type ()]
unfoldFFITy t@(HS.TyTuple _ _ tys) = tys
unfoldFFITy t@(HS.TyVar _ _) = [t]
unfoldFFITy t = unfoldAppCon t




{-
exampleHsEmbLay = HsEmbedLayout 
    (HS.TyTuple () HS.Boxed [HS.TyCon () (HS.UnQual () (HS.Ident () "SysState")),HS.TyCon () (HS.UnQual () (HS.Ident () "Word32"))] )
        HsTuple
        Unknown
        ( M.fromList 
        [ ("_1", Right (
            HsEmbedLayout (HS.TyCon () (HS.UnQual () (HS.Ident () "SysState")))
              HsTyAbs
              HsTuple
              (M.fromList [("_1",Left 1)])
            ))
        , ("_2", Right (
             HsEmbedLayout (HS.TyCon () (HS.UnQual () (HS.Ident () "Word32"))) HsPrim HsTuple
                 (M.fromList [("_2",Left 1)]))
          )
        ] )
        -}
