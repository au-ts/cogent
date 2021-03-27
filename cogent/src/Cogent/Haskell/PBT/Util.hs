{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TemplateHaskell #-}

module Cogent.Haskell.PBT.Util where

import Cogent.Compiler (__impossible)
import qualified Cogent.Core as CC
import Cogent.Haskell.PBT.DSL.Types
import Cogent.Haskell.FFIGen (hsc2hsType)
import qualified Cogent.Haskell.HscSyntax as Hsc
import Cogent.Haskell.Shallow (mkName, mkQName, mkTyConT)

import Language.Haskell.Exts.Build
import Language.Haskell.Exts.SrcLoc
import qualified Language.Haskell.Exts as HS

import Lens.Micro
import Lens.Micro.TH

import Data.List (find, isInfixOf, isSuffixOf, partition, sortOn, stripPrefix)
import Data.List.Extra (trim)
import Data.Char (toLower)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import Debug.Trace

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

data GroupTag = HsTuple | HsRecord | HsVariant | HsMaybe | HsList | 
                HsPrim | HsTyVar | HsTyAbs | HsCollection | 
                Unknown 
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
        -- Cannot make any assumptions here b/c it is a hs embedding of the cogent type 
        -- which may be abstract
        (HsEmbedLayout hsTyp HsTyAbs prevGroup $ M.singleton fieldName (Left depth))
determineUnpack cogTyp hsTyp@(HS.TyApp _ l r) prevGroup depth fieldName
    = let (maybeConName:fieldTypes) = unfoldAppCon hsTyp
          cogFields = getFields cogTyp
          conName = getConIdentName maybeConName
          groupTag = toGroupTag cogTyp
          accessors = getAccessor conName groupTag fieldTypes (Just (map fst cogFields))
        in HsEmbedLayout hsTyp groupTag prevGroup $
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
        -- note: fine to check here -> as we expect a haskell type (abstracted away from concrete function)
        ({-if | prevGroup == HsMaybe -> HsEmbedLayout hsTyp HsTyAbs prevGroup $ M.singleton fieldName (Left depth)

            | otherwise -> -} HsEmbedLayout hsTyp HsTyAbs prevGroup $ M.singleton fieldName (Left depth))
determineUnpack' hsTyp@(HS.TyApp _ l r) prevGroup depth fieldName
    = let (maybeConName:fieldTypes) = unfoldAppCon hsTyp
          conName = getConIdentName maybeConName
          groupTag = toGroupTag' conName
          -- TODO: unsure if ^^ works - when would oa be a custom record?
          --       Makes more sense to restrict oa to either a prim or a built in hs type rather then allowing
          --       them to define there own records
          accessors = getAccessor conName groupTag fieldTypes Nothing
        in HsEmbedLayout hsTyp groupTag prevGroup $
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

-- --------------------------------------------------------------------------
-- replace pure hs embedding layout record with C type layout details (but keeping bind names)
-- expects unfolded ty
determineUnpackFFI :: HsEmbedLayout 
                   -> String 
                   -> String 
                   -> HS.Type () 
                   -> Hsc.HscModule
                   -- -> M.Map String (M.Map String (HS.Type ())) 
                   -> HsFFILayout
determineUnpackFFI layout varToUnpack fieldName ffiTy ffiTypes
    = let hsTy = layout ^. hsTyp
          group = layout ^. grTag
          prevGroup = layout ^. prevGrTag
          fld = M.toList $ layout ^. fieldMap
          cTy = let ts = filter (\x -> all (/= getConIdentName x) ["Ptr", "IO"]) $ unfoldFFITy ffiTy
                  in if length ts /= 1 then __impossible $ "Bad FFI Type"++show ts
                     else head ts
          cn = getConIdentName cTy
          ffiFields = findFFITypeByName ffiTypes $ cn
          cFields = M.toList $ fromMaybe M.empty $ M.lookup cn ffiFields
        in HsFFILayout ffiTy group prevGroup $ M.fromList $ 
         if group /= HsVariant 
         then [ let (k,v) = fld!!i
                    (ck,cv) = if i >= length cFields then (fieldName, cTy)
                              else cFields!!i
                  in case v of 
                  (Left depth) -> ( mkKIdentVarBind varToUnpack k depth
                                  , Left $ fieldName)
                  (Right next) -> ( if (head ck == '_') then tail ck else ck
                                  , Right $ determineUnpackFFI next varToUnpack ck cv ffiTypes )
              | i <- [0..length fld-1] ]
         else [ let (ck,cv) = cFields!!i
                    -- Have to create ad-hoc "Tag" field to match up with the C type fields
                    -- where Variants are Enums and the Tag field is the enumeration.
                    -- Assumes Variants always are represented by Enums on the C level
                    -- and that the names of the variant's alternatives match the enums names 
                    -- (minus all the generated stuff prepended on)
                    (k,v) = let ck' = fromMaybe "unknown" $ stripPrefix "ct" $
                                        [toLower x | x <- ck, x `notElem` ("_"++[head . show $ y | y <- [0..9]])]
                              in fromMaybe (if "tag" `isInfixOf` ck 
                                 then let nn = "_"++cn++"Tag"
                                        in ( nn
                                           , Right $ HsEmbedLayout (mkTyConT . mkName $ "Int") HsPrim HsVariant $ M.singleton nn $ Left 0)
                                 else ("unknown", Left 0)) $
                                find (\(k,v) -> ck' `isInfixOf` (allLower k)) fld
                  in case v of 
                  (Left depth) -> ( mkKIdentVarBind varToUnpack k depth
                                  , Left $ fieldName)
                  (Right next) -> ( if (head ck == '_') then tail ck else ck
                                  , Right $ determineUnpackFFI next varToUnpack ck cv ffiTypes )
              | i <- [0..length cFields-1] ]

allLower :: String -> String 
allLower xs = [toLower x | x <- xs]

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
toGroupTag' conName = if | isMaybeType conName -> HsMaybe 
                         | isSumType conName -> HsVariant 
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
        in case groupTag of
            HsMaybe -> ["_Just"]
            HsVariant -> if | conName == "Either" && length fs == 2 -> ["_Left", "_Right"]
                            | otherwise -> map (\x -> "_" ++ conName ++ "_" ++ x) fs
            HsCollection -> ["each" | t <- ts]
            HsList -> ["each" | t <- ts]
            HsTyAbs -> ["unknown"]
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

isMaybeType :: String -> Bool
isMaybeType x = x `elem` hsMaybeTypes

unknownCon :: String
unknownCon = "Unknown"

unknownConTy :: HS.Type ()
unknownConTy = HS.TyCon () $ HS.UnQual () $ HS.Ident () unknownCon

prims = ["Word8","Word16","Word32","Word64","Bool","String"] ++ intPrims
intPrims = ["Int", "Int8", "Int16", "Int32", "Int64", "Integer"]

hsMaybeTypes = ["Maybe"] 
hsSumTypes = ["Either"]
hsCollectionTypes = ["List", "Array", "Set", "Map"]


        
unfoldFFITy :: HS.Type () -> [HS.Type ()]
unfoldFFITy t@(HS.TyTuple _ _ tys) = tys
unfoldFFITy t@(HS.TyVar _ _) = [t]
unfoldFFITy t = unfoldAppCon t


-- | scan user infix expression -> looking for lens/prisms in exp,
-- | and use the structure of the lens/prism to create the unique identifier var
-- | and place it in a map.
-- | We know it will produce the same var as if the type was scanned with 
-- | HsEmbedLayout type. 
-- -----------------------------------------------------------------------
scanUserInfixE :: HS.Exp () -> Int -> String -> M.Map String String
scanUserInfixE (HS.Paren () e) depth kid = scanUserInfixViewE e depth kid
scanUserInfixE exp depth kid
    | (HS.InfixApp () lhs op rhs) <- exp 
    = let opname = getOpStr op
        in if | any (==opname) ["^.", "^?"] -> scanUserInfixViewE exp depth kid
              | otherwise -> M.union (scanUserInfixE lhs depth kid) (scanUserInfixE rhs depth kid)
scanUserInfixE exp depth kid =  scanUserInfixViewE exp depth kid

scanUserShortE :: HS.Exp () -> Int -> M.Map String String
scanUserShortE (HS.Paren () e) depth = scanUserShortE e depth
scanUserShortE (HS.Var _ (HS.UnQual _ (HS.Ident _ name))) depth 
    = if ("'" `isInfixOf` (trim name)) then M.singleton (trim name) ([x | x <- (trim name), x `notElem` "'"])
      else M.empty
scanUserShortE _ depth = M.empty 

-- | scan (^.|^?) expressions 
-- | want to extract fieldname & depth as this is enought to build the 
-- | fieldname pattern for view binds i.e. name ++ replicate depth $ P.head "'"
-- | in the map, fieldname ++ postfix maps to depth in expression
-- | depth only increases when recursing down RHS
-- -----------------------------------------------------------------------
scanUserInfixViewE :: HS.Exp () -> Int -> String -> M.Map String String
scanUserInfixViewE (HS.Paren () e) depth kid = scanUserInfixViewE e depth kid
scanUserInfixViewE (HS.InfixApp () lhs op rhs) depth kid  
    = if getOpStr op == "." 
       then M.union (scanUserInfixViewE lhs (depth) kid ) (scanUserInfixViewE rhs (depth+1) kid )
       else M.union (scanUserInfixViewE lhs (depth) kid ) (scanUserInfixViewE rhs (depth) kid )
scanUserInfixViewE exp depth kid | (HS.Var _ (HS.UnQual _ (HS.Ident _ name))) <- exp
    = if | (any (==trim name ) ["ic","ia","oc","oa"]) -> M.empty
         | null (scanUserShortE exp 0) -> M.singleton (mkKIdentVarBind kid name (depth+1)) (name)
         | otherwise -> scanUserShortE exp 0
scanUserInfixViewE _ depth kid = M.empty

-- | Builder for unique var identifier - this pattern is also follow by HsEmbedLayout
-- -----------------------------------------------------------------------

-- | Return operator string value
-- -----------------------------------------------------------------------
getOpStr :: HS.QOp () -> String
getOpStr (HS.QVarOp _ (HS.UnQual _ (HS.Symbol _ name))) = name
getOpStr _ = ""

-- | Replace lens/prisms ((^.)|(^?)) nodes in the Exp AST with vars
-- | that are bound such that the expression is semantically equivalent
-- -----------------------------------------------------------------------
replaceVarsInUserInfixE :: HS.Exp () -> Int -> M.Map String String -> HS.Exp ()
replaceVarsInUserInfixE (HS.Paren () e) depth vars = replaceVarsInUserInfixE e depth vars
replaceVarsInUserInfixE exp depth vars
    | (HS.InfixApp () lhs op rhs) <- exp 
    = let opname = getOpStr op
        in if | any (==opname) ["^.", "^?", ".~"] -> replaceInfixViewE exp depth vars
              | otherwise -> HS.InfixApp () (replaceVarsInUserInfixE lhs depth vars) op (replaceVarsInUserInfixE rhs depth vars)
replaceVarsInUserInfixE exp depth vars = exp

-- | Actual transform of AST (lens/prisms -> var) occurs here
-- -----------------------------------------------------------------------
replaceInfixViewE :: HS.Exp () -> Int -> M.Map String String -> HS.Exp ()
replaceInfixViewE (HS.Paren () e) depth vars = HS.Paren () $ replaceInfixViewE e depth vars
replaceInfixViewE (HS.InfixApp () lhs op rhs) depth vars 
    --   ok just to handle rhs because of fixity
    = replaceInfixViewE rhs (depth+1) vars
replaceInfixViewE exp depth vars | (HS.Var _ (HS.UnQual _ (HS.Ident _ name))) <- exp
    -- TODO: how to handle multiple
    = let ns = filter (\(k,v) -> v == name) $ M.toList vars
        in if length ns == 0 then exp else HS.Var () (HS.UnQual () (HS.Ident () ((head ns) ^. _1)))
replaceInfixViewE exp depth vars = exp


mkVar :: String -> HS.Exp ()
mkVar = var . mkName

mkOp :: String -> HS.QOp ()
mkOp = op . mkName


-- | Builder the actual lens view infix expression 
-- -----------------------------------------------------------------------
-- | @varToView@ is the var that the view transform is being applied to
-- | @tag@ is the kind of type the view is being built for
-- | @prev@ previous expression, which is the tail rec var being built up
-- | @accessor@ the actual variable we want to view 
-- ----------------------------------------------------------------------------------------------------
mkViewInfixE :: String -> GroupTag -> Maybe (HS.Exp ()) -> String -> HS.Exp ()
mkViewInfixE varToView tag prev accessor
    = let viewE = case tag of
                    HsVariant -> mkOp "^?"
                    HsMaybe -> mkOp "^?"
                    HsCollection -> mkOp "^.."
                    HsList -> mkOp "^.."
                    _ -> mkOp "^."
        in case prev of
             Just x -> let (op, x') = case tag of 
                                HsCollection -> ("^..", paren x)
                                HsList -> ("^..",  paren x)
                                _ -> (".", x)
                        in infixApp x' (mkOp op) $ mkVar accessor
             Nothing -> infixApp (mkVar varToView) viewE $ mkVar accessor

mkLens :: String -> HS.Decl ()
mkLens t
    = let fname = if | any (==head t) ['R', 'C'] -> "makeLenses"
                     | head t == 'V' -> "makePrisms"
                     | otherwise -> "undefined"
       in HS.SpliceDecl () $ app (function fname) (HS.TypQuote () (HS.UnQual () (mkName t)))


-- | Builder for the lens view expression that extracts the fields from complex types
-- -----------------------------------------------------------------------
-- | @layout@ is a tree like structure containing info about the layout of fields in a constructor
-- | @varToView@ is the var that the view transform is being applied to
-- | @prevGroup@ is the previous kind of type, which is essentially what type are we in right now in the recursion
-- | @prev@ previous expression, which is the tail rec var being built up
mkLensView :: HsEmbedLayout -> String -> GroupTag -> Maybe (HS.Exp ()) -> [((String, HS.Exp ()), (HS.Type (), GroupTag))]
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

mkLensView' :: HsFFILayout -> String -> GroupTag -> Maybe (HS.Exp ()) -> [((String, HS.Exp ()), (HS.Type (), GroupTag))]
mkLensView' layout varToView prevGroup prev
    = let hsTy = layout ^. cTyp
          group =  layout ^. groupTag
          fld = layout ^. cFieldMap
       in concatMap ( \(k, v) 
            -> let n = k
                   (cTyCon:cTyParams,ptrCon) = partition (\x -> all (/= getConIdentName x) ["Ptr", "IO"]) $ unfoldFFITy hsTy
                   name = getConIdentName cTyCon
                   vv = if null ptrCon then varToView else mkKIdentVarBind varToView name 0
                 in case v of
           (Left depth) -> let e = fromMaybe (mkVar vv) prev 
                             in [ ( ( n
                                    , e & (mkFromIntegral hsTy prevGroup) ) 
                                  , (hsTy, prevGroup) ) ]
           (Right next) -> mkLensView' next varToView group $ Just $ mkViewInfixE vv group prev k
       ) $ M.toList $ fld


mkFromIntegral :: HS.Type () -> GroupTag -> HS.Exp () -> HS.Exp ()
mkFromIntegral ty group prev =
    if isFromIntegral ty 
    then infixApp prev (mkRevAppOp group) (function "fromIntegral") 
    else prev
    where mkRevAppOp x = case x of 
                        HsVariant -> mkOp "<&>"
                        _ -> mkOp "&"

isFromIntegral :: HS.Type () -> Bool
isFromIntegral (HS.TyCon _ (HS.UnQual _ (HS.Ident _ n)))
    = n `elem` ["Word8","Word16","Word32","Word64"]
isFromIntegral _ = False

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
                                             (HS.TyCon _ (HS.UnQual _ (HS.Ident _ n))) -> [n]
                                             _ -> []
        ) $ M.toList fld

getConNames' :: HsFFILayout -> [String] -> [String]
getConNames' tyL acc
    = let hsTy = tyL ^. cTyp
          ty = tyL ^. groupTag
          fld = tyL ^. cFieldMap
        in concatMap (\(k,v)
            -> let n = k
                   (cTyCon:cTyParams,ptrCon) = partition (\x -> all (/= getConIdentName x) ["Ptr", "IO"]) $ unfoldFFITy hsTy
                   name = getConIdentName cTyCon
                 in case v of
            Left _ -> acc
            Right next -> getConNames' next $ acc ++ if null ptrCon then [] else [name]
        ) $ M.toList fld
