--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

-- | Haskell FFI generator
--
-- Generates .hsc files to be compiled by the [hsc2hs](http://hackage.haskell.org/package/hsc2hs) tool


module Cogent.Haskell.HscGen (
  ffiHsc
, hscType
) where

import Cogent.C.GenState (boolT, primCId, tagsT, untypedFuncEnum)
import Cogent.C.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Haskell.HscSyntax as Hsc
import Cogent.Util (decap, toCName)

-- import Control.Monad
import Data.Char (isNumber)
import Data.List as L
-- import qualified Data.Map as M
import Data.Maybe (catMaybes, fromJust)
import qualified Data.Set as S
import qualified Text.PrettyPrint.ANSI.Leijen as P ((<$>))
import Text.PrettyPrint.ANSI.Leijen as P hiding ((<$>))

ffiHsc :: String
       -> [FilePath]
       -> [CExtDecl]
       -> [CExtDecl]
       -> [(TypeName, S.Set [CId])]
       -> [TypeName]
       -> String
       -> Doc
ffiHsc name cnames ctys cenums absts fclsts log =
  text "{-" P.<$> text log P.<$> text "-}" P.<$> 
  pretty (hscModule name cnames ctys cenums absts fclsts)

hscModule :: String
          -> [FilePath]
          -> [CExtDecl]
          -> [CExtDecl]
          -> [(TypeName, S.Set [CId])]
          -> [TypeName]
          -> Hsc.HscModule
hscModule name cnames ctys cenums absts fclsts =
  Hsc.HscModule pragmas name $
    imports ++
    include ++
    L.intersperse Hsc.EmptyDecl (catMaybes (map hscEnum cenums ++
                                            map hscTyDecl ctys ++
                                            map hscStorageInst ctys) ++
                                 map hscEnumTypes fclsts ++
                                 [])  -- concatMap hscTypeDefs absts)
  where pragmas = map Hsc.LanguagePragma [ "DisambiguateRecordFields"
                                         , "DuplicateRecordFields"
                                         , "ForeignFunctionInterface"
                                         , "GeneralizedNewtypeDeriving" ]
        imports = map Hsc.HsDecl 
                    [ Hsc.ImportDecl "Foreign" False Nothing [] []
                    , Hsc.ImportDecl "Foreign.Ptr" False Nothing [] []
                    , Hsc.ImportDecl "Foreign.C.String" False Nothing [] []
                    , Hsc.ImportDecl "Foreign.C.Types" False Nothing [] []
                    , Hsc.ImportDecl "Util" False Nothing [] []
                    , Hsc.ImportDecl hscAbs False Nothing [] [] ]
                  ++ [Hsc.EmptyDecl]
        include = (map (Hsc.HscDecl . Hsc.HashInclude) cnames) ++ [Hsc.EmptyDecl]
        hscAbs = name ++ "_Abs"

hscTagsT = "Tag"
hscUntypedFuncEnum = "FuncEnum"

toHscName = ("C" ++)

hscEnum :: CExtDecl -> Maybe Hsc.Declaration
hscEnum (CDecl (CEnumDecl (Just ((==) tagsT -> True)) ms)) =
  Just . Hsc.HscDecl $ Hsc.HashEnum hscTagsT hscTagsT $ map hscTag ms
hscEnum (CDecl (CEnumDecl (Just ((==) untypedFuncEnum -> True)) ms)) =
  Just . Hsc.HscDecl $ Hsc.HashEnum hscUntypedFuncEnum hscUntypedFuncEnum $ map hscTag ms
hscEnum _ = Nothing

hscTag :: (CId, Maybe CExpr) -> (Hsc.TagName, Maybe Hsc.Expression)
hscTag (n, me) = (toCName n, fmap hscExpr me)

hscExpr :: CExpr -> Hsc.Expression
hscExpr (CConst (CNumConst i _ DEC)) = Hsc.ELit $ Hsc.LitInt i
hscExpr _ = __todo "hscExpr: other expressions have not been implemented"

hscTyDecl :: CExtDecl -> Maybe Hsc.Declaration
hscTyDecl (CDecl (CStructDecl n flds)) = Just . Hsc.HsDecl $ Hsc.DataDecl (toHscName n) [] [Hsc.DataCon (toHscName n) $ flds']
  where flds' = map (\(t, Just f) -> (decap f, hscType t)) flds
  -- \ ^ TODO: it does not support --funion-for-variants yet
hscTyDecl _ = Nothing

hscType :: CType -> Hsc.Type
hscType (CInt signed intt) = Hsc.TyCon (toHscName $ s signed $ i intt) []
  where s True = id; s False = ('U':)
        i CCharT  = "Char"
        i CShortT = "Short"
        i CIntT   = "Int"
        i CLongT  = "Long"
        i CLongLongT = "LLong"
hscType (CogentPrim pt) = hscPrimType pt
hscType (CBool) = Hsc.TyCon (toHscName boolT) []
hscType (CChar) = Hsc.TyCon "CChar" []
hscType (CStruct tn) = Hsc.TyCon (toHscName tn) []
hscType (CUnion {}) = __todo "hscType: c union types"
hscType (CEnum tn) = Hsc.TyCon (toHscName tn) []
hscType (CPtr t) = Hsc.TyCon "Ptr" [hscType t]
hscType (CArray t _) = Hsc.TyCon "Ptr" [hscType t]
hscType (CIdent tn) = Hsc.TyCon (toHscName tn) []
hscType (CFunction t1 t2) = __todo "hscType: c function types"
hscType (CVoid) = __impossible "hscType: void type shouldn't appear"  -- Hsc.TyTuple []

hscPrimType :: PrimInt -> Hsc.Type
hscPrimType Boolean = Hsc.TyCon (toHscName boolT) []
hscPrimType t = Hsc.TyCon (toHscName $ primCId t) []

hscPtr = "ptr"

-- NOTE: parametric abstract types are defined monomorphically, thus there's
--       no point in generating type synonyms for them. They should be derived
--       from the .ah files, which could be quite tricky to do. / zilinc
{-
hscTypeDefs :: (TypeName, S.Set [CId]) -> [Hsc.Declaration]
hscTypeDefs _ = []
hscTypeDefs (tn, insts) = flip L.map (S.toList insts) $ \ts ->
    let tn' = toHscName $ tn ++ "_" ++ L.intercalate "_" ts
        ty  = TyCon (toHscName tn) (map (flip TyCon [] . trim) ts)
     in HsDecl (TypeDecl tn' [] ty)
  where 
        -- This function is very hacky! / zilinc
        trim [] = __impossible "trim: empty constructor name"
        trim n@('u':n':_) | isNumber n' = toHscName n  -- primitive types
        trim   ('u':ns) = toHscName ns
        trim n = toHscName n
-}

hscEnumTypes :: TypeName -> Hsc.Declaration
hscEnumTypes tn = HsDecl $ TypeDecl (toHscName tn) [] (TyCon "Int" [])

-- | generate 'Foreign.Storable.Storable' instances
hscStorageInst :: CExtDecl -> Maybe Hsc.Declaration
hscStorageInst (CDecl (CStructDecl n flds)) = Just . Hsc.HsDecl $ Hsc.InstDecl "Storable" [] (Hsc.TyCon (toHscName n) []) bindings
  where bindings = [sizeof, alignement, peek, poke]
        sizeof = Hsc.Binding "sizeOf" [Hsc.PUnderscore] $ Hsc.EHsc Hsc.HashSize [n]
        alignement = Hsc.Binding "alignment" [Hsc.PUnderscore] $ Hsc.EHsc Hsc.HashAlignment [n]
        peek = Hsc.Binding "peek" [Hsc.PVar hscPtr] $ Hsc.EApplicative (Hsc.ECon (toHscName n) []) peekFields
        peekFields = map peekField flds
        peekField (_, Just cid) = Hsc.EApp (Hsc.EHsc Hsc.HashPeek [n, cid]) [Hsc.EVar hscPtr]
        peekField _ = __todo "peekField: no support for --funion-for-variants yet"
        poke = Hsc.Binding "poke" [Hsc.PVar hscPtr, Hsc.PCon (toHscName n) fnames] $ Hsc.EDo pokeFields
        fnames = map (Hsc.PVar . decap . fromJust . snd) flds
        pokeFields = map pokeField flds
        pokeField (_, Just cid) = Hsc.DoBind [] $ Hsc.EApp (Hsc.EHsc Hsc.HashPoke [n, cid]) [Hsc.EVar hscPtr, Hsc.EVar (decap cid)]
        pokeField _ = __todo "pokeField: no support for --funion-for-variants yet"
hscStorageInst _ = Nothing


