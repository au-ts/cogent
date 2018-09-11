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
  hscModule
) where

import Cogent.C.Compile
import Cogent.C.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Haskell.HscSyntax as Hsc
import Cogent.Util

import Data.List as L
import Data.Maybe (catMaybes, fromJust)

hscModule :: String -> String -> [CExtDecl] -> [CExtDecl] -> Hsc.HscModule
hscModule name cname ctys cenums =
  Hsc.HscModule pragmas name $
    imports ++
    include ++
    L.intersperse Hsc.EmptyDecl (catMaybes (map hscEnum cenums ++ map hscTyDecl ctys ++ map hscStorageInst ctys))
  where pragmas = map Hsc.LanguagePragma [ "DisambiguateRecordFields"
                                         , "DuplicateRecordFields"
                                         , "ForeignFunctionInterface"
                                         , "GeneralizedNewtypeDeriving" ]
        imports = map Hsc.HsDecl 
                    [ Hsc.ImportDecl "Foreign" False Nothing [] []
                    , Hsc.ImportDecl "Foreign.Ptr" False Nothing [] []
                    , Hsc.ImportDecl "Foreign.C.String" False Nothing [] []
                    , Hsc.ImportDecl "Foreign.C.Types" False Nothing [] []
                    , Hsc.ImportDecl "Util" False Nothing [] [] ]
                  ++ [Hsc.EmptyDecl]
        include = [Hsc.HscDecl $ Hsc.HashInclude cname, Hsc.EmptyDecl]

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
hscTag (n, me) = (n, fmap hscExpr me)

hscExpr :: CExpr -> Hsc.Expression
hscExpr (CConst (CNumConst i _ DEC)) = Hsc.ELit $ Hsc.LitInt i
hscExpr _ = __todo "hscExpr: other expressions have not been implemented"

hscTyDecl :: CExtDecl -> Maybe Hsc.Declaration
hscTyDecl (CDecl (CStructDecl n flds)) = Just . Hsc.HsDecl $ Hsc.DataDecl (toHscName n) [] [Hsc.DataCon (toHscName n) $ flds']
  where flds' = map (\(t, Just f) -> (decap f, hscType t)) flds  -- TODO: it does not support --funion-for-variants yet
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
hscType (CIdent tn) = Hsc.TyCon (toHscName tn) []
hscType (CFunction t1 t2) = __todo "hscType: c function types"
hscType (CVoid) = __impossible "hscType: void type shouldn't appear"  -- Hsc.TyTuple []

hscPrimType :: PrimInt -> Hsc.Type
hscPrimType Boolean = Hsc.TyCon (toHscName boolT) []
hscPrimType t = Hsc.TyCon (toHscName $ primCId t) []

hscPtr = "ptr"

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
        pokeField (_, Just cid) = Hsc.DoBind [] $ Hsc.EApp (Hsc.EHsc Hsc.HashPoke [n, cid]) [Hsc.EVar hscPtr, Hsc.EVar cid]
        pokeField _ = __todo "pokeField: no support for --funion-for-variants yet"
hscStorageInst _ = Nothing


