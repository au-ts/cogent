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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

-- | This modules renders C code from the intermediate C AST.

module Cogent.C.Render where

import Cogent.C.GenState (primCId)
import Cogent.C.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Util

import Control.Arrow (second, (***))
import Data.Char (isAlphaNum, toUpper)
import Data.List as L
import Data.Loc (noLoc)
import Data.Monoid ((<>))
import qualified "language-c-quote" Language.C as C
import Language.C.Quote.C
import "language-c-quote" Language.C.Syntax ()
import Text.PrettyPrint.Mainland
#if MIN_VERSION_mainland_pretty(0,6,0)
import Text.PrettyPrint.Mainland.Class
#endif


render :: FilePath
       -> [CExtDecl]
       -> [CExtDecl]
       -> String
       -> ([C.Definition], [C.Definition])
render hName hdefns cdefns log =
  let guard = L.map (\c -> if not (isAlphaNum c) then '_' else toUpper c) hName ++ "__"  -- guard name
      hfile = L.map (\l -> C.EscDef ("// " ++ l) noLoc) (lines log) ++
              C.EscDef "" noLoc :
              C.EscDef ("#ifndef " ++ guard) noLoc :
              C.EscDef ("#define " ++ guard ++ "\n") noLoc :
              C.EscDef ("#include <cogent-defns.h>\n") noLoc :
              map cExtDecl hdefns ++
              -- \ ^^^ Type synonyms shouldn't be referenced to by gen'ed C code;
              -- Gen'ed C only uses machine gen'ed type names and abstract type names
              [C.EscDef ("#endif") noLoc]
      cfile = L.map (\l -> C.EscDef ("// " ++ l) noLoc) (lines log) ++
              C.EscDef "" noLoc :
              C.EscDef ("#include \"" ++ hName ++ "\"\n") noLoc :
              map cExtDecl cdefns
   in (hfile, cfile)

#if MIN_VERSION_language_c_quote(0,11,2)
#else
instance IsString C.Id where
  fromString = flip C.Id noLoc
#endif


cId :: CId -> C.Id
cId v = toIdent (toCName v) noLoc

cType :: CType -> C.Type
cType ty = let (dcsp, decl) = splitCType ty in C.Type dcsp decl noLoc

cFieldGroup :: CType -> C.FieldGroup
cFieldGroup (CUnion Nothing (Just flds)) =
  C.FieldGroup (C.DeclSpec [] [] (C.Tunion Nothing (Just $ cFieldGroups $ map (second Just) flds) [] noLoc) noLoc) [] noLoc
cFieldGroup _ = __impossible "cFieldGroup"

cInitializer :: CInitializer -> C.Initializer
cInitializer (CInitE e) = [cinit| $(cExpr e) |]
cInitializer (CInitList dis) = C.CompoundInitializer (map cDesignatedInitr dis) noLoc

cFieldGroups :: [(CType, Maybe CId)] -> [C.FieldGroup]
cFieldGroups = map (\(ty, mf) -> case mf of
                      Just f  -> [csdecl| $ty:(cType ty) $id:(cId f); |]
                      Nothing -> cFieldGroup ty)

isCTypeSigned :: CType -> Bool
isCTypeSigned (CInt s _) = s
isCTypeSigned (CogentPrim _) = False
isCTypeSigned _ = True  -- FIXME

cLitConst :: CLitConst -> C.Exp
cLitConst (CNumConst n (isCTypeSigned -> False) DEC) | n < 65536 = [cexp| $uint:n |]
                                                     | n < 4294967296 = [cexp| $ulint:n |]
                                                     | otherwise = [cexp| $ullint:n |]
cLitConst (CNumConst n s DEC) | n < 65536 = [cexp| $int:n |]
                              | n < 4294967296 = [cexp| $lint:n |]
                              | otherwise = [cexp| $llint:n |]
cLitConst (CNumConst {}) = __impossible "cLitConst"  -- NOTE: currently we parse everything to its decimal form / zilinc
cLitConst (CCharConst c) = [cexp| $char:c |]
cLitConst (CStringConst s) = [cexp| $string:s |]

cDesignator :: CDesignator -> C.Designator
cDesignator (CDesignE e) = C.IndexDesignator (cExpr e) noLoc
cDesignator (CDesignFld fn) = C.MemberDesignator (cId fn) noLoc

cDesignators :: [CDesignator] -> Maybe C.Designation
cDesignators [] = Nothing
cDesignators ds = Just $ C.Designation (map cDesignator ds) noLoc

cDesignatedInitr :: ([CDesignator], CInitializer) -> (Maybe C.Designation, C.Initializer)
cDesignatedInitr = cDesignators *** cInitializer

cExpr :: CExpr -> C.Exp
cExpr (CBinOp opr e1 e2) = C.BinOp opr (cExpr e1) (cExpr e2) noLoc
cExpr (CUnOp opr e) = C.UnOp opr (cExpr e) noLoc
cExpr (CCondExpr c e1 e2) = [cexp| $(cExpr c) ? $(cExpr e1) : $(cExpr e2) |]
cExpr (CConst lit) = cLitConst lit
cExpr (CVar v _) = [cexp| $id:(cId v) |]
cExpr (CStructDot e f) = [cexp| $(cExpr e).$id:(cId f) |]
cExpr (CArrayDeref e i) = [cexp| $(cExpr e)[$(cExpr i)] |]
cExpr (CDeref e) = [cexp| (* $(cExpr e)) |]
cExpr (CAddrOf e) = [cexp| (& $(cExpr e)) |]
cExpr (CTypeCast ty e) = [cexp| ($ty:(cType ty)) $(cExpr e) |]
cExpr (CSizeof e) = [cexp| sizeof ($(cExpr e)) |]
cExpr (CSizeofTy ty) = [cexp| sizeof ($ty:(cType ty)) |]
cExpr (CEFnCall fn args) = [cexp| $(cExpr fn) ($args:(map cExpr args)) |]
cExpr (CCompLit ty dis) = C.CompoundLit (cType ty) (map cDesignatedInitr dis) noLoc  -- cannot add another pair of parens
cExpr (CMKBOOL e) = [cexp| $(cExpr e) != 0 |]

mkDeclSpec :: C.TypeSpec -> C.DeclSpec
mkDeclSpec tysp = C.DeclSpec [] [] tysp noLoc

cSign :: Bool -> C.Sign
cSign True  = C.Tsigned   noLoc
cSign False = C.Tunsigned noLoc

splitCType :: CType -> (C.DeclSpec, C.Decl)
splitCType (CInt signed intTy) = (,) (case intTy of
  CCharT     -> mkDeclSpec $ C.Tchar      (Just $ cSign signed) noLoc;
  CShortT    -> mkDeclSpec $ C.Tshort     (Just $ cSign signed) noLoc;
  CIntT      -> mkDeclSpec $ C.Tint       (Just $ cSign signed) noLoc;
  CLongT     -> mkDeclSpec $ C.Tlong      (Just $ cSign signed) noLoc;
  CLongLongT -> mkDeclSpec $ C.Tlong_long (Just $ cSign signed) noLoc) (C.DeclRoot noLoc)
splitCType (CogentPrim pt) = (mkDeclSpec $ C.Tnamed (C.Id (primCId pt) noLoc) [] noLoc, C.DeclRoot noLoc)
splitCType CBool = (mkDeclSpec $ C.Tnamed "Bool" [] noLoc, C.DeclRoot noLoc)
splitCType CChar = (mkDeclSpec $ C.Tchar Nothing noLoc, C.DeclRoot noLoc)
splitCType (CStruct tid) = (mkDeclSpec $ C.Tstruct (Just $ cId tid) Nothing [] noLoc, C.DeclRoot noLoc)
splitCType (CUnion {}) = __impossible "splitCType"
splitCType (CEnum tid) = (mkDeclSpec $ C.Tenum (Just $ cId tid) [] [] noLoc, C.DeclRoot noLoc)
splitCType (CPtr ty) = let (tysp, decl) = splitCType ty in (tysp, C.Ptr [] decl noLoc)
splitCType (CArray t msize)
  | CPtrToArray <- msize = 
      let (C.DeclSpec _ _ tsp _,dl) = splitCType t
       in (mkDeclSpec tsp, C.Ptr [] dl noLoc)
  | otherwise =
      let arrsize = case msize of
            CNoArraySize -> C.NoArraySize noLoc
            CArraySize sz -> C.ArraySize False (cExpr sz) noLoc  -- True will print `static sz'.
          (C.DeclSpec _ _ tsp _,dl) = splitCType t
       in (mkDeclSpec tsp, C.Array [] arrsize dl noLoc)
splitCType (CIdent tn) = (mkDeclSpec $ C.Tnamed (cId tn) [] noLoc, C.DeclRoot noLoc)
splitCType (CFunction t1 t2) = __fixme $ splitCType t2  -- FIXME: this type is rarely used and is never tested / zilinc
splitCType CVoid = (mkDeclSpec $ C.Tvoid noLoc, C.DeclRoot noLoc)

cFnSpecOnDeclSpec :: FnSpec -> C.DeclSpec -> C.DeclSpec
cFnSpecOnDeclSpec (FnSpec stg qual attr) (C.DeclSpec stg' qual' tysp loc) =
  C.DeclSpec (stg' ++ L.map cStorage stg) (qual' ++ L.map cTypeQual qual ++ L.concatMap cAttrs attr) tysp loc
cFnSpecOnDeclSpec _ decl = decl  -- NOTE: doesn't work for C.AntiDeclSpec / zilinc

cFnSpecOnType :: FnSpec -> C.Type -> C.Type
cFnSpecOnType fnsp (C.Type dcsp decl loc) = C.Type (cFnSpecOnDeclSpec fnsp dcsp) decl loc
cFnSpecOnType _ t = t  -- NOTE: doesn't work for C.AntiType / zilinc

cStorage :: Storage -> C.Storage
cStorage STAuto = C.Tauto noLoc
cStorage STRegister = C.Tregister noLoc
cStorage STStatic = C.Tstatic noLoc
cStorage STExtern = C.Textern Nothing noLoc  -- FIXME: can be extended to support Linkage / zilinc

cTypeQual :: TypeQual -> C.TypeQual
cTypeQual TQConst = C.Tconst noLoc
cTypeQual TQVolatile = C.Tvolatile noLoc
cTypeQual TQInline = C.Tinline noLoc
cTypeQual TQRestrict = C.Trestrict noLoc

cAttrs :: GccAttrs -> [C.TypeQual]
cAttrs (GccAttrs attrs) = L.map cAttr attrs

cAttr :: GccAttr -> C.TypeQual
cAttr (GccAttr n es) = C.TAttr (C.Attr (C.Id n noLoc) (L.map cExpr es) noLoc)

cDeclaration :: CDeclaration d -> C.InitGroup
cDeclaration (CVarDecl ty v ext (Just initr)) = [cdecl| $ty:(cType ty) $id:(cId v) = $init:(cInitializer initr); |]
cDeclaration (CVarDecl ty v ext Nothing) = [cdecl| $ty:(cType ty) $id:(cId v); |]
cDeclaration (CStructDecl tid flds) = [cdecl| struct $id:(cId tid) { $sdecls:(cFieldGroups flds) }; |]
cDeclaration (CTypeDecl ty vs) = let (dcsp, decl) = splitCType ty
                                 in C.TypedefGroup dcsp [] (map (\v -> C.Typedef (cId v) decl [] noLoc) vs) noLoc
cDeclaration (CExtFnDecl rt fn params fnsp) = [cdecl| $ty:(cFnSpecOnType fnsp (cType rt)) $id:(cId fn) ($params:(map cParam' params)); |]
cDeclaration (CEnumDecl mtid eis) =
  C.InitGroup (mkDeclSpec $ C.Tenum (fmap cId mtid) (map (\(ei, me) -> C.CEnum (cId ei) (fmap cExpr me) noLoc) eis) [] noLoc) [] [] noLoc

cParam :: (CType, CId) -> C.Param
cParam (ty, v) = [cparam| $ty:(cType ty) $id:(cId v) |]

cParam' :: (CType, Maybe CId) -> C.Param
cParam' (ty, Nothing) = [cparam| $ty:(cType ty) |]
cParam' (ty, Just v) = cParam (ty, v)

cStmt :: CStmt -> C.Stm
cStmt (CAssign el er) = [cstm| $(cExpr el) = $(cExpr er); |]
cStmt (CAssignFnCall mel er args) = case mel of Nothing -> [cstm| $(cExpr er) ($args:(map cExpr args)); |]
                                                Just el -> [cstm| $(cExpr el) = $(cExpr er) ($args:(map cExpr args)); |]
cStmt (CReturnFnCall f args) = [cstm| return $(cExpr f) ($args:(map cExpr args)); |]
cStmt (CBlock bis) = [cstm| { $items:(map cBlockItem bis) } |]
cStmt (CWhile e s) = [cstm| while ($(cExpr e)) $stm:(cStmt s) |]
cStmt (CReturn me) = case me of Nothing -> [cstm| return; |]; Just e -> [cstm| return $(cExpr e); |]
cStmt CBreak = [cstm| break; |]
cStmt CContinue = [cstm| continue; |]
cStmt (CIfStmt c th el) = [cstm| if ($(cExpr c)) $stm:(cStmt th) else $stm:(cStmt el) |]
cStmt (CSwitch e alts) = [cstm| switch ($(cExpr e)) { $items:(map cAlt alts) } |]
cStmt CEmptyStmt = [cstm| ; |]
cStmt (CComment c s) = C.Comment c (cStmt s) noLoc

cAlt :: (Maybe CExpr, CStmt) -> C.BlockItem
cAlt (Nothing, s) = [citem| default: $stm:(cStmt s) |]
cAlt (Just e , s) = [citem| case $(cExpr e): $stm:(cStmt s) |]

cBlockItem :: CBlockItem -> C.BlockItem
cBlockItem (CBIStmt stmt) = [citem| $stm:(cStmt stmt) |]
cBlockItem (CBIDecl decl) = [citem| $decl:(cDeclaration decl); |]

cExtDecl :: CExtDecl -> C.Definition
cExtDecl (CFnDefn (ty, fn) params bis fnsp) =
  [cedecl| $ty:(cFnSpecOnType fnsp (cType ty)) $id:(cId fn) ($params:(map cParam params)) { $items:(map cBlockItem bis) }|]
cExtDecl (CDecl decl) = [cedecl| $decl:(cDeclaration decl); |]
cExtDecl (CMacro s) = C.EscDef s noLoc
cExtDecl (CFnMacro fn as body) = C.EscDef (string1 ++ "\\\n" ++ string2) noLoc
  where macro1, macro2 :: Doc
        macro1 = string "#define" <+> string fn <> parens (commasep $ L.map string as)
        macro2 = let body' = L.map cBlockItem body in ppr [citems| $items:(body') |]
        string1, string2 :: String
        string1 = L.filter (/= '\n') $ pretty 100 macro1
        string2 = concat $ map (\c -> if c == '\n' then "\\\n" else [c]) $ pretty 100 macro2
