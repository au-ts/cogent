module Cogent.LLVM.CHeader (createCHeader) where

-- This module attempts to create a header file so the LLVM code can be compiled
-- along with C code
-- We should reuse the existing .h file generation but this is simpler for now

import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types (PrimInt (..), Sigil (Boxed, Unboxed))
import Cogent.Core as Core (Definition (FunDef), Type (..), TypedExpr)
import Data.Char (toUpper)
import Data.List (intercalate, sort)

-- This is particularly horrifying
type CExpr = String
type CType = String
type CCode = String

-- Don't use the normal <cogent-defs.h>
cogentTypes :: [CExpr]
cogentTypes =
    [ typeDef "unsigned char" "u8"
    , typeDef "unsigned short" "u16"
    , typeDef "unsigned int" "u32"
    , typeDef "unsigned long long" "u64"
    , typeDef "u8" "bool"
    , typeDef "u8" "unit"
    , ""
    ]

-- Convert to a C type name
toCType :: Core.Type t b -> CType
toCType (TPrim p) = case p of
    U8 -> "u8"
    U16 -> "u16"
    U32 -> "u32"
    U64 -> "u64"
    Boolean -> "bool"
toCType TUnit = "unit"
toCType TString = "char*"
toCType (TRecord _ ts Unboxed) = "struct { " ++ concatMap toCField ts ++ "}"
toCType (TRecord r ts (Boxed _ _)) = toCType (TRecord r ts Unboxed) ++ "*"
toCType (TSum ts) =
    "struct { enum { "
        ++ intercalate "," (sort $ fst <$> ts)
        ++ " } tag; union { "
        ++ concatMap toCField ts
        ++ "} val; }"
toCType _ = error "not implemented"

-- Fields go inside struct or union definitions
toCField :: (String, (Core.Type t b, Bool)) -> CExpr
toCField (n, (t, _)) = toCType t ++ " " ++ n ++ "; "

toCDef :: Core.Definition TypedExpr VarName VarName -> [CExpr]
toCDef (FunDef _ name _ _ t rt _) =
    [ typeDef (toCType t) arg
    , typeDef (toCType rt) ret
    , ret ++ " " ++ name ++ "(" ++ arg ++ ")" ++ ";"
    , ""
    ]
    where
        arg = name ++ "_arg"
        ret = name ++ "_ret"
toCDef _ = []

typeDef :: CType -> String -> CExpr
typeDef t i = unwords ["typedef", t, i] ++ ";"

-- Wrap other expressions in a #include guarad
createHeaderGuard :: [CExpr] -> String -> [CExpr]
createHeaderGuard exprs filename =
    [ "#ifndef " ++ h ++ "_H__"
    , "#define " ++ h ++ " _H__"
    , ""
    ]
        ++ exprs
        ++ ["#endif"]
    where
        h = toUpper <$> filename

createCHeader :: [Core.Definition TypedExpr VarName VarName] -> String -> CCode
createCHeader defs filename =
    unlines $
        createHeaderGuard
            (cogentTypes ++ concatMap toCDef defs)
            filename
