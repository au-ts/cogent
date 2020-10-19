module Cogent.LLVM.CHeader (createCHeader) where

-- This module attempts to create a header file so the LLVM code can be compiled
-- along with C code
-- We should reuse the existing .h file generation but this is simpler for now

import Cogent.Common.Syntax (FunName, VarName)
import Cogent.Common.Types (PrimInt (..), Sigil (Boxed, Unboxed))
import Cogent.Core as Core (Definition (..), Type (..), TypedExpr)
import Control.Monad.State (State, execState, gets, modify)
import Data.Char (toUpper)
import Data.List (intercalate, sort)
import Debug.Trace (traceShowM)

-- Really should be newtype, but adds a lot of complexity
type CType = String
type CIdent = String

-- When generating a header file just keep track of:
--  - unique type definitions
--  - type aliases
--  - function prototypes
data HGen = HGen
    { typeDefs :: [(CType, CIdent)]
    , typeAliases :: [(CIdent, CIdent)]
    , funDefs :: [(CType, CType, CIdent)]
    }

cogentDefs :: [String]
cogentDefs =
    [ "typedef unsigned char u8;"
    , "typedef unsigned short u16;"
    , "typedef unsigned int u16;"
    , "typedef unsigned long long u64;"
    , "typedef u8 bool_t;"
    , "typedef u8 unit_t;"
    , ""
    ]

-- Convert  list of Cogent definitions to a header file
createCHeader :: [Core.Definition TypedExpr VarName VarName] -> String -> String
createCHeader monoed mod =
    let defs = execState (mapM_ define monoed) (HGen [] [] [])
        guard = toUpper <$> mod ++ "_H__"
        ifndef = ["#ifndef " ++ guard, "#define " ++ guard, ""]
        endif = ["", "#endif"]
        ts =
            (\(t, i) -> "typedef " ++ t ++ " " ++ i ++ ";")
                <$> (typeDefs defs ++ typeAliases defs)
        fs =
            (\(t, rt, i) -> rt ++ " " ++ i ++ "(" ++ t ++ ");")
                <$> funDefs defs
     in unlines $ ifndef ++ cogentDefs ++ ts ++ fs ++ endif

-- From a single Cogent definition, emit C definitions
define :: Core.Definition TypedExpr VarName VarName -> State HGen ()
define (FunDef _ name _ _ t rt _) = toCFun name t rt
define (AbsDecl _ name _ _ t rt) = toCFun name t rt
define (TypeDef name _ (Just t)) = toCType t >>= typeAlias name
define _ = pure ()

-- Convert to a C function declaration
toCFun :: FunName -> Core.Type t b -> Core.Type t b -> State HGen ()
toCFun name t rt = do
    arg <- toCType t
    ret <- toCType rt
    modify $ \s -> s {funDefs = (arg, ret, name) : funDefs s}
    typeAlias (name ++ "_arg") arg
    typeAlias (name ++ "_ret") ret

-- Convert to a C type name
toCType :: Core.Type t b -> State HGen CType
toCType (TPrim p) = pure $ case p of
    U8 -> "u8"
    U16 -> "u16"
    U32 -> "u32"
    U64 -> "u64"
    Boolean -> "bool_t"
toCType TUnit = pure "unit_t"
toCType TString = pure "char*"
toCType (TRecord r ts (Boxed _ _)) = (++ "*") <$> toCType (TRecord r ts Unboxed)
toCType (TRecord _ ts Unboxed) =
    toCFields ts
        >>= \fs -> typeDef ("struct { " ++ fs ++ "}")
toCType (TSum ts) = do
    traceShowM $ fst <$> ts
    fs <- toCFields ts
    enum <- typeDef ("enum { " ++ intercalate ", " (sort $ fst <$> ts) ++ " }")
    typeDef ("struct { " ++ enum ++ " tag; union { " ++ fs ++ "} val; }")
toCType (TCon tn ts (Boxed _ _)) = (++ "*") <$> toCType (TCon tn ts Unboxed)
toCType (TCon tn ts Unboxed) =
    (tn ++) . filter (/= '*') <$> (concatMap ("_" ++) <$> mapM toCType ts)
toCType _ = error "not implemented"

-- Conver the fields in a record or variant to C fields
toCFields :: [(String, (Core.Type t b, Bool))] -> State HGen String
toCFields ts =
    concatMap (\((n, _), t) -> t ++ " " ++ n ++ "; ") . zip ts
        <$> mapM (toCType . fst . snd) ts

-- Make a fresh type name
freshType :: State HGen CIdent
freshType = gets ((("t" ++) . show . (+ 1) . length) . typeDefs)

-- Get or define a unique type with a generated or provided name
typeDef :: CType -> State HGen CIdent
typeDef t = do
    types <- gets typeDefs
    case lookup t types of
        Just ident -> pure ident
        Nothing -> do
            ident <- freshType
            modify $ \s -> s {typeDefs = (t, ident) : typeDefs s}
            pure ident

typeAlias :: CIdent -> CType -> State HGen ()
typeAlias n t = modify $ \s -> s {typeAliases = (t, n) : typeAliases s}