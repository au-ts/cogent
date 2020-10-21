--
-- Copyright 2020, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

module Cogent.LLVM.CHeader (createCHeader) where

-- This module attempts to create a header file so the LLVM code can be compiled
-- along with C code
-- We might be able to reuse the existing .h file generation but this is
-- simpler for now

import Cogent.Common.Syntax (FunName, TagName, VarName)
import Cogent.Common.Types (PrimInt (..), Sigil (Boxed, Unboxed))
import Cogent.Core as Core (Definition (..), Type (..), TypedExpr)
import Cogent.Util (toCName)
import Control.Monad.State (State, execState, gets, modify)
import Data.Bifunctor (Bifunctor (first))
import Data.Char (toUpper)
import Data.List (intercalate)

-- Instead of using strings for everything it would be wiser to use quasiquoted C or something
type CType = String
type CIdent = String
data TypeDef = Fn CType CType | Ty CType deriving (Eq)

-- When generating a header file just keep track of:
--  - unique type definitions
--  - type aliases
--  - function prototypes
--  - function type typedefs
data HGen = HGen
    { typeDefs :: [(TypeDef, CIdent)]
    , typeAliases :: [(CIdent, CIdent)]
    , funProtos :: [(CType, CType, CIdent)]
    }

-- Convert  list of Cogent definitions to a header file
createCHeader :: [Core.Definition TypedExpr VarName VarName] -> String -> [TagName] -> String
createCHeader monoed mod tags =
    let defs = execState (mapM_ define monoed) (HGen [] [] [])
        guard = toUpper <$> mod ++ "_H__"
        ifndef = ["#ifndef " ++ guard, "#define " ++ guard]
        cogentDefs = ["#include <cogent-llvm-defns.h>"]
        endif = ["#endif"]
        tag_enum = ["typedef enum { " ++ intercalate ", " tags ++ " } tag_t;"]
        ts =
            ( \(t, i) ->
                "typedef "
                    ++ ( case t of
                            Ty t -> t ++ " " ++ i ++ ";"
                            Fn t rt -> rt ++ "(*" ++ i ++ ")(" ++ t ++ ");"
                       )
            )
                <$> (reverse (typeDefs defs) ++ (first Ty <$> typeAliases defs))
        fs =
            (\(t, rt, i) -> rt ++ " " ++ i ++ "(" ++ t ++ ");")
                <$> funProtos defs
     in unlines $ intercalate [""] [ifndef, cogentDefs, tag_enum, ts, fs, endif]

-- From a single Cogent definition, emit C definitions
define :: Core.Definition TypedExpr VarName VarName -> State HGen ()
define (FunDef _ name _ _ t rt _) = toCProto name t rt
define (AbsDecl _ name _ _ t rt) = toCProto name t rt
define (TypeDef name _ (Just t)) = toCType t >>= typeAlias (toCName name) . filter (/= '*')
define _ = pure ()

-- Convert to a C function prototype
toCProto :: FunName -> Core.Type t b -> Core.Type t b -> State HGen ()
toCProto name t rt = do
    arg <- toCType t
    ret <- toCType rt
    let cName = toCName name
    modify $ \s -> s {funProtos = (arg, ret, cName) : funProtos s}
    typeAlias (cName ++ "_arg") arg
    typeAlias (cName ++ "_ret") ret

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
        >>= \fs -> typeDef $ Ty $ "struct { " ++ fs ++ "}"
toCType (TSum ts) = do
    fs <- toCFields ts
    typeDef $ Ty $ "struct { tag_t tag; union { " ++ fs ++ "} val; }"
toCType (TCon tn ts (Boxed _ _)) = (++ "*") <$> toCType (TCon tn ts Unboxed)
toCType (TCon tn ts Unboxed) =
    (tn ++) . filter (/= '*') <$> (concatMap ("_" ++) <$> mapM toCType ts)
toCType (TFun t rt) = do
    t' <- toCType t
    rt' <- toCType rt
    typeDef $ Fn t' rt'
toCType _ = error "not implemented"

-- Conver the fields in a record or variant to C fields
toCFields :: [(String, (Core.Type t b, Bool))] -> State HGen String
toCFields ts =
    concatMap (\((n, _), t) -> t ++ " " ++ toCName n ++ "; ") . zip ts
        <$> mapM (toCType . fst . snd) ts

-- Get or define a unique type with a generated name
-- Two structurally equal types should have the same name
typeDef :: TypeDef -> State HGen CIdent
typeDef t = do
    types <- gets typeDefs
    case lookup t types of
        Just ident -> pure ident
        Nothing -> do
            ident <- gets (((prefix t ++) . show . (+ 1) . length) . typeDefs)
            modify $ \s -> s {typeDefs = (t, ident) : typeDefs s}
            pure ident

-- What to start type identifiers with
prefix :: TypeDef -> CIdent
prefix Ty {} = "t"
prefix Fn {} = "f"

-- Define a type alias
-- It's fine for the same type to have multiple aliases
typeAlias :: CIdent -> CType -> State HGen ()
typeAlias n t = modify $ \s -> s {typeAliases = (t, n) : typeAliases s}
