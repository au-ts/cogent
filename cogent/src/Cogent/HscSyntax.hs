--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


module Cogent.HscSyntax where

-- NOTE: This syntax is meant to be kept simple, rather than complete. / zilinc


data HscModule = HscModule [ModulePragma] ModuleName [Declaration]


data ModulePragma = LanguagePragma String

data Declaration = HsDecl HsDecl | HscDecl HscDecl

data HsDecl = DataDecl TypeName [TyVarName] [DataCon]
            | TypeDecl TypeName [TyVarName] Type
            | InstDecl ClassName [Context] Type [FuncBinding]

data Context = Context ClassName Type

data FuncBinding = FuncBinding VarName [Pattern] Expression

data Pattern = PVar VarName
             | PCon ConsName [Pattern]

data Expression = EVar VarName
                | EDo  [DoBinding]
                | EOp OpName [Expression]
                | ECon ConsName [Expression]
                | EApp Expression [Expression]
                | EAbs [Pattern] Expression
                | ELet [FuncBinding] Expression
                | EHsc HscSymbol Expression
                | ETuple [Expression]

data HscSymbol = HscPeek | HscPoke | HscSize | HscAlignment

data DoBinding = DoBinding [Pattern] Expression


data DataCon = DataCon ConsName [(FieldName, Type)]


data Type = Type ConsName [Type]
          | TyVar TyVarName

data HscDecl = HashInclude String | HaskEnum TypeName ConsName [TagName]

type ModuleName = String
type VarName    = String
type OpName     = String
type TyVarName  = String
type TypeName   = String
type ConsName   = String
type ClassName  = String
type FieldName  = String
type TagName    = String



