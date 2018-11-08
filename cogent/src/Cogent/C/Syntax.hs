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
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}

-- | Most of the abstract syntax is derived from Absyn.ML in c-parser.
--   Currently we just implement the smallest set used in our CG.
--   This AST is used as a simpler intermediate representation between the Cogent
--   Core language and the verbose C syntax as defined in language-c-quote.

module Cogent.C.Syntax (
  module Cogent.C.Syntax
, C.BinOp (..), C.UnOp (..)
) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Core           as CC
import           Data.Nat            as Nat

import Data.Map as M
import qualified "language-c-quote" Language.C as C

type CId = String

data CIntType = CCharT | CShortT | CIntT | CLongT | CLongLongT
              deriving (Eq, Ord, Show)

data CArraySize = CArraySize CExpr
                | CNoArraySize
                | CPtrToArray
                deriving (Eq, Ord, Show)

-- The type parameter has been striped off
data CType = CInt Bool CIntType      -- ^ 'True' is signed
           | CogentPrim  PrimInt     -- ^ add Cogent primitive types
           | CBool  -- ^ __NOTE:__ this should be the same as Cogent boolean (could be used interchangeably)
           | CChar
           | CStruct CId
           | CUnion (Maybe CId) (Maybe [(CType, CId)])  -- ^ made specifically for @--funion-for-variants@
           | CEnum CId
           | CPtr CType
           | CArray CType CArraySize
           -- \ | CBitfield Bool c  -- True for signed field
           | CIdent CId
           | CFunction CType CType
           | CVoid
           deriving (Eq, Ord, Show)

data Radix = BIN | OCT | DEC | HEX
              deriving (Eq, Ord, Show)

data CLitConst = CNumConst Integer CType Radix
               | CCharConst Char
               | CStringConst String
               deriving (Eq, Ord, Show)

data CExpr = CBinOp CBinOp CExpr CExpr
           | CUnOp  CUnOp CExpr
           | CCondExpr CExpr CExpr CExpr
           | CConst CLitConst
           | CVar CId (Maybe CType)
           | CStructDot CExpr CId
           | CArrayDeref CExpr CExpr
           | CDeref CExpr
           | CAddrOf CExpr
           | CTypeCast CType CExpr
           | CSizeof   CExpr
           | CSizeofTy CType
           | CEFnCall CExpr [CExpr]
           | CCompLit CType [([CDesignator], CInitializer)]
           -- \ | CArbitrary (CType CExpr)
           | CMKBOOL CExpr
           deriving (Eq, Ord, Show)


data CInitializer = CInitE CExpr
                  | CInitList [([CDesignator], CInitializer)]
                  deriving (Eq, Ord, Show)


data CDesignator = CDesignE CExpr
                 | CDesignFld CId
                 deriving (Eq, Ord, Show)

type CBinOp    = C.BinOp
type CUnOp     = C.UnOp

-- data CTrappable = CBreakT | CContinueT

data CStmt = CAssign CExpr CExpr
           | CAssignFnCall (Maybe CExpr) CExpr [CExpr]  -- ^ lval, fn, args
           -- \ | CChaos     CExpr
           -- \ | CEmbFnCall CExpr CExpr [CExpr] -- lval, fn, args
           | CBlock [CBlockItem]
           | CWhile CExpr CStmt  -- ^ elide @string wrap option@
           -- \ | CTrap CTrappable CStmt
           | CReturn (Maybe CExpr)
           | CReturnFnCall CExpr [CExpr]
           | CBreak
           | CContinue
           | CIfStmt CExpr CStmt CStmt
           | CSwitch CExpr [(Maybe CExpr, CStmt)]  -- simplified
           | CEmptyStmt
           -- elide `Auxupd' `Ghostupd' `Spec' and `AsmStmt'
           -- \ | CLocalInit CExpr
           | CComment String CStmt  -- to accommodate comments
           deriving (Show)

data CBlockItem = CBIStmt CStmt
                | CBIDecl (CDeclaration IND)
                deriving (Show)

data FnSpec = FnSpec [Storage] [TypeQual] [GccAttrs] deriving (Eq, Show)

noFnSpec = FnSpec [] [] []
staticInlineFnSpec = FnSpec [STStatic] [TQInline] []

data Storage  = STStatic | STRegister | STAuto   | STExtern   deriving (Eq, Show)
data TypeQual = TQConst  | TQVolatile | TQInline | TQRestrict deriving (Eq, Show)
data GccAttrs = GccAttrs [GccAttr] deriving (Eq, Show)
data GccAttr  = GccAttr String [CExpr] deriving (Eq, Show)

-- | internal decl
data IND
-- | external decl
data EXD

data CDeclaration d where
  -- | elide @gcc_attribute list@; 'True' if __NOT__ @extern@
  CVarDecl    :: CType -> CId -> Bool -> Maybe CInitializer -> CDeclaration d
  -- | add 'Maybe' for @--funion-for-variants@
  CStructDecl :: CId -> [(CType, Maybe CId)] -> CDeclaration EXD
  -- | change @[(t, v)] -> ...@ to @t -> [v] -> ...@
  CTypeDecl   :: CType -> [CId] -> CDeclaration EXD
  CExtFnDecl  :: { retType :: CType,
                   name    :: CId,
                   params  :: [(CType, Maybe CId)] ,
                   specs   :: FnSpec } -> CDeclaration EXD
  CEnumDecl   :: Maybe CId -> [(CId, Maybe CExpr)] -> CDeclaration EXD
deriving instance Show (CDeclaration d)

data CExtDecl = CFnDefn (CType, CId) [(CType, CId)] [CBlockItem] FnSpec
              | CDecl (CDeclaration EXD)
              | CMacro String
              | CFnMacro CId [CId] [CBlockItem]
              deriving (Show)


-- | 'StrlType' tried to unify some of the types we have in Core.
--   It can be deemed as the C representation for Cogent types.
data StrlType = Record  [(CId, CType)]       -- ^ @(fieldname &#x21A6; fieldtype)@
              | BoxedRecord (CC.Type 'Zero)
                -- ^ Depends on the Cogent type of the record, so that different boxed cogent records
                --   get given different StrlTypes and thus different CTypes.
                --   The CType will always be a struct with a single field
                --   named 'data' of type 'unsigned int *'.
              | Product CType CType          -- ^ pair
              | Variant (M.Map CId CType)    -- ^ one tag field, and fields for all possibilities
              | Function CType CType
              | AbsType CId
              | Array CType (Maybe Int)
              deriving (Eq, Ord, Show)

