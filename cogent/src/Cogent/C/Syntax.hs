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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}

-- | Most of the abstract syntax is derived from Absyn.ML in c-parser.
--   Currently we just implement the smallest set used in our CG.
--   This AST is used as a simpler intermediate representation between the Cogent
--   Core language and the verbose C syntax as defined in language-c-quote.

module Cogent.C.Syntax (
  module Cogent.C.Syntax
, C.BinOp (..), C.UnOp (..)
) where

import Cogent.Common.Syntax as Syn
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core           as CC
import Cogent.Dargent.Allocation
import Cogent.Util (tupleFieldNames)
import qualified Data.DList  as DList
import Data.Nat              as Nat
import qualified Data.OMap   as OMap

import Data.Binary (Binary)
import Data.Map as M hiding (map)
import GHC.Generics (Generic, Generic1)
import qualified "language-c-quote" Language.C as C

import Text.Parsec.Pos (SourcePos, initialPos)

type CId = String

data CIntType = CCharT | CShortT | CIntT | CLongT | CLongLongT
              deriving (Eq, Ord, Show, Generic)

instance Binary CIntType

data CArraySize = CArraySize CExpr
                | CNoArraySize
                | CPtrToArray
                deriving (Eq, Ord, Show, Generic)

instance Binary CArraySize

-- The type parameter has been stripped off
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
           deriving (Eq, Ord, Show, Generic)

instance Binary CType

data Radix = OCT | DEC | HEX
              deriving (Eq, Ord, Show, Generic)

instance Binary Radix

data CLitConst = CNumConst Integer CType Radix
               | CCharConst Char
               | CStringConst String
               deriving (Eq, Ord, Show, Generic)

instance Binary CLitConst

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
           deriving (Eq, Ord, Show, Generic)

instance Binary CExpr

data CInitializer = CInitE CExpr
                  | CInitList [([CDesignator], CInitializer)]
                  deriving (Eq, Ord, Show, Generic)

instance Binary CInitializer

data CDesignator = CDesignE CExpr
                 | CDesignFld CId
                 deriving (Eq, Ord, Show, Generic)

instance Binary CDesignator

type CBinOp    = C.BinOp
type CUnOp     = C.UnOp

-- Orphans

deriving instance Generic C.BinOp
deriving instance Generic C.UnOp

instance Binary C.BinOp
instance Binary C.UnOp

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

data CBlockItem = CBIStmt CStmt SourcePos
                | CBIDecl (CDeclaration IND) SourcePos
                deriving (Show)

__dummyPos = initialPos "dummy"

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
              deriving (Show, Generic)

-- | 'StrlType' tried to unify some of the types we have in Core.
--   It can be deemed as the C representation for Cogent types.
data StrlType = Record  [(CId, CType)]         -- ^ @(fieldname &#x21A6; fieldtype)@
              | RecordL (DataLayout BitRange)  -- to be laid out according to its Dargent description
              | Product CType CType            -- ^ pair
              | Variant (M.Map CId CType)      -- ^ one tag field, and fields for all possibilities
              | Function CType CType
              | AbsType CId
              | Array CType (Maybe CExpr)      -- for static arrays the size is needed
              | ArrayL (DataLayout BitRange)
              deriving (Eq, Ord, Show, Generic)

instance Binary StrlType

type RecordAccessors = OMap.OMap FieldName (Maybe FunName, Maybe FunName)

data Sort = SRecord (DList.DList (Sigil ())) (Maybe RecordAccessors)
          | SVariant
          | SAbstract
          | SArray
          deriving (Eq, Ord, Show, Generic)

instance Binary Sort

typeToSort :: CC.Type 'Zero a -> Sort
typeToSort (CC.TCon {}) = SAbstract
typeToSort (CC.TSum {}) = SVariant
typeToSort (CC.TRecord _ fs s) = SRecord (DList.singleton $ fmap (const ()) s) mfs
  where mfs = case s of Unboxed  -> Nothing
                        Boxed {} -> Just $ OMap.fromList $ map (\(f,_) -> (f, (Nothing, Nothing))) fs
#ifdef BUILTIN_ARRAYS
typeToSort (CC.TArray {}) = SArray
typeToSort (CC.TRefine b _) = typeToSort b
#endif
typeToSort _ = __impossible "typeToSort"

extendSort :: CC.Type 'Zero a -> Sort -> Sort
extendSort (CC.TRecord _ fs s') (SRecord ss ma) =
  SRecord (fmap (const ()) s' `DList.cons` ss) $
    case (s', ma) of
      (Unboxed,  Nothing) -> Nothing
      (Boxed {}, Nothing) -> Just $ OMap.fromList $ map (\(f,_) -> (f, (Nothing, Nothing))) fs
      (_, Just ma') -> Just ma'
extendSort _ s = s


-- Custom equality for `BoxedRecord` case of `StrlType`
-- Needed to allow us to ignore whether fields/alternatives are/aren't "taken"
-- when deciding whether two cogent types should go to the same C type
newtype StrlCogentType = StrlCogentType (CC.Type 'Zero VarName)
                       deriving (Show, Binary)

instance Eq StrlCogentType where
  (StrlCogentType t1) == (StrlCogentType t2) = strlCogentTypeEq t1 t2

instance Ord StrlCogentType where
  (StrlCogentType t1) <= (StrlCogentType t2) = strlCogentTypeEq t1 t2 || t1 <= t2


-- *****************************************************************************
-- * Helper functions to build C syntax

u32 :: CType
u32 = CogentPrim U32

ulongCTy, uintCTy, sintCTy, charCTy :: CType
ulongCTy = CInt False CLongT
uintCTy  = CInt False CIntT
sintCTy  = CInt True CIntT
charCTy  = CInt False CCharT

unitCTy, tagCTy, boolCTy :: CType
unitCTy = CIdent unitT
tagCTy  = CIdent tagsT
boolCTy = CIdent boolT

archCTy :: CType
archCTy = case __cogent_arch of X86_64 -> ulongCTy; X86_32 -> uintCTy; ARM32 -> uintCTy


-- FIXME: more might be true / zilinc
-- isAddressableCExpr :: CExpr -> Bool
-- isAddressableCExpr (CVar {}) = True
-- isAddressableCExpr (CDeref e) = isAddressableCExpr e
-- isAddressableCExpr (CTypeCast _ e) = isAddressableCExpr e
-- isAddressableCExpr _ = False

primCId :: PrimInt -> String
primCId Boolean = "Bool"
primCId U8  = "u8"
primCId U16 = "u16"
primCId U32 = "u32"
primCId U64 = "u64"

likelihood :: Likelihood -> (CExpr -> CExpr)
likelihood l = case l of Likely   -> likely
                         Regular  -> id
                         Unlikely -> unlikely

likely :: CExpr -> CExpr
likely e = CEFnCall (CVar "likely" (Just $ CFunction CBool CBool)) [e]

unlikely :: CExpr -> CExpr
unlikely e = CEFnCall (CVar "unlikely" (Just $ CFunction CBool CBool)) [e]

variable :: CId -> CExpr
variable = flip CVar Nothing

mkBoolLit :: CExpr -> CExpr
mkBoolLit e = CCompLit (CIdent boolT) [([CDesignFld boolField], CInitE e)]

true :: CExpr
true = mkConst Boolean 1

-- | Produces a C expression for an unsigned integer literal with the given integer value.
uint :: Integer -> CExpr
uint n = CConst $ CNumConst n uintCTy DEC

-- | Produces a C expression for a signed integer literal with the given integer value.
sint :: Integer -> CExpr
sint n = CConst $ CNumConst n sintCTy DEC

mkConst :: (Integral n) => PrimInt -> n -> CExpr
mkConst pt (fromIntegral -> n)
  | pt == Boolean = mkBoolLit (mkConst U8 n)
  | otherwise = CConst $ CNumConst n (CogentPrim pt) DEC

-- str.fld
strDot' :: CId -> CId -> CExpr
strDot' str fld = strDot (variable str) fld

-- str->fld
strArrow' :: CId -> CId -> CExpr
strArrow' str fld = strArrow (variable str) fld

strDot :: CExpr -> CId -> CExpr
strDot rec fld = CStructDot rec fld

strArrow :: CExpr -> CId -> CExpr
strArrow rec fld = CStructDot (CDeref rec) fld

mkArrIdx :: Integral t => CExpr -> t -> CExpr
mkArrIdx arr idx = CArrayDeref arr (mkConst U32 idx)

isTrivialCExpr :: CExpr -> Bool
isTrivialCExpr (CBinOp {}) = False
isTrivialCExpr (CUnOp {}) = False
isTrivialCExpr (CCondExpr {}) = False
isTrivialCExpr (CConst {}) = True
isTrivialCExpr (CVar {}) = True
isTrivialCExpr (CStructDot (CDeref e) _) = False  -- NOTE: Not sure why but we cannot do `isTrivialCExpr e && not __cogent_fintermediate_vars' / zilinc
isTrivialCExpr (CArrayDeref e idx) = __fixme $ isTrivialCExpr e && isTrivialCExpr idx
isTrivialCExpr (CStructDot e _) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CDeref e) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CAddrOf e) = isTrivialCExpr e && not __cogent_fintermediate_vars
isTrivialCExpr (CTypeCast _ e) = isTrivialCExpr e
isTrivialCExpr (CSizeof   e) = isTrivialCExpr e
isTrivialCExpr (CSizeofTy _) = True
isTrivialCExpr (CEFnCall {}) = False
isTrivialCExpr (CCompLit _ dis) = and (map (\(ds,i) -> and (map isTrivialCDesignator ds) && isTrivialCInitializer i) dis) && __cogent_fuse_compound_literals
isTrivialCExpr (CMKBOOL e) = isTrivialCExpr e

isTrivialCInitializer :: CInitializer -> Bool
isTrivialCInitializer (CInitE e) = isTrivialCExpr e
isTrivialCInitializer (CInitList dis) = and $ map (\(ds,i) -> and (map isTrivialCDesignator ds) && isTrivialCInitializer i) dis

isTrivialCDesignator :: CDesignator -> Bool
isTrivialCDesignator (CDesignE e) = isTrivialCExpr e
isTrivialCDesignator (CDesignFld _) = True


genOp :: Syn.Op -> CC.Type 'Zero VarName -> [CExpr] -> CExpr
genOp opr (CC.TPrim pt) es =
  let oprf = case opr of
               -- binary
               Plus        -> (\[e1,e2] -> downcast pt $ CBinOp C.Add  (upcast pt e1) (upcast pt e2))
               Minus       -> (\[e1,e2] -> downcast pt $ CBinOp C.Sub  (upcast pt e1) (upcast pt e2))
               Divide      -> (\[e1,e2] -> (if __cogent_fcheck_undefined then flip (CCondExpr e2) (mkConst pt 0) else id)
                                              (downcast pt $ CBinOp C.Div (upcast pt e1) (upcast pt e2)))
               Times       -> (\[e1,e2] -> downcast pt $ CBinOp C.Mul  (upcast pt e1) (upcast pt e2))
               Mod         -> (\[e1,e2] -> (if __cogent_fcheck_undefined then flip (CCondExpr e2) (mkConst pt 0) else id)
                                              (downcast pt $ CBinOp C.Mod (upcast pt e1) (upcast pt e2)))
               And         -> (\[e1,e2] -> mkBoolLit (CBinOp C.Land (strDot e1 boolField) (strDot e2 boolField)))
               Or          -> (\[e1,e2] -> mkBoolLit (CBinOp C.Lor  (strDot e1 boolField) (strDot e2 boolField)))
               BitAnd      -> (\[e1,e2] -> downcast pt $ CBinOp C.And  (upcast pt e1) (upcast pt e2))
               BitXor      -> (\[e1,e2] -> downcast pt $ CBinOp C.Xor  (upcast pt e1) (upcast pt e2))
               BitOr       -> (\[e1,e2] -> downcast pt $ CBinOp C.Or   (upcast pt e1) (upcast pt e2))
               LShift      -> (\[e1,e2] -> (if __cogent_fcheck_undefined
                                              then CCondExpr (CBinOp C.Ge e2 (mkConst pt $ width pt)) (mkConst pt 0) else id)
                                             (downcast pt $ CBinOp C.Lsh (upcast pt e1) (upcast pt e2)))
               RShift      -> (\[e1,e2] -> (if __cogent_fcheck_undefined
                                              then CCondExpr (CBinOp C.Ge e2 (mkConst pt $ width pt)) (mkConst pt 0) else id)
                                             (downcast pt $ CBinOp C.Rsh (upcast pt e1) (upcast pt e2)))
               Gt          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Gt e1 e2)
               Lt          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Lt e1 e2)
               Ge          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Ge e1 e2)
               Le          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Le e1 e2)
               Syn.Eq      -> (\[e1,e2] -> case pt of
                                Boolean -> mkBoolLit (CBinOp C.Eq (strDot e1 boolField) (strDot e2 boolField))
                                _       -> mkBoolLit (CBinOp C.Eq e1 e2))
               Syn.NEq     -> (\[e1,e2] -> case pt of
                                Boolean -> mkBoolLit (CBinOp C.Ne (strDot e1 boolField) (strDot e2 boolField))
                                _       -> mkBoolLit (CBinOp C.Ne e1 e2))
               -- unary
               Syn.Not        -> (\[e1] -> mkBoolLit (CUnOp C.Lnot (strDot e1 boolField)))
               Syn.Complement -> (\[e1] -> downcast pt $ CUnOp C.Not (upcast pt e1))
   in oprf es
  where width = \case U8 -> 8; U16 -> 16; U32 -> 32; U64 -> 64; Boolean -> 8
        -- vvv FIXME: I don't remember why we did it this way. Is it for verification or performance? / zilinc
        upcast, downcast :: PrimInt -> CExpr -> CExpr
        upcast   pt e = if pt `elem` [U8, U16] then CTypeCast u32 e else e
        downcast pt e = if pt `elem` [U8, U16] then CTypeCast (CogentPrim pt) e else e
genOp _ _ _ = __impossible "genOp"


-- *****************************************************************************
-- ** Naming conventions

-- NOTE: Reserved names; users should NOT use them in Cogent programs!
--       Prefixing underscores are disliked by C-parser / zilinc


tagsT, fieldTag :: CId
tagsT         = "tag_t"
fieldTag      = "tag"
tagEnum tag   = "TAG_ENUM_" ++ tag

variantT :: CId
variantT = "variant_t"

-- NOTE: assume ty is given by function `genType'
mkVariantTT :: TagName -> CType -> CId
mkVariantTT tag (CIdent tn) = tag ++ "_" ++ tn
mkVariantTT tag (CPtr (CIdent tn)) = tag ++ "_p" ++ tn  -- FIXME: may need to distinguish * and non-* / zilinc
mkVariantTT _ _ = __impossible "mkVariantTT"

argOf fn = fn ++ "_arg"
retOf fn = fn ++ "_ret"

unitT, dummyField :: CId
unitT         = "unit_t"
dummyField    = "dummy"

boolT, boolField :: CId
boolT     = "bool_t"
boolField = "boolean"

arrField :: CId
arrField = "data"

funEnum fn = "FUN_ENUM_" ++ fn
untypedFuncEnum = "untyped_func_enum" :: CId
funDispatch tn = "dispatch_" ++ tn  -- tn is the typename of the Enum
funMacro f = "FUN_MACRO_" ++ f
funDispMacro f = "FUN_DISP_MACRO_" ++ f

-- FIXME: we can probably merge these
letbangTrue = "LETBANG_TRUE"
letTrue = "LET_TRUE"

p1, p2 :: CId
p1 = tupleFieldNames !! 0
p2 = tupleFieldNames !! 1

-- NOTE: use actual names instead
-- XXX | field n = 'f':show n
-- XXX | fields = map (('f':) . show) [0 :: Int ..]


{- |
Compares cogent types ignoring whether fields are or aren't taken
-}
strlCogentTypeEq :: CC.Type 'Zero VarName -> CC.Type 'Zero VarName -> Bool
strlCogentTypeEq (TCon n1 ts1 s1) (TCon n2 ts2 s2) = n1 == n2 && ts1 == ts2 && strlSigilEq s1 s2
strlCogentTypeEq (TPrim p1)       (TPrim p2)       = p1 == p2
strlCogentTypeEq (TSum alts1)     (TSum alts2)     = all (\((n1, (t1, _)), (n2, (t2, _))) -> n1 == n2 && strlCogentTypeEq t1 t2) $ zip alts1 alts2
strlCogentTypeEq (TRecord _ fs1 s1) (TRecord _ fs2 s2) = strlSigilEq s1 s2 && all (\((n1, (t1, _)), (n2, (t2, _))) -> n1 == n2 && strlCogentTypeEq t1 t2) (zip fs1 fs2)
strlCogentTypeEq TUnit            TUnit            = True
#ifdef BUILTIN_ARRAYS
strlCogentTypeEq a1@(TArray t1 l1 s1 _) (TArray t2 l2 s2 _) = t1 == t2 && l1 == l2 && strlSigilEq s1 s2
#endif
strlCogentTypeEq a1@(TProduct _ _)(TProduct _ _)   = __impossible $ "Cogent.C.Syntax: StrlCogentType instance Eq: Type " ++ show a1 ++ " cannot be embedded in a boxed record."
strlCogentTypeEq a1@(TString)     (TString)        = __impossible $ "Cogent.C.Syntax: StrlCogentType instance Eq: Type " ++ show a1 ++ " cannot be embedded in a boxed record."
strlCogentTypeEq a1@(TFun _ _)    (TFun _ _)       = __impossible $ "Cogent.C.Syntax: StrlCogentType instance Eq: Type " ++ show a1 ++ " cannot be embedded in a boxed record."
strlCogentTypeEq a1@(TVar _)      (TVar _)         = __impossible $ "Cogent.C.Syntax: StrlCogentType instance Eq: Type " ++ show a1 ++ " cannot be embedded in a boxed record."
strlCogentTypeEq a1@(TVarBang _)  (TVarBang _)     = __impossible $ "Cogent.C.Syntax: StrlCogentType instance Eq: Type " ++ show a1 ++ " cannot be embedded in a boxed record."
strlCogentTypeEq _                _                = False

strlSigilEq :: Eq a => Sigil a -> Sigil a -> Bool
strlSigilEq (Boxed _ l1) (Boxed _ l2) = l1 == l2
strlSigilEq Unboxed      Unboxed      = True
strlSigilEq _            _            = False

