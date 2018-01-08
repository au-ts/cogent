--
-- Copyright 2017, Data61
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
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{- LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{- LANGUAGE TypeFamilies #-}
{- LANGUAGE TypeOperators #-}

-- Copied from Cogent, dropping tyvars
data Type
  = TCon TypeName [Type] Sigil
  | TFun Type Type
  | TPrim PrimInt
  | TString
  | TSum [(TagName, (Type, Bool))]  -- True means taken (since 2.0.4)
  | TProduct Type Type
  | TRecord [(FieldName, (Type, Bool))] Sigil  -- True means taken
  | TUnit
  deriving (Show, Eq, Ord)

data Sigil = ReadOnly  -- 0-kind
           | Writable  -- 1-kind
           | Unboxed   -- 2-kind
           deriving (Show, Eq, Ord)

data PrimInt = U8 | U16 | U32 | U64 | Boolean deriving (Show, Eq, Ord)

data Kind = K { canEscape :: Bool, canShare :: Bool, canDiscard :: Bool }
          deriving (Show, Eq, Ord)

type FieldName   = String
type TagName     = String
type FunName     = String
type VarName     = String
type TyVarName   = String
type TypeName    = String

type FieldIndex = Int

data Op
  = Plus | Minus | Times | Divide | Mod
  | Not | And | Or
  | Gt | Lt | Le | Ge | Eq | NEq
  | BitAnd | BitOr | BitXor | LShift | RShift | Complement
  deriving (Eq, Show)

data DdslType where
  CogentType :: Type -> DdslType
  Bitfield   :: Type -> BitInfo -> DdslType
  Arrow      :: DdslType -> DdslType -> DdslType

data BitInfo where
  BitInfo :: [(FieldName, Int)] -> BitInfo

data Range where
  Rng :: Int -> Int -> Range

data Decl where
  FunDef :: FunName -> DdslType -> Expr (X t) -> Decl
  FunDer :: FunName -> DdslType -> Decl
  FunAbs :: FunName -> DdslType -> Decl

type Id = String
 
data Expr m where
  Lam :: Id -> Expr b -> Expr (a -> b)
  App :: Expr (a -> b) -> Expr a -> Expr b
  Lit :: Literal -> Expr m
  SFun :: Id -> Expr (t -> S t ())
  DFun :: Id -> Expr (D t t)
  Var :: Id -> Expr m
  Bind :: Expr (m t a) -> Id -> Expr (a -> m t b) -> Expr (m t b)
  Seq  :: Expr (m t a) -> Expr (m t b) -> Expr (m t b)
  Return :: Expr t -> Expr (m t t)
  Inv :: Expr (S t a) -> Expr (D t b) -> Expr (X t)
  Case :: Expr t -> [(Expr t, Expr (m s a))] -> Expr (m s a)
  Pair :: Expr a -> Expr b -> Expr (a,b)

data Buf

data RW t
data RO t

data S t a
data D t a

data X t

-- data Mode = S | D | B | V
-- 
-- data SMode (m :: Mode) where
--   SS :: SMode S
--   SD :: SMode D
--   SB :: SMode B
--   SV :: SMode V

data Literal where
  IntLit  :: Int  -> Literal
  BoolLit :: Bool -> Literal

-- data Bind where
--   Bind :: Idx -> Expr -> Bind
-- 
-- data Alt where
--   LitAlt  :: Literal -> Alt
--   Default :: Alt

pu8 :: Decl
pu8 = FunAbs "pu8" (CogentType $ TPrim U8)

pu16 :: Decl
pu16 = FunAbs "pu16" (CogentType $ TPrim U16)

t1, t2, t3 :: Decl
t1 = FunAbs "t1" (CogentType $ TCon "T1" [] Writable)
t2 = FunAbs "t2" (CogentType $ TCon "T2" [] Writable)
t3 = FunAbs "t3" (CogentType $ TCon "T3" [] Writable)

y :: Decl
y = Inv
      (Lam "tag" 
        (Lam "v" 
          (Seq
            (App (SFun "pu16") (Var "tag")) 
            (Case 
              (Var "tag") 
              [ (Lit (IntLit 1), App (SFun "t1") (Var "v"))
              , (Lit (IntLit 2), App (SFun "t2") (Var "v"))
              , (Lit (IntLit 7), App (SFun "t3") (Var "v"))
              ]
            )
          )
        )
      )
      (Bind
        (DFun "pu16")
        ("tag")
        (Bind
          ()
          ("v")
          (Return ()))
      )
