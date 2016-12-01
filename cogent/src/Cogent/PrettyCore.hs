--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
#if __GLASGOW_HASKELL__ < 709
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.PrettyCore where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Core
import Cogent.Vec

import System.Console.ANSI (hSetSGR)
import System.IO (Handle, hPutChar, hPutStr)
import Text.PrettyPrint.ANSI.Leijen hiding (tupled,indent)
#if __GLASGOW_HASKELL__ >= 709
import Prelude hiding ((<$>))
#endif

import Unsafe.Coerce

indentation, ifIndentation :: Int
indentation = 3
ifIndentation = 3
position = string
varName = string
primop = blue . (pretty :: Op -> Doc)
keyword = bold . string
typevar = blue . string
typename = blue . bold . string
literal = dullcyan
typesymbol = cyan . string
kind = bold . typesymbol
funName = dullyellow . string
fieldName = magenta . string
fieldIndex = magenta . string . ('.':) . show
tagName = dullmagenta . string
symbol = string
kindsig = red . string
commaList = encloseSep empty empty (comma <> space)
dotList = encloseSep empty empty (symbol ".")
tupled = encloseSep lparen rparen (comma <> space)
tupled1 [x] = x
tupled1 x = encloseSep lparen rparen (comma <> space) x
typeargs x = encloseSep lbracket rbracket (comma <> space) x
err = red . string
comment = black . string
context = black . string
letbangvar = dullgreen . string
record = encloseSep (lbrace <> space) (space <> rbrace) (comma <> space)
variant = encloseSep (langle <> space) rangle (symbol "|" <> space) . map (<> space)
indent = nest indentation

level :: Associativity -> Int
level (LeftAssoc i) = i
level (RightAssoc i) = i
level (NoAssoc i) = i
level (Prefix) = 0

levelE :: Expr t v a e -> Int
levelE (Op opr [_,_]) = level (associativity opr)
levelE (ILit {}) = 0
levelE (Variable {}) = 0
levelE (Fun {}) = 0
levelE (App {}) = 1
levelE (Tuple {}) = 0
levelE (Con {}) = 0
levelE (Esac {}) = 0
levelE (Member {}) = 0
levelE (Take {}) = 0
levelE (Put {}) = 1
levelE (Promote {}) = 0
levelE _ = 100

class Pretty a => PrettyP a where
  prettyP :: Int -> a -> Doc

instance (Pretty a, Pretty (Expr t v a e)) => PrettyP (Expr t v a e) where
  prettyP l x | levelE x < l   = pretty x
              | otherwise = parens (pretty x)

instance (Pretty a, Pretty (TypedExpr t v a)) => PrettyP (TypedExpr t v a) where
  prettyP i (TE _ x) = prettyP i x
instance (Pretty a, Pretty (UntypedExpr t v a)) => PrettyP (UntypedExpr t v a) where
  prettyP i (E x) = prettyP i x

instance Pretty Likelihood where
  pretty Likely = symbol "=>"
  pretty Unlikely = symbol "~>"
  pretty Regular = symbol "->"

-- prettyL :: Likelihood -> Doc
-- prettyL Likely = symbol "+%"
-- prettyL Regular = empty
-- prettyL Unlikely = symbol "-%"

prettyV = dullblue  . string . ("_v" ++) . show . finInt
prettyT = dullgreen . string . ("_t" ++) . show . finInt

instance Pretty a => Pretty (TypedExpr t v a) where
  pretty (TE _ e) = pretty e
instance Pretty a => Pretty (UntypedExpr t v a) where
  pretty (E e) = pretty e

instance (Pretty a, PrettyP (e t v a), Pretty (e t ('Suc v) a), Pretty (e t ('Suc ('Suc v)) a))
         => Pretty (Expr t v a e) where
  pretty (Op opr [a,b])
     | LeftAssoc  l <- associativity opr = prettyP (l+1) a <+> primop opr <+> prettyP l b
     | RightAssoc l <- associativity opr = prettyP l a <+> primop opr <+> prettyP (l+1)  b
     | NoAssoc    l <- associativity opr = prettyP l a <+> primop opr <+> prettyP l  b
  pretty (Op opr [e]) = primop opr <+> prettyP 1 e
  pretty (Op opr es)  = primop opr <+> tupled (map pretty es)
  pretty (ILit i pt) = literal (string $ show i) <+> symbol "::" <+> pretty pt
  pretty (SLit s) = literal $ string s
  pretty (Variable x) = pretty (snd x) <> angles (prettyV $ fst x)
  pretty (Fun fn ins nt) = pretty nt <> funName fn <+> pretty ins
  pretty (App a b) = prettyP 2 a <+> prettyP 1 b
  pretty (Let a e1 e2) = align (keyword "let" <+> pretty a <+> symbol "=" <+> pretty e1 <$>
                                keyword "in" <+> pretty e2)
  pretty (LetBang bs a e1 e2) = align (keyword "let!" <+> tupled (map (prettyV . fst) bs) <+> pretty a <+> symbol "=" <+> pretty e1 <$>
                                       keyword "in" <+> pretty e2)
  pretty (Unit) = tupled []
  pretty (Tuple e1 e2) = tupled (map pretty [e1, e2])
  pretty (Struct fs) = symbol "#" <> record (map (\(n,e) -> fieldName n <+> symbol "=" <+> pretty e) fs)
  pretty (Con tn e) = tagName tn <+> prettyP 1 e
  pretty (If c t e) = group . align $ (keyword "if" <+> pretty c
                                       <$> indent (keyword "then" </> align (pretty t))
                                       <$> indent (keyword "else" </> align (pretty e)))
  pretty (Case e tn (l1,_,a1) (l2,_,a2)) = align (keyword "case" <+> pretty e <+> keyword "of"
                                                  <$> indent (tagName tn <+> pretty l1 <+> align (pretty a1))
                                                  <$> indent (symbol "*" <+> pretty l2 <+> align (pretty a2)))
  pretty (Esac e) = keyword "esac" <+> parens (pretty e)
  pretty (Split _ e1 e2) = align (keyword "split" <+> pretty e1 <$>
                                  keyword "in" <+> pretty e2)
  pretty (Member x f) = prettyP 1 x <> symbol "." <> fieldIndex f
  pretty (Take (a,b) rec f e) = align (keyword "take" <+> tupled [pretty a, pretty b] <+> symbol "="
                                                      <+> prettyP 1 rec <+> record (fieldIndex f:[]) <$>
                                       keyword "in" <+> pretty e)
  pretty (Put rec f v) = prettyP 1 rec <+> record [fieldIndex f <+> symbol "=" <+> pretty v]
  pretty (Promote t e) = prettyP 1 e <+> symbol "::" <+> pretty t

instance Pretty FunNote where
  pretty NoInline = empty
  pretty InlineMe = comment "{-# INLINE #-}" <+> empty
  pretty MacroCall = comment "{-# FNMACRO #-}" <+> empty
  pretty InlinePlease = comment "inline" <+> empty

instance Pretty (Type t) where
  pretty (TVar v) = prettyT v
  pretty (TVarBang v) = prettyT v <> typesymbol "!"
  pretty (TPrim pt) = pretty pt
  pretty (TString) = typename "String"
  pretty (TUnit) = typename "()"
  pretty (TProduct t1 t2) = tupled (map pretty [t1, t2])
  pretty (TSum alts) = variant (map (\(n,(t,_)) -> tagName n <+> pretty t) alts)  -- FIXME: cogent.1
  pretty (TFun t1 t2) = prettyT' t1 <+> typesymbol "->" <+> pretty t2
     where prettyT' e@(TFun {}) = parens (pretty e)
           prettyT' e           = pretty e
  pretty (TRecord fs s) = record (map (\(f,(t,b)) -> fieldName f <+> symbol ":" <> prettyTaken b <+> pretty t) fs) <> pretty s
  pretty (TCon tn [] s) = typename tn <> pretty s
  pretty (TCon tn ts s) = typename tn <> pretty s <+> typeargs (map pretty ts)

prettyTaken :: Bool -> Doc
prettyTaken True  = symbol "*"
prettyTaken False = empty

instance Pretty Sigil where
  pretty Writable = empty
  pretty ReadOnly = typesymbol "!"
  pretty Unboxed  = typesymbol "#"

#if __GLASGOW_HASKELL__ < 709
instance Pretty (TyVarName, Kind) where
#else
instance {-# OVERLAPPING #-} Pretty (TyVarName, Kind) where
#endif
  pretty (v,k) = pretty v <> typesymbol ":<" <> pretty k

instance Pretty Kind where
  pretty (K False False False) = string "()"
  pretty (K e s d) = if e then kind "E" else empty <>
                     if s then kind "S" else empty <>
                     if d then kind "D" else empty

instance Pretty a => Pretty (Vec t a) where
  pretty Nil = empty
  pretty (Cons x Nil) = pretty x
  pretty (Cons x xs) = pretty x <> string "," <+> pretty xs


class PrettyH e (n :: Nat) a where
  prettyH :: forall (t :: Nat). e t n a -> Doc

instance Pretty a => PrettyH TypedExpr n a where
  prettyH = pretty
  
instance (Pretty a, PrettyH e ('Suc 'Zero) a) => Pretty (Definition e a) where
  pretty (FunDef _ fn ts t rt e)  = funName fn <+> symbol ":" <+> brackets (pretty ts) <> symbol "." <+>
                                    parens (pretty t) <+> symbol "->" <+> parens (pretty rt) <+> symbol "=" <$>
                                    prettyH e  -- FIXME: Use of `unsafeCoerce' to retain existential type / zilinc
  pretty (AbsDecl _ fn ts t rt)   = funName fn <+> symbol ":" <+> brackets (pretty ts) <> symbol "." <+>
                                    parens (pretty t) <+> symbol "->" <+> parens (pretty rt)
  pretty (TypeDef tn ts Nothing)  = keyword "type" <+> typename tn <+> pretty ts
  pretty (TypeDef tn ts (Just t)) = keyword "type" <+> typename tn <+> pretty ts <+>
                                    symbol "=" <+> pretty t
  prettyList xs = vcat (map (pretty)  xs)

displayOneLine :: Handle -> SimpleDoc -> IO ()
displayOneLine handle simpleDoc = display simpleDoc >> hPutChar handle '\n'
  where
    display SFail          = error $ "@SFail@ can not appear uncaught in a " ++ "rendered @SimpleDoc@"
    display SEmpty         = return ()
    display (SChar c x)    = do{ hPutChar handle c  ; display x}
    display (SText l s x)  = do{ hPutStr  handle s  ; display x}
    display (SLine i x)    = do{ hPutChar handle ' '; display x}
    display (SSGR s x)     = do{ hSetSGR  handle s  ; display x}
