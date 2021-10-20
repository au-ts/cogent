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

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.PrettyPrint where
import qualified Cogent.Common.Syntax as S (associativity)
import Cogent.Common.Syntax hiding (associativity)
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Reorganizer (ReorganizeError(..), SourceObject(..))
import Cogent.Surface
-- import Cogent.TypeCheck --hiding (context)
import Cogent.TypeCheck.Base
import Cogent.TypeCheck.Subst hiding (null)
import qualified Cogent.TypeCheck.ARow as ARow
import qualified Cogent.TypeCheck.Row as Row

import Cogent.Dargent.Allocation
import Cogent.Dargent.Core
import Cogent.Dargent.TypeCheck
import Cogent.Dargent.Util

import Control.Arrow (second)
import Data.Bifoldable (bifoldMap)
import qualified Data.Foldable as F
import Data.Function ((&))
import Data.IntMap as I (IntMap, toList, lookup)
import Data.List (intercalate, nub, partition)
import qualified Data.Map as M hiding (foldr)
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid (mconcat)
import Prelude hiding (foldr)
#else
import Prelude hiding ((<$>), foldr)
#endif
import Data.Nat (natToInt)
import Data.Word (Word32)
import System.FilePath (takeFileName)
import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen hiding (indent, tupled)


-- pretty-printing theme definition
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- meta-level constructs

position = string
err = red . string
errbd = bold . err
warn = dullyellow . string
comment = black . string
context = black . string
context' = string

-- language ast

varname = string
letbangvar = dullgreen . string
primop = blue . string
keyword = bold . string
literal = dullcyan
reprname = dullcyan . string
typevar = blue . string
typename = blue . bold . string
typesymbol = cyan . string  -- type operators, e.g. !, ->, take
funname = green . string
funname' = underline . green . string
fieldname = magenta . string
tagname = dullmagenta . string
dlvarname = dullblue . string
symbol = string
kindsig = red . string
typeargs [] = brackets empty
typeargs xs = encloseSep lbracket rbracket (comma <> space) xs
layoutargs [] = braces $ braces empty
layoutargs xs = encloseSep (lbrace <> lbrace) (rbrace <> rbrace) (comma <> space) xs
array = encloseSep lbracket rbracket (comma <> space)
record = encloseSep (lbrace <> space) (space <> rbrace) (comma <> space)
variant = encloseSep (langle <> space) rangle (symbol "|" <> space) . map (<> space)
reftype v t e = lbracket <+> v <+> symbol ":" <+> t <+> symbol "|" <+> e <+> rbracket

-- combinators, helpers

indentation :: Int
indentation = 3

indent = nest indentation
indent' = (string (replicate indentation ' ') <>) . indent

-- FIXME: no spaces within parens where elements are on multiple lines / zilinc
tupled = __fixme . encloseSep lparen rparen (comma <> space)
-- non-unit tuples. put parens subject to arity
tupled1 [x] = x
tupled1 x = __fixme $ encloseSep lparen rparen (comma <> space) x

spaceList = encloseSep empty empty space
commaList = encloseSep empty empty (comma <> space)


-- associativity
-- ~~~~~~~~~~~~~~~~

associativity :: String -> Associativity
associativity = S.associativity . symbolOp


-- type classes and instances for different constructs
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

class Prec a where  -- precedence
  prec :: a -> Int  -- smaller the number stronger the associativity

instance Prec () where
  prec _ = 0

instance Prec Associativity where
  prec (LeftAssoc  i) = i
  prec (RightAssoc i) = i
  prec (NoAssoc    i) = i
  prec (Prefix)       = 9  -- as in the expression builder

instance Prec (Expr t p ip l e) where
  -- vvv terms
  prec (Var {}) = 0
  prec (TLApp {}) = 0
  prec (BoolLit {}) = 0
  prec (Con _ []) = 0
  prec (IntLit {}) = 0
  prec (CharLit {}) = 0
  prec (StringLit {}) = 0
  prec (Unitel) = 0
  prec (Tuple {}) = 0
#ifdef BUILTIN_ARRAYS
  prec (ArrayLit {}) = 0
  prec (ArrayMap2 {}) = 9
#endif
  prec (UnboxedRecord {}) = 0
  -- vvv parsed by the expression builder
  prec (Member {}) = 8
  prec (Upcast {}) = 9
  prec (App  _ _ False) = 9
  prec (AppC {}) = 9
  prec (Con _ _) = 9
  prec (Put {}) = 9
#ifdef BUILTIN_ARRAYS
  prec (ArrayIndex {}) = 10
  prec (ArrayPut {}) = 9
#endif
  prec (Comp {}) = 10
  prec (PrimOp n _) = prec (associativity n)  -- range 11 - 19
  prec (Annot {}) = 30
  prec (App  _ _ True) = 31
  -- vvv expressions
  prec (Lam  {}) = 100
  prec (LamC {}) = 100
  prec (Seq {}) = 100
  prec (Match {}) = 100
  prec (If {}) = 100
  prec (MultiWayIf {}) = 100
  prec (Let {}) = 100

instance Prec RawExpr where
  prec (RE e) = prec e

instance Prec LocExpr where
  prec (LocExpr _ e) = prec e

instance Prec (TExpr t l) where
  prec (TE _ e _) = prec e

instance Prec (SExpr t l) where
  prec (SE _ e) = prec e
  prec (SU {}) = 0

-- NOTE: they differ from the definition of the fixity of Constraint
instance Prec Constraint where
  prec (_ :&  _) = 3
  prec (_ :@  _) = 2
#ifdef BUILTIN_ARRAYS
  prec (_ :-> _) = 1
#endif
  prec _ = 0

-- ------------------------------------

-- add parens and indents to expressions depending on level
prettyPrec :: (Pretty a, Prec a) => Int -> a -> Doc
prettyPrec l x | prec x < l = pretty x
               | otherwise  = parens (indent (pretty x))

-- ------------------------------------

class ExprType a where
  isVar :: a -> VarName -> Bool

instance ExprType (Expr t p ip l e) where
  isVar (Var n) s = (n == s)
  isVar _ _ = False

instance ExprType RawExpr where
  isVar (RE e) = isVar e

instance ExprType LocExpr where
  isVar (LocExpr _ e) = isVar e

instance ExprType (TExpr t l) where
  isVar (TE _ e _) = isVar e

instance ExprType (SExpr t l) where
  isVar (SE _ e) = isVar e
  isVar (SU {}) = const False

-- ------------------------------------

class PatnType a where
  isPVar  :: a -> VarName -> Bool
  prettyP :: a -> Doc
  prettyB :: (Pretty t, Pretty e, Prec e) => (a, Maybe t, e) -> Bool -> Doc  -- binding

instance (PrettyName pv, PatnType ip, Pretty ip, Pretty e) => PatnType (IrrefutablePattern pv ip e) where
  isPVar (PVar pv) = isName pv
  isPVar _ = const False

  prettyP p@(PTake {}) = parens (pretty p)
  prettyP p = pretty p

  prettyB (p, Just t, e) i
    = group (pretty p <+> symbol ":" <+> pretty t <+> symbol "=" <+>
             (if i then (prettyPrec 100) else pretty) e)
  prettyB (p, Nothing, e) i
    = group (pretty p <+> symbol "=" <+>
             (if i then (prettyPrec 100) else pretty) e)

instance PatnType RawIrrefPatn where
  isPVar  (RIP p) = isPVar p
  prettyP (RIP p) = prettyP p
  prettyB (RIP p,mt,e) = prettyB (p,mt,e)

instance PatnType LocIrrefPatn where
  isPVar  (LocIrrefPatn _ p) = isPVar p
  prettyP (LocIrrefPatn _ p) = prettyP p
  prettyB (LocIrrefPatn _ p,mt,e) = prettyB (p,mt,e)

instance (Pretty t, Pretty l) => PatnType (TIrrefPatn t l) where
  isPVar  (TIP p _) = isPVar p
  prettyP (TIP p _) = prettyP p
  prettyB (TIP p _,mt,e) = prettyB (p,mt,e)

instance (PatnType ip, Pretty ip) => PatnType (Pattern ip) where
  isPVar (PIrrefutable ip) = isPVar ip
  isPVar _ = const False

  prettyP (PIrrefutable ip) = prettyP ip
  prettyP p = pretty p

  prettyB (p, Just t, e) i
       = group (pretty p <+> symbol ":" <+> pretty t <+> symbol "<=" <+> (if i then (prettyPrec 100) else pretty) e)
  prettyB (p, Nothing, e) i
       = group (pretty p <+> symbol "<=" <+> (if i then (prettyPrec 100) else pretty) e)

instance PatnType RawPatn where
  isPVar  (RP p)= isPVar p
  prettyP (RP p) = prettyP p
  prettyB (RP p,mt,e) = prettyB (p,mt,e)

instance PatnType LocPatn where
  isPVar  (LocPatn _ p) = isPVar p
  prettyP (LocPatn _ p) = prettyP p
  prettyB (LocPatn _ p,mt,e) = prettyB (p,mt,e)

instance (Pretty t, Pretty l) => PatnType (TPatn t l) where
  isPVar  (TP p _) = isPVar p
  prettyP (TP p _) = prettyP p
  prettyB (TP p _,mt,e) = prettyB (p,mt,e)

-- ------------------------------------

class TypeType t where
  isCon :: t -> Bool
  isTakePut :: t -> Bool
  isFun :: t -> Bool
  isAtomic :: t -> Bool

instance TypeType (Type e l t) where
  isCon     (TCon {})  = True
  isCon     _          = False
  isFun     (TFun {})  = True
  isFun     _          = False
  isTakePut (TTake {}) = True
  isTakePut (TPut  {}) = True
#ifdef BUILTIN_ARRAYS
  isTakePut (TATake {}) = True
  isTakePut (TAPut  {}) = True
#endif
  isTakePut _          = False
  isAtomic t | isFun t || isTakePut t = False
             | TCon _ (_:_) _ <- t = False
             | TUnbox _ <- t = False
             | TBang  _ <- t= False
             | otherwise = True

instance TypeType RawType where
  isCon     (RT t) = isCon     t
  isTakePut (RT t) = isTakePut t
  isFun     (RT t) = isFun     t
  isAtomic  (RT t) = isAtomic  t

instance TypeType DepType where
  isCon     (DT t) = isCon     t
  isTakePut (DT t) = isTakePut t
  isFun     (DT t) = isFun     t
  isAtomic  (DT t) = isAtomic  t

instance TypeType TCType where
  isCon     (T t) = isCon t
  isCon     _     = False
  isFun     (T t) = isFun t
  isFun     _     = False
  isTakePut (T t) = isTakePut t
  isTakePut _     = False
  isAtomic  (T t) = isAtomic t
  isAtomic  (U _) = True
  isAtomic  (Synonym _ []) = True
  isAtomic  _     = False

-- ------------------------------------

class PrettyName a where
  prettyName :: a -> Doc
  isName :: a -> String -> Bool

instance PrettyName VarName where
  prettyName = varname
  isName s = (== s)

instance Pretty t => PrettyName (VarName, t) where
  prettyName (a, b) | __cogent_fshow_types_in_pretty = parens $ prettyName a <+> comment "::" <+> pretty b
                    | otherwise = prettyName a
  isName (a, b) x = a == x

-- ------------------------------------

-- class Pretty

instance Pretty Word32 where
  pretty = integer . fromIntegral

instance Pretty Likelihood where
  pretty Likely   = symbol "=>"
  pretty Unlikely = symbol "~>"
  pretty Regular  = symbol "->"

instance (PrettyName pv, PatnType ip, Pretty ip, Pretty e) => Pretty (IrrefutablePattern pv ip e) where
  pretty (PVar v) = prettyName v
  pretty (PTuple ps) = tupled (map pretty ps)
  pretty (PUnboxedRecord fs) = string "#" <> record (fmap handleTakeAssign fs)
  pretty (PUnderscore) = symbol "_"
  pretty (PUnitel) = string "()"
  pretty (PTake v fs) = prettyName v <+> record (fmap handleTakeAssign fs)
#ifdef BUILTIN_ARRAYS
  pretty (PArray ps) = array $ map pretty ps
  pretty (PArrayTake v ips) = prettyName v <+> string "@" <>
                              record (map (\(i,p) -> symbol "@" <> pretty i <+> symbol "=" <+> pretty p) ips)
#endif

instance Pretty RawIrrefPatn where
  pretty (RIP ip) = pretty ip

instance Pretty LocIrrefPatn where
  pretty (LocIrrefPatn _ ip) = pretty ip

instance (Pretty t, Pretty l) => Pretty (TIrrefPatn t l) where
  pretty (TIP ip _) = pretty ip

instance (PatnType ip, Pretty ip) => Pretty (Pattern ip) where
  pretty (PCon c [] )     = tagname c
  pretty (PCon c [p])     = tagname c <+> prettyP p
  pretty (PCon c ps )     = tagname c <+> spaceList (map prettyP ps)
  pretty (PIntLit i)      = literal (string $ show i)
  pretty (PBoolLit b)     = literal (string $ show b)
  pretty (PCharLit c)     = literal (string $ show c)
  pretty (PIrrefutable p) = pretty p

instance Pretty RawPatn where
  pretty (RP p) = pretty p

instance Pretty LocPatn where
  pretty (LocPatn _ p) = pretty p

instance (Pretty t, Pretty l) => Pretty (TPatn t l) where
  pretty (TP p _) = pretty p

instance (Pretty t, PatnType ip, PatnType p, Pretty p, Pretty e, Prec e) => Pretty (Binding t p ip e) where
  pretty (Binding p t e []) = prettyB (p,t,e) False
  pretty (Binding p t e bs)
     = prettyB (p,t,e) True <+> hsep (map (letbangvar . ('!':)) bs)
  pretty (BindingAlts p t e [] alts) = prettyB (p,t,e) False
                                    <> mconcat (map ((hardline <>) . indent . prettyA True) alts)
  pretty (BindingAlts p t e bs alts) = prettyB (p,t,e) True <+> hsep (map (letbangvar . ('!':)) bs)
                                    <> mconcat (map ((hardline <>) . indent . prettyA True) alts)

instance (Pretty p, Pretty e) => Pretty (Alt p e) where
  pretty (Alt p arrow e) = pretty p <+> group (pretty arrow <+> pretty e)

prettyA :: (Pretty p, Pretty e)
        => Bool  -- is biased
        -> Alt p e
        -> Doc
prettyA False alt = symbol "|" <+> pretty alt
prettyA True alt = symbol "|>" <+> pretty alt

instance Pretty Inline where
  pretty Inline = keyword "inline" <+> empty
  pretty NoInline = empty

instance (ExprType e, Prec e, Pretty t, PatnType p, Pretty p, PatnType ip, Pretty ip, Pretty e, Pretty l) =>
         Pretty (Expr t p ip l e) where
  pretty (Var x)             = varname x
  pretty (TLApp x ts ls note) = pretty note <> varname x
                                  <> typeargs (map (\case Nothing -> symbol "_"; Just t -> pretty t) ts)
                                  <> layoutargs (map (\case Nothing -> symbol "_"; Just t -> pretty t) ls)
  pretty (Member x f)        = prettyPrec 9 x <> symbol "." <> fieldname f
  pretty (IntLit i)          = literal (string $ show i)
  pretty (BoolLit b)         = literal (string $ show b)
  pretty (CharLit c)         = literal (string $ show c)
  pretty (StringLit s)       = literal (string $ show s)
#ifdef BUILTIN_ARRAYS
  pretty (ArrayLit es)       = array $ map pretty es
  pretty (ArrayIndex e i)    = prettyPrec 11 e <+> symbol "@" <+> prettyPrec 10 i
  pretty (ArrayMap2 ((p1,p2),f) (e1,e2)) = keyword "map2"
                                       <+> parens (string "\\" <> pretty p1 <+> pretty p2 <+> symbol "=>" <+> pretty f)
                                       <+> prettyPrec 1 e1 <+> prettyPrec 1 e2
  pretty (ArrayPut e es)     = prettyPrec 10 e <+> symbol "@"
                            <> record (map (\(i,e) -> symbol "@" <> pretty i <+> symbol "=" <+> pretty e) es)
#endif
  pretty (Unitel)            = string "()"
  pretty (PrimOp n [a,b])
     | LeftAssoc  l <- associativity n = prettyPrec (l+1) a <+> primop n <+> prettyPrec l     b
     | RightAssoc l <- associativity n = prettyPrec l     a <+> primop n <+> prettyPrec (l+1) b
     | NoAssoc    l <- associativity n = prettyPrec l     a <+> primop n <+> prettyPrec l     b
  pretty (PrimOp n [e])
     | a  <- associativity n = primop n <+> prettyPrec (prec a) e
  pretty (PrimOp n es)       = primop n <+> tupled (map pretty es)
  pretty (Upcast e)          = keyword "upcast" <+> prettyPrec 9 e
  pretty (Lam p mt e)        = string "\\" <> pretty p <>
                               (case mt of Nothing -> empty; Just t -> space <> symbol ":" <+> pretty t) <+> symbol "=>" <+> prettyPrec 101 e
  pretty (LamC p mt e _)     = pretty (Lam p mt e :: Expr t p ip l e)
  pretty (App  a b False)    = prettyPrec 10 a <+> prettyPrec 9 b
  pretty (App  a b True )    = prettyPrec 31 a <+> symbol "$" <+> prettyPrec 32 b
  pretty (Comp f g)          = prettyPrec 10 f <+> symbol "o" <+> prettyPrec 9 g
  pretty (AppC a b)          = prettyPrec 10 a <+> prettyPrec 9 b
  pretty (Con n [] )         = tagname n
  pretty (Con n es )         = tagname n <+> spaceList (map (prettyPrec 9) es)
  pretty (Tuple es)          = tupled (map pretty es)
  pretty (UnboxedRecord fs)  = string "#" <> record (map (handlePutAssign . Just) fs)
  pretty (If c vs t e)       = group (keyword "if" <+> handleBangedIf vs (prettyPrec 100 c)
                                                   <$> indent (keyword "then" </> pretty t)
                                                   <$> indent (keyword "else" </> pretty e))
    where handleBangedIf []  = id
          handleBangedIf vs  = (<+> hsep (map (letbangvar . ('!':)) vs))
  pretty (MultiWayIf es el)  = keyword "if" <+> mconcat (map ((hardline <>) . indent . (symbol "|" <+>) . prettyBranch) es)
                                            <> hardline <> indent (symbol "|" <+> keyword "else" <+> symbol "->" <+> pretty el)
    where handleBangedIf []  = id
          handleBangedIf vs  = (<+> hsep (map (letbangvar . ('!':)) vs))

          prettyBranch (c,bs,l,e) = handleBangedIf bs (prettyPrec 100 c) <+> pretty l <+> pretty e
  pretty (Match e [] alts)   = prettyPrec 100 e
                               <> mconcat (map ((hardline <>) . indent . prettyA False) alts)
  -- vvv It's a hack here. See the notes in <tests/pass_letbang-cond-type-annot.cogent>
  pretty (Match e bs alts)   = handleLetBangs bs (prettyPrec 30 e)
                               <> mconcat (map ((hardline <>) . indent . prettyA False) alts)
    where handleLetBangs bs  = (<+> hsep (map (letbangvar . ('!':)) bs))
  pretty (Seq a b)           = prettyPrec 100 a <> symbol ";" <$> pretty b
  pretty (Let []     e)      = __impossible "pretty (in RawExpr)"
  pretty (Let (b:[]) e)      = keyword "let" <+> indent (pretty b)
                                             <$> keyword "in" <+> indent (pretty e)
  pretty (Let (b:bs) e)      = keyword "let" <+> indent (pretty b)
                                             <$> vsep (map ((keyword "and" <+>) . indent . pretty) bs)
                                             <$> keyword "in" <+> indent (pretty e)
  pretty (Put e fs)          = prettyPrec 10 e <+> record (map handlePutAssign fs)
  pretty (Annot e t)         = prettyPrec 31 e <+> symbol ":" <+> pretty t

instance Pretty RawExpr where
  pretty (RE e) = pretty e

instance Pretty LocExpr where
  pretty (LocExpr _ e) = pretty e

instance (Pretty t, Pretty l) => Pretty (TExpr t l) where
  pretty (TE t e _) | __cogent_fshow_types_in_pretty = parens $ pretty e <+> comment "::" <+> pretty t
                    | otherwise = pretty e

instance (Pretty t, Pretty l) => Pretty (SExpr t l) where
  pretty (SE t e) | __cogent_fshow_types_in_pretty = parens $ pretty e <+> comment "::" <+> pretty t
                  | otherwise = pretty e
  pretty (SU t n) | __cogent_fshow_types_in_pretty = parens $ warn ('?':show n) <+> comment "::" <+> pretty t
                  | otherwise = warn ('?':show n)

instance Pretty RecursiveParameter where
  pretty (Rec p) = typesymbol "rec" <+> symbol p
  pretty NonRec  = empty

prettyT' :: (TypeType t, Pretty t) => t -> Doc
prettyT' t | not $ isAtomic t = parens (pretty t)
           | otherwise        = pretty t

instance (Pretty t, TypeType t, Pretty e, Pretty l, Eq l) => Pretty (Type e l t) where
  pretty (TCon n [] s) = (if | readonly s -> (<> typesymbol "!")
                             | s == Unboxed && n `notElem` primTypeCons -> (typesymbol "#" <>)
                             | otherwise -> id) . (case s of Boxed _ (Just l) -> (<+> typesymbol "layout" <+> pretty l); _ -> id) $ typename n
  pretty (TCon n as s) = (if | readonly s -> (<> typesymbol "!") . parens
                             | s == Unboxed -> ((typesymbol "#" <>) . parens)
                             | otherwise -> id) . (case s of Boxed _ (Just l) -> (<+> typesymbol "layout" <+> pretty l); _ -> id) $
                         typename n <+> hsep (map prettyT' as)
  pretty (TVar n b u) = (if u then typesymbol "#" else empty) <> typevar n <> (if b then typesymbol "!" else empty)
  pretty (TTuple ts) = tupled (map pretty ts)
  pretty (TUnit)     = typesymbol "()" & (if __cogent_fdisambiguate_pp then (<+> comment "{- unit -}") else id)
#ifdef BUILTIN_ARRAYS
  pretty (TArray t l s tkns) =
    let (sigilPretty, layoutPretty) = case s of
          Unboxed     -> ((typesymbol "#" <>), id)
          Boxed ro ml -> (if ro then (<> typesymbol "!") else id, case ml of Just l -> (<+> typesymbol "layout" <+> pretty l); _ -> id)
        (takes,puts) = partition snd tkns
        pTakens = if null takes then id else
                (<+> typesymbol "@take" <+> tupled (map (pretty . fst) takes))
        pPuts = id  -- default is put
        -- pPuts   = if null puts  then id else
        --         (<+> typesymbol "@put"  <+> tupled (map (pretty . fst) puts ))
     in prettyT' t <> (layoutPretty . sigilPretty $ brackets (pretty l)) & (pPuts . pTakens)
  pretty (TATake idxs t)
    = (prettyT' t <+> typesymbol "@take"
                  <+> tupled (map pretty idxs))
      & (if __cogent_fdisambiguate_pp then (<+> comment "{- @take -}") else id)
  pretty (TAPut  idxs t)
    = (prettyT' t <+> typesymbol "@put"
                  <+> tupled (map pretty idxs))
      & (if __cogent_fdisambiguate_pp then (<+> comment "{- @put -}") else id)
#endif
#ifdef REFINEMENT_TYPES
  pretty (TRefine v t e) = reftype (varname v) (pretty t) (pretty e)
#endif
  pretty (TRecord rp ts s) =
      let recordPretty = record (map (\(a,(b,c)) -> fieldname a <+> symbol ":" <+> pretty b) ts) -- all untaken
          tk = map fst $ filter (snd . snd) ts
          tkUntkPretty = (if or $ map (snd . snd) ts
                          then (<+> typesymbol "take" <+> tupled1 (map fieldname tk))
                          else id)
          (sigilPretty, layoutPretty) = case s of
            Unboxed     -> ((typesymbol "#" <>), id)
            Boxed rw ml -> (if rw then (<> typesymbol "!") else id, case ml of Just l -> (<+> typesymbol "layout" <+> pretty l); _ -> id)
       in pretty rp <+> (layoutPretty . tkUntkPretty . sigilPretty $ recordPretty)
  pretty (TVariant ts) | any snd ts = let
     names = map fst $ filter (snd . snd) $ M.toList ts
   in pretty (TVariant $ fmap (second (const False)) ts :: Type e l t)
        <+> typesymbol "take"
        <+> tupled1 (map fieldname names)
  pretty (TVariant ts) = variant (map (\(a,bs) -> case bs of
                                          [] -> tagname a
                                          _  -> tagname a <+> spaceList (map prettyT' bs)) $ M.toList (fmap fst ts))
  pretty (TFun t t') = prettyT' t <+> typesymbol "->" <+> prettyT' t'
    where prettyT' e | isFun e   = parens (pretty e)
                     | otherwise = pretty e
  pretty (TUnbox t) = (typesymbol "#" <> prettyT' t) & (if __cogent_fdisambiguate_pp then (<+> comment "{- unbox -}") else id)
  pretty (TBang t) = (prettyT' t <> typesymbol "!") & (if __cogent_fdisambiguate_pp then (<+> comment "{- bang -}") else id)
  pretty (TRPar v b m) = (if __cogent_fdisambiguate_pp then (comment "{- rec -}" <+> ) else id) $ typevar v <> (if b then typesymbol "!" else mempty)
  pretty (TTake fs x) = (prettyT' x <+> typesymbol "take"
                                    <+> case fs of Nothing  -> tupled (fieldname ".." : [])
                                                   Just fs' -> tupled1 (map fieldname fs'))
                        & (if __cogent_fdisambiguate_pp then (<+> comment "{- take -}") else id)
  pretty (TPut fs x) = (prettyT' x <+> typesymbol "put"
                                   <+> case fs of Nothing -> tupled (fieldname ".." : [])
                                                  Just fs' -> tupled1 (map fieldname fs'))
                       & (if __cogent_fdisambiguate_pp then (<+> comment "{- put -}") else id)
  pretty (TLayout l t) = (prettyT' t <+> typesymbol "layout" <+> pretty l)
           & (if __cogent_fdisambiguate_pp then (<+> comment "{- layout -}") else id)

instance Pretty RawType where
  pretty (RT t) = pretty t

instance Pretty DepType where
  pretty (DT t) = pretty t

instance Pretty TCType where
  pretty (T t) = pretty t
  pretty t@(V v) = symbol "V" <+> pretty v
  pretty t@(R rp v s) =
    let sigilPretty = case s of
                        Left s -> pretty s
                        Right n -> parens (symbol "?" <> pretty n)
        rpPretty    = case rp of
                        Mu v -> typesymbol "rec" <+> symbol v <+> empty
                        None -> empty
                        UP p -> parens (symbol "?" <> pretty p) <+> empty
     in symbol "R" <+> rpPretty <> pretty v <+> sigilPretty
#ifdef BUILTIN_ARRAYS
  pretty (A t l s row) =
    let sigilPretty = case s of
                        Left s -> pretty s
                        Right n -> parens (warn $ '?' : show n)
        holePretty = case row of
                       Left Nothing  -> empty
                       Left (Just e) -> space <> keyword "@take" <+> parens (pretty e)
                       Right n       -> space <> warn ('?' : show n)

     in symbol "A" <+> pretty t <+> brackets (pretty l) <+> sigilPretty <> holePretty
#endif
  pretty (U v) = warn ('?':show v)
  pretty (Synonym n []) = warn ("syn:" ++ n)
  pretty (Synonym n ts) = warn ("syn:" ++ n) <+> spaceList (map pretty ts)

instance Pretty LocType where
  pretty t = pretty (stripLocT t)

renderPolytypeHeader vs ts = keyword "all" <> tupled (map prettyKS vs ++ map prettyTS ts) <> symbol "."
    where prettyKS (v,K False False False) = typevar v
          prettyKS (v,k) = typevar v <+> symbol ":<" <+> pretty k
          prettyTS (v,t) = typevar v <+> symbol ":~" <+> pretty t

instance Pretty t => Pretty (Polytype t) where
  pretty (PT [] [] t) = pretty t
  pretty (PT vs ts t) = renderPolytypeHeader vs ts <+> pretty t

renderTypeDecHeader n vs = keyword "type" <+> typename n <> hcat (map ((space <>) . typevar) vs)
                                          <+> symbol "="

prettyFunDef :: (Pretty p, Pretty e, Pretty t) => Bool -> FunName -> Polytype t -> [Alt p e] -> Doc
prettyFunDef typeSigs v pt [Alt p Regular e] = (if typeSigs then (funname v <+> symbol ":" <+> pretty pt <$>) else id)
                                                 (funname v <+> pretty p <+> group (indent (symbol "=" <$> pretty e)))
prettyFunDef typeSigs v pt alts = (if typeSigs then (funname v <+> symbol ":" <+> pretty pt <$>) else id) $
                                       (indent (funname v <> mconcat (map ((hardline <>) . indent . prettyA False) alts)))

prettyConstDef typeSigs v t e  = (if typeSigs then (funname v <+> symbol ":" <+> pretty t <$>) else id) $
                                         (funname v <+> group (indent (symbol "=" <+> pretty e)))

instance (Pretty t, Pretty p, Pretty e) => Pretty (TopLevel t p e) where
  pretty (TypeDec n vs t) = keyword "type" <+> typename n <> hcat (map ((space <>) . typevar) vs)
                                           <+> indent (symbol "=" </> pretty t)
  pretty (RepDef f) = pretty f
  pretty (FunDef v pt alts) = prettyFunDef True v pt alts
  pretty (AbsDec v pt) = funname v <+> symbol ":" <+> pretty pt
  pretty (Include s) = keyword "include" <+> literal (string $ show s)
  pretty (IncludeStd s) = keyword "include <" <+> literal (string $ show s)
  pretty (AbsTypeDec n vs ts) = keyword "type" <+> typename n  <> hcat (map ((space <>) . typevar) vs)
                             <> (if F.null ts then empty else empty <+> symbol "-:" <+> commaList (map pretty ts))
  pretty (ConstDef v t e) = prettyConstDef True v t e
  pretty (DocBlock _) = __fixme empty  -- FIXME: doesn't PP docs right now

instance Pretty Kind where
  pretty k = kindsig (stringFor k)
    where stringFor k = (if canDiscard k then "D" else "")
                     ++ (if canShare   k then "S" else "")
                     ++ (if canEscape  k then "E" else "")

instance Pretty SourcePos where
  pretty p | __cogent_ffull_src_path = position (show p)
           | otherwise = position $ show $ setSourceName p (takeFileName $ sourceName p)

instance Pretty DataLayoutDecl where
  pretty (DataLayoutDecl _ n v e) = keyword "layout" <+> reprname n <+> hsep (fmap varname v) <+> indent (symbol "=" </> pretty e)

instance Pretty DataLayoutSize where
  pretty (Bits b) = literal (string (show b ++ "b"))
  pretty (Bytes b) = literal (string (show b ++ "B"))
  pretty (Add a b) = pretty a <+> symbol "+" <+> pretty b

instance Pretty Endianness where
  pretty LE = keyword "LE"
  pretty BE = keyword "BE"
  pretty ME = err "Invalid endianness" <+> keyword "ME"

instance Pretty d => Pretty (DataLayoutExpr' d) where
  pretty (RepRef n s) = if null s then reprname n else parens $ reprname n <+> hsep (fmap pretty s)
  pretty (Prim sz) = pretty sz
  pretty (Offset e s) = pretty e <+> keyword "at" <+> pretty s
  pretty (After e f) = pretty e <+> keyword "after" <+> pretty f
  pretty (Endian e n) = pretty e <+> keyword "using" <+> pretty n
  pretty (Record fs) = keyword "record" <+> record (map (\(f,_,e) -> fieldname f <+> symbol ":" <+> pretty e ) fs)
  pretty (Variant e vs) = keyword "variant" <+> parens (pretty e)
                                                 <+> record (map (\(f,_,i,e) -> tagname f <+> tupled [literal $ string $ show i] <> symbol ":" <+> pretty e) vs)
#ifdef BUILTIN_ARRAYS
  pretty (Array e s) = keyword "array" <+> parens (pretty e) <+> keyword "at" <+> pretty s
#endif
  pretty Ptr = keyword "pointer"
  pretty (LVar n) = dlvarname n

instance Pretty DataLayoutExpr where
  pretty (DL l) = pretty l

instance Pretty TCDataLayout where
  pretty (TL l) = pretty l
  pretty (TLU n) = warn ('?':show n)

instance Pretty Metadata where
  pretty (Constant {constName})              = err "the binding" <+> funname constName <$> err "is a global constant"
  pretty (Reused {varName, boundAt, usedAt}) = err "the variable" <+> varname varName
                                               <+> err "bound at" <+> pretty boundAt <> err ""
                                               <$> err "was already used at"
                                               <$> indent' (vsep $ map pretty $ F.toList usedAt)
  pretty (Unused {varName, boundAt}) = err "the variable" <+> varname varName
                                       <+> err "bound at" <+> pretty boundAt <> err ""
                                       <$> err "was never used."
  pretty (UnusedInOtherBranch {varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "bound at" <+> pretty boundAt <> err ""
    <$> err "was used in another branch of control at"
    <$> indent' (vsep $ map pretty $ F.toList usedAt)
    <$> err "but not this one."
  pretty (UnusedInThisBranch {varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "bound at" <+> pretty boundAt <> err ""
    <$> err "was used in this branch of control at"
    <$> indent' (vsep $ map pretty $ F.toList usedAt)
    <$> err "but not in all other branches."
  pretty Suppressed = err "a binder for a value of this type is being suppressed."
  pretty (UsedInMember {fieldName}) = err "the field" <+> fieldname fieldName
                                       <+> err "is being extracted without taking the field in a pattern."
#ifdef BUILTIN_ARRAYS
  pretty UsedInArrayIndexing = err "an element of the array is being accessed"
  pretty MultipleArrayTakePut = err "more than one array element is being taken or put"
#endif
  pretty UsedInLetBang = err "it is being returned from such a context."
  pretty (TypeParam {functionName, typeVarName }) = err "it is required by the type of" <+> funname functionName
                                                      <+> err "(type variable" <+> typevar typeVarName <+> err ")"
  pretty ImplicitlyTaken = err "it is implicitly taken via subtyping."
  -- pretty (LayoutParam exp lv) = err "it is required by the expression" <+> pretty exp
                            -- <+> err "(layout variable" <+> dlvarname lv <+> err ")"

instance Pretty FuncOrVar where
  pretty MustFunc  = err "Function"
  pretty MustVar   = err "Variable"
  pretty FuncOrVar = err "Variable or function"

instance Pretty TypeError where
  pretty (DifferingNumberOfConArgs f n m) = err "Constructor" <+> tagname f
                                        <+> err "invoked with differing number of arguments (" <> int n <> err " vs " <> int m <> err ")"
  pretty (DuplicateTypeVariable vs)      = err "Duplicate type variable(s)" <+> commaList (map typevar vs)
  pretty (SuperfluousTypeVariable vs)    = err "Superfluous type variable(s)" <+> commaList (map typevar vs)
  pretty (DuplicateLayoutVariable vs)    = err "Duplicate layout variable(s)" <+> commaList (map dlvarname vs)
  pretty (SuperfluousLayoutVariable vs)  = err "Superfluous layout variable(s)" <+> commaList (map dlvarname vs)
  pretty (TypeVariableNotDeclared vs)    = err "Type variable(s) not declared" <+> commaList (map typevar vs)
  pretty (DuplicateRecordFields fs)      = err "Duplicate record field(s)" <+> commaList (map fieldname fs)
  pretty (FunctionNotFound fn)           = err "Function" <+> funname fn <+> err "not found"
  pretty (TooManyTypeArguments fn pt)    = err "Too many type arguments to function"
                                           <+> funname fn <+> err "of type" <+> pretty pt
  pretty (TooManyLayoutArguments fn pt)  = err "Too many layout arguments to function"
                                           <+> funname fn <+> err "of type" <+> pretty pt
  pretty (NotInScope fov vn)             = pretty fov <+> varname vn <+> err "not in scope"
  pretty (UnknownTypeVariable vn)        = err "Unknown type variable" <+> typevar vn
  pretty (UnknownTypeConstructor tn)     = err "Unknown type constructor" <+> typename tn
  pretty (TypeArgumentMismatch tn provided required)
                                         = typename tn <+> err "expects"
                                           <+> int required <+> err "arguments, but has been given" <+> int provided
  pretty (TypeMismatch t1 t2)            = err "Mismatch between" <$> indent' (pretty t1)
                                           <$> err "and" <$> indent' (pretty t2)
  pretty (RequiredTakenField f t)        = err "Field" <+> fieldname f <+> err "of type" <+> pretty t
                                           <+> err "is required, but has been taken"
  pretty (TypeNotShareable t m)          = err "Cannot share type" <+> pretty t
                                           <$> err "but this is needed as" <+> pretty m
  pretty (TypeNotEscapable t m)          = err "Cannot let type" <+> pretty t <+> err "escape from a !-ed context,"
  pretty (TypeNotDiscardable t m)        = err "Cannot discard type" <+> pretty t
                                           <+> err "but this is needed as" <+> pretty m
  pretty (PatternsNotExhaustive t tags)  = err "Patterns not exhaustive for type" <+> pretty t
                                           <$> err "cases not matched" <+> tupled1 (map tagname tags)
  pretty (UnsolvedConstraint c os)       = analyseLeftover c os
  pretty (RecordWildcardsNotSupported)   = err "Record wildcards are not supported"
  pretty (NotAFunctionType t)            = err "Type" <+> pretty t <+> err "is not a function type"
  pretty (DuplicateVariableInPattern vn) = err "Duplicate variable" <+> varname vn <+> err "in pattern"
  -- pretty (DuplicateVariableInPattern vn pat)       = err "Duplicate variable" <+> varname vn <+> err "in pattern:"
  --                                                    <$> pretty pat
  -- pretty (DuplicateVariableInIrrefPattern vn ipat) = err "Duplicate variable" <+> varname vn <+> err "in (irrefutable) pattern:"
  --                                                    <$> pretty ipat
  pretty (TakeFromNonRecordOrVariant fs t) = err "Cannot" <+> keyword "take" <+> err "fields"
                                             <+> (case fs of Nothing  -> tupled (fieldname ".." : [])
                                                             Just fs' -> tupled1 (map fieldname fs'))
                                             <+> err "from non record/variant type:"
                                             <$> indent' (pretty t)
  pretty (PutToNonRecordOrVariant fs t)    = err "Cannot" <+> keyword "put" <+> err "fields"
                                             <+> (case fs of Nothing  -> tupled (fieldname ".." : [])
                                                             Just fs' -> tupled1 (map fieldname fs'))
                                             <+> err "into non record/variant type:"
                                             <$> indent' (pretty t)
  pretty (TakeNonExistingField f t) = err "Cannot" <+> keyword "take" <+> err "non-existing field"
                                      <+> fieldname f <+> err "from record/variant" <$> indent' (pretty t)
  pretty (PutNonExistingField f t)  = err "Cannot" <+> keyword "put" <+> err "non-existing field"
                                      <+> fieldname f <+> err "into record/variant" <$> indent' (pretty t)
  pretty (DiscardWithoutMatch t)    = err "Variant tag"<+> tagname t <+> err "cannot be discarded without matching on it."
  pretty (RequiredTakenTag t)       = err "Required variant" <+> tagname t <+> err "but it has already been matched."
#ifdef BUILTIN_ARRAYS
  pretty (ArithConstraintsUnsatisfiable es msg) = err "The following arithmetic constraints are unsatisfiable" <> colon
                                              <$> indent' (vsep (map ((<> semi) . pretty) es))
                                              <$> err "The SMT-solver comments" <> colon
                                              <$> indent' (pretty msg)
  pretty (TakeElementsFromNonArrayType is t) = err "Taking elements" <+> commaList (map pretty is)
                                           <$> err "from a non-array type" <+> pretty t
  pretty (PutElementsToNonArrayType is t)    = err "Putting elements" <+> commaList (map pretty is)
                                           <$> err "to a non-array type" <+> pretty t
#endif
  pretty (CustTyGenIsSynonym t)     = err "Type synonyms have to be fully expanded in --cust-ty-gen file:" <$> indent' (pretty t)
  pretty (CustTyGenIsPolymorphic t) = err "Polymorphic types are not allowed in --cust-ty-gen file:" <$> indent' (pretty t)
  pretty (DataLayoutError e)        = err "Data Layout Error:" <$> indent' (pretty e)
  pretty (LayoutOnNonRecordOrCon t) = err "Tried to put a layout onto something that isn't a record or abstract type:" <$> indent' (pretty t)
  pretty (LayoutDoesNotMatchType l t) = err "Layout " <$$> indent' (pretty l)
                                          <$$> err " does not match type " <$$> indent' (pretty t)
  pretty (LayoutsNotCompatible l1 l2) = err "Layout " <$$> indent' (pretty l1)
                                          <$$> err " is not compatible with layout " <$$> indent' (pretty l2)
  pretty (TypesNotFit t1 t2)          = err "The layout of type " <$$> indent' (pretty t1)
                                          <$$> err " does not fit the layout of type " <$$> indent' (pretty t2)
  pretty (TypeWarningAsError w)       = pretty w

instance Pretty TypeWarning where
  pretty (UnusedLocalBind v) = warn "[--Wunused-local-binds]" <$$> indent' (warn "Defined but not used:" <+> pretty v)
  pretty (TakeTakenField f t) = warn "[--Wdodgy-take-put]" <$$> indent' (warn "Take a taken field" <+> fieldname f
                                  <+> warn "from type" <$> pretty t)
  pretty (PutUntakenField f t) = warn "[--Wdodgy-take-put]" <$$> indent' (warn "Put an untaken field" <+> fieldname f
                                  <+> warn "into type" <$> pretty t)

instance Pretty TcLog where
  pretty = either ((err "Error:" <+>) . pretty) ((warn "Warning:" <+>) . pretty)

instance Pretty VarOrigin where
  pretty (ExpressionAt l) = warn ("the term at location " ++ show l)
  pretty (TermInType e t l) = warn "the term" <+> pretty e <$>
                              warn "of type" <+> pretty t <$>
                              warn ("at location" ++ show l)
  pretty (TypeOfExpr e bs l) = warn "the type of expression" <+> pretty e <> bangs bs <$>
                               warn ("at location " ++ show l)
    where bangs [] = empty; bangs ts = empty <+> symbol "!" <> parens (spaceList $ fmap letbangvar bs)
  pretty (TypeOfPatn p l) = warn "the type of pattern" <+> pretty p <$>
                            warn ("at location " ++ show l)
  pretty (TypeOfIrrefPatn p l) = warn "the type of pattern" <+> pretty p <$>
                                 warn ("at location " ++ show l)
  pretty (ImplicitTypeApp l) = warn ("implicit type application at location " ++ show l) 
  pretty (ImplicitLayoutApp l) = warn ("implicit layout application at location " ++ show l) 
  pretty (TypeHole l) = warn ("type hole at location " ++ show l)
  pretty (LayoutHole l) = warn ("layout hole at location " ++ show l)
  pretty (UnifyingRows r1 r2) = warn "the solver when trying to unify rows" <$>
                                pretty r1 <+> warn "and" <+> pretty r2
  pretty (SinkFloat u s t) = warn "the solver's sink/float phase when breaking up type" <+> pretty u <$>
                             warn "to" <+> pretty s <$>
                             warn "because it should have the same structure as type" <+> pretty t
  pretty (SinkFloatRow u r t1 t2) = warn ("the solver's sink/float phase when breaking up row variable ?" ++ show u) <$>
                                    warn "to" <+> pretty r <$>
                                    warn "when comparing types" <+> pretty t1 <+> warn "and" <+> pretty t2
  pretty (SinkFloatEntry e t1 t2) = warn "populating the entry" <+> pretty e <$>
                                    warn "when comparing types" <+> pretty t1 <+> warn "and" <+> pretty t2 <$>
                                    warn "in the solver's sink/float phase"
  pretty (SinkFloatSigil t1 t2) = warn "the sigil in" <+> pretty t1 <$>
                                  warn "when comparing it with" <+> pretty t2 <$>
                                  warn "in the solver's sink/float phase"
  pretty (BoundOf a b d) = warn ("taking the " ++ show d ++ " of") <$>
                           pretty a <+> warn "and" <+> pretty b
  pretty (EqualIn e1 e2 t1 t2) = __todo "pretty (VarOrigin)"
  pretty (BlockedByType t l) = warn "other errors in type well-formedness of" <+> pretty t
                           <$> warn ("at location " ++ show l)
  pretty (BlockedByLayout r l) = warn "other errors in layout well-formedness of" <+> pretty r
                             <$> warn ("at location " ++ show l)
  pretty (OtherOrigin s) = warn s

analyseLeftover :: Constraint -> I.IntMap VarOrigin -> Doc
{-
analyseLeftover c@(F t :< F u) os
    | Just t' <- flexOf t
    , Just u' <- flexOf u
    = vcat $ err "A subtyping constraint" <+>  pretty c <+> err "can't be solved because both sides are unknown."
           : map (\i -> warn "• The unknown" <+> pretty (U i) <+> warn "originates from" <+> pretty (I.lookup i os))
                 (nub [t',u'])
    | Just t' <- flexOf t
    = vcat $ (case t of
        U _ -> err "Constraint" <+> pretty c <+> err "can't be solved as another constraint blocks it."
        _   -> err "A subtyping constraint" <+>  pretty c
           <+> err "can't be solved because the LHS is unknown and uses non-injective operators (like !).")
             : map (\i -> warn "• The unknown" <+> pretty (U i) <+> warn "originates from" <+> pretty (I.lookup i os)) ([t'])
    | Just u' <- flexOf u
    = vcat $ (case u of
        U _ -> err "Constraint" <+> pretty c <+> err "can't be solved as another constraint blocks it."
        _   -> err "A subtyping constraint" <+>  pretty c
           <+> err "can't be solved because the RHS is unknown and uses non-injective operators (like !).")
             : map (\i -> warn "• The unknown" <+> pretty (U i) <+> warn "originates from" <+> pretty (I.lookup i os)) ([u']) -}
analyseLeftover c os =
#ifdef BUILTIN_ARRAYS
  case bifoldMap (\t -> unifVars t ++ unknowns t) unifLVars c of
#else
  case bifoldMap unifVars unifLVars c of
#endif
    [] -> err "Constraint" <$> indent' (pretty c) <$> err "cannot be solved, or is unsatisfiable."
    xs -> err "Constraint" <$> indent' (pretty c) <$> err "cannot be solved, or is unsatisfiable."
          <$$> indent' (context "with relevant unifiers:"
               <$$> indent' (vcat $ fmap (originInfo os) xs))
  where originInfo os x = warn "•" <+>
                            align (warn "The unknown" <+> pretty (U x) <+> warn "originates from" <+>
                            prettyOrigin (I.lookup x os))
        prettyOrigin Nothing  = warn "unknown origin"
        prettyOrigin (Just o) = pretty o

instance Pretty Constraint where
  pretty (a :< b)         = pretty a </> warn ":<" </> pretty b
  pretty (a :=: b)        = pretty a </> warn ":=:" </> pretty b
  pretty (a :& b)         = prettyPrec 4 a </> warn ":&" </> prettyPrec 3 b
  pretty (Upcastable a b) = pretty a </> warn "~>" </> pretty b
  pretty (Share  t m)     = warn "Share" <+> pretty t
  pretty (Drop   t m)     = warn "Drop" <+> pretty t
  pretty (Escape t m)     = warn "Escape" <+> pretty t
  pretty (Unsat e)        = err  "Unsat"
  pretty (SemiSat w)      = warn "SemiSat"
  pretty (Sat)            = warn "Sat"
  pretty (UnboxedNotRecursive t)
                          = warn "UnboxedNotRecursive" <+> pretty t
  pretty (NotReadOnly s)  = warn "NotReadOnly" <+> prettyS s
    where prettyS (Left  l) = pretty l
          prettyS (Right x) = warn ('?':show x)
  pretty (Exhaustive t p) = warn "Exhaustive" <+> pretty t <+> pretty p
  pretty (Solved t)       = warn "Solved" <+> pretty t
  pretty (IsPrimType t)   = warn "IsPrimType" <+> pretty t
  pretty (x :@ _)         = pretty x
#ifdef BUILTIN_ARRAYS
  pretty (Arith e)        = pretty e
  pretty (a :-> b)        = prettyPrec 2 a </> warn ":->" </> prettyPrec 1 b
#endif
  pretty (LayoutOk t)     = warn "LayoutOk" <+> pretty t
  pretty (l :~ n)         = pretty l </> warn ":~" </> pretty n
  pretty (l :~< m)        = pretty l </> warn ":~<" </> pretty m
  pretty (a :~~ b)        = pretty a </> warn ":~~" </> pretty b

-- a more verbose version of constraint pretty-printer which is mostly used for debugging
prettyC :: Constraint -> Doc
prettyC (Unsat e) = errbd "Unsat" <$> pretty e
prettyC (SemiSat w) = warn "SemiSat" -- <$> pretty w
prettyC (a :& b) = prettyCPrec 4 a </> warn ":&" <$> prettyCPrec 3 b
prettyC (c :@ e) = prettyCPrec 3 c & (if __cogent_ddump_tc_ctx then (</> prettyCtx e False) else (</> warn ":@ ..."))
#ifdef BUILTIN_ARRAYS
prettyC (a :-> b) = prettyCPrec 2 a </> warn ":->" </> prettyCPrec 1 b
#endif
prettyC c = pretty c

prettyCPrec :: Int -> Constraint -> Doc
prettyCPrec l x | prec x < l = prettyC x
                | otherwise  = parens (indent (prettyC x))

instance Pretty SourceObject where
  pretty (TypeName n) = typename n
  pretty (ValName  n) = varname n
  pretty (RepName  n) = reprname n
  pretty (DocBlock' _) = __fixme empty  -- FIXME: not implemented

instance Pretty ReorganizeError where
  pretty CyclicDependency = err "cyclic dependency"
  pretty DuplicateTypeDefinition = err "duplicate type definition"
  pretty DuplicateValueDefinition = err "duplicate value definition"
  pretty DuplicateRepDefinition = err "duplicate repr definition"
  pretty NonStrictlyPositive = err "non strictly positive occurence of recursive type"
  pretty RecParShadowsTyVar = err "recursive parameter shadows type variable"

instance Pretty Subst where
  pretty (Subst m) = pretty m

instance Pretty AssignResult where
  pretty (Type t) = pretty t
  pretty (Sigil s) = pretty s
  pretty (Row (Left r)) = pretty r
  pretty (Row (Right sh)) = pretty sh
  pretty (Layout' l) = pretty l
#ifdef BUILTIN_ARRAYS
  pretty (ARow r) = pretty r
  pretty (Expr e) = pretty e
  pretty (Hole h) = case h of
                      Nothing -> empty
                      Just h' -> keyword "@take" <+> parens (pretty h')
#endif
  pretty (RecP r) = pretty r

instance Pretty RP where
  pretty (Mu t) = typevar t
  pretty (None) = pretty "None"
  pretty (UP i) = warn ('?':show i)

instance Pretty r => Pretty (Sigil r) where
  pretty (Boxed False l) = keyword "[W]" <+> parens (pretty l)
  pretty (Boxed True  l) = keyword "[R]" <+> parens (pretty l)
  pretty Unboxed  = keyword "[U]"

instance (Pretty t) => Pretty (Row.Row t) where
  pretty r =
    let rowFieldsDoc =
          hsep $ punctuate (text ",") $ map pretty (Row.entries r)
        prettyRowVar Nothing  = symbol "✗"
        prettyRowVar (Just x) = symbol "?" <> pretty x
     in enclose (text "❲") (text "❳") (rowFieldsDoc <+> symbol "|" <+> prettyRowVar (Row.var r))

instance Pretty t => Pretty (Row.Entry t) where
  pretty e =
    let tkDoc = case Row.taken e of
          True  -> text "taken"
          False -> text "present"
    in text (Row.fname e) <+> text ":" <+> pretty (Row.payload e) <+>
       parens tkDoc

instance (Pretty e, Show e) => Pretty (ARow.ARow e) where
  pretty (ARow.ARow m u a v) = typesymbol "A-row" <+> brackets (pretty m <+> symbol "|" <+> pretty u <> all <> var)
    where var = case v of Nothing -> empty; Just x -> (symbol " |" <+> symbol "?" <> pretty x)
          all = case a of Nothing -> empty
                          Just True  -> (symbol " |" <+> text "all taken")
                          Just False -> (symbol " |" <+> text "all put"  )

instance Pretty a => Pretty (I.IntMap a) where
  pretty = align . vcat . map (\(k,v) -> pretty k <+> text "|->" <+> pretty v) . I.toList


instance Pretty DataLayoutTcError where
  pretty (OverlappingBlocks blks)
    = err "The following pairs of declared data blocks cannot overlap:" <$$>
      vcat (map (\((r1,c1),(r2,c2)) -> indent' (pretty r1 <+> pretty c1 <$>
                                                err "and" <$>
                                                pretty r2 <+> pretty c2))
           (fmap unOverlappingAllocationBlocks blks))
  pretty (UnknownDataLayout r ctx) 
    =  err "Undeclared data layout" <+> reprname r <$$> pretty ctx

  pretty (BadDataLayout l p) = err "Bad data layout" <+> pretty l
  pretty (TagSizeTooLarge ctx) =
    err "Variant tag allocated more bits than necessary" <$$> pretty ctx
  pretty (TagNotSingleBlock ctx) =
    err "Variant tag must be a single block of bits" <$$> pretty ctx
  pretty (SameTagValues context name1 name2 value) =
    err "Alternatives" <+> tagname name1 <+> err "and" <+> tagname name2 <+> err "of same variant cannot have the same tag value" <+> literal (pretty value) <$$>
    indent (pretty context)
  pretty (OversizedTagValue context range altName value) =
    err "Oversized tag value" <+> literal (pretty value) <+> err "for tag data block" <+> pretty range <+> err "in variant alternative" <+> tagname altName <$$>
    indent (pretty context)
  pretty (ZeroSizedBitRange context) =
    err "Zero-sized bit range" <$$>
    indent (pretty context)
  pretty (UnknownDataLayoutVar n ctx) =
    err "Undeclared data layout variable" <+> dlvarname n <$$> indent (pretty ctx)
  pretty (DataLayoutArgsNotMatch n exp act ctx) =
    err "Number of arguments for data layout synonym" <+> reprname n <+> err "not matched,"
    </> err "expected" <+> int exp <+> err "args, but actual" <+> int act <+> err "args"
    <$$> indent (pretty ctx)
  pretty (OverlappingFields fs ctx) =
    err "Overlapping fields" <+> foldr1 (<+>) (fmap fieldname fs) <$$> indent (pretty ctx)
  pretty (CyclicFieldDepedency fs ctx) =
    err "Cyclic dependency of fields" <+> foldr1 (<+>) (fmap fieldname fs) <$$> indent (pretty ctx)
  pretty (NonExistingField f ctx) =
    err "Non-existing field" <+> symbol "after" <+> fieldname f <$$> indent (pretty ctx)
  pretty (InvalidUseOfAfter f ctx) =
    err "The use of" <+> symbol "after" <+> fieldname f <+> err "layout expression is invalid" <$$> indent (pretty ctx)
  pretty (InvalidEndianness end ctx) =
    err "Endianness" <+> pretty end <+> err "can only be applied to int sizes"

instance Pretty DataLayoutPath where
  pretty (InField n po ctx) = context' "for field" <+> fieldname n <+> context' "(" <> pretty po <> context' ")" </> pretty ctx
  pretty (InTag ctx)        = context' "for the variant tag block" </> pretty ctx
  pretty (InAlt t po ctx)   = context' "for the constructor" <+> tagname t <+> context' "(" <> pretty po <> context' ")" </> pretty ctx
#ifdef BUILTIN_ARRAYS
  pretty (InElmt po ctx)    = context' "in the array element (" <> pretty po <> context' ")" </> pretty ctx
#endif
  pretty (InDecl n p)       = context' "in the representation" <+> reprname n <+> context' "(" <> pretty p <> context' ")"
  pretty (PathEnd)          = mempty

instance Pretty a => Pretty (DataLayout a) where
  pretty (Layout l) = symbol "layout" <+> pretty l
  pretty CLayout = symbol "c-layout"

instance Pretty a => Pretty (DataLayout' a) where
  pretty UnitLayout =
    parens (literal (symbol "unit"))

  pretty PrimLayout {bitsDL, endianness} =
    parens (pretty bitsDL <+> keyword "using" <+> pretty endianness)

  pretty SumLayout {tagDL, alternativesDL} =
    parens (pretty tagDL) <> variant (map prettyAlt $ M.toList alternativesDL)
    where prettyAlt (n,(v,l)) = tagname n <> parens (integer $ fromIntegral v) <> colon <> pretty l

  pretty RecordLayout {fieldsDL} =
    record (map prettyField $ M.toList fieldsDL)
    where prettyField (f,l) = fieldname f <+> symbol ":" <+> pretty l
#ifdef BUILTIN_ARRAYS
  pretty (ArrayLayout l) = brackets (pretty l)
#endif
  pretty (VarLayout n s) = (dullcyan . string . ("_l" ++) . show $ natToInt n) <> prettyOffset s
    where prettyOffset 0 = empty
          prettyOffset n = space <> symbol "offset" <+> integer n <> symbol "b"

instance Pretty BitRange where
  pretty br = literal (pretty $ bitSizeBR br) <> symbol "b" <+> symbol "at" <+> literal (pretty $ bitOffsetBR br) <> symbol "b"


-- helper functions
-- ~~~~~~~~~~~~~~~~~~~~~~~~~

-- assumes positive `n`
nth :: Int -> Doc
nth n = context $ show n ++ ordinalOf n

ordinalOf :: Int -> String
ordinalOf n =
  let (d,m) = divMod n 10
   in if d == 1
      then "th"
      else
        case m of
          1 -> "st"
          2 -> "nd"
          3 -> "rd"
          _ -> "th"


-- ctx -> indent -> doc
prettyCtx :: ErrorContext -> Bool -> Doc
prettyCtx (SolvingConstraint c) _ = context "from constraint" <+> indent (pretty c)
prettyCtx (ThenBranch) _ = context "in the" <+> keyword "then" <+> context "branch"
prettyCtx (ElseBranch) _ = context "in the" <+> keyword "else" <+> context "branch"
prettyCtx (NthBranch n) _ = context "in the" <+> nth n <+> context "branch of a multiway-if"
prettyCtx (InExpression e t) True = context "when checking that the expression at ("
                                      <> pretty (posOfE e) <> context ")"
                                      <$> (indent' (pretty (stripLocE e)))
                                      <$> context "has type" <$> (indent' (pretty t))
prettyCtx (InExpression e t) False = context "when checking the expression at ("
                                       <> pretty (posOfE e) <> context ")"
prettyCtx (InType l t) True  = context "when checking well-formedness of the type at ("
                                 <> pretty l <> context ")"
                                 <$> indent' (pretty t)
prettyCtx (InType l t) False = context "when checking well-formedness of the type at ("
                                 <> pretty l <> context ")"
-- FIXME: more specific info for patterns
prettyCtx (InPattern p) True = context "when checking the pattern at ("
                                 <> pretty (posOfP p) <> context ")"
                                 <$> (indent' (pretty (stripLocP p)))
prettyCtx (InPattern p) False = context "when checking the pattern at ("
                                  <> pretty (posOfP p) <> context ")"
prettyCtx (InIrrefutablePattern ip) True = context "when checking the pattern at ("
                                             <> pretty (posOfIP ip) <> context ")"
                                             <$> (indent' (pretty (stripLocIP ip)))
prettyCtx (InIrrefutablePattern ip) False = context "when checking the pattern at ("
                                              <> pretty (posOfIP ip) <> context ")"
prettyCtx (NthAlternative n p) _ = context "in the" <+> nth n <+> context "alternative" <+> pretty p
prettyCtx (InDefinition p tl) _ = context "in the definition at (" <> pretty p <> context ")"
                               <$> context "for the" <+> helper tl
  where helper (TypeDec n _ _) = context "type synonym" <+> typename n
        helper (AbsTypeDec n _ _) = context "abstract type" <+> typename n
        helper (AbsDec n _) = context "abstract function" <+> varname n
        helper (ConstDef v _ _) = context "constant" <+> varname v
        helper (FunDef v _ _) = context "function" <+> varname v
        helper (RepDef (DataLayoutDecl _ n v _)) = context "representation" <+> reprname n <+> hsep (fmap varname v)
        helper _  = __impossible "helper"
prettyCtx (AntiquotedType t) i = (if i then (<$> indent' (pretty (stripLocT t))) else id)
                               (context "in the antiquoted type at (" <> pretty (posOfT t) <> context ")" )
prettyCtx (AntiquotedExpr e) i = (if i then (<$> indent' (pretty (stripLocE e))) else id)
                               (context "in the antiquoted expression at (" <> pretty (posOfE e) <> context ")" )
prettyCtx (InAntiquotedCDefn n) _ = context "in the antiquoted C definition" <+> varname n
prettyCtx (CustomisedCodeGen t) _ = context "in customising code-generation for type" <+> pretty t

handleTakeAssign :: (PatnType ip, Pretty ip) => Maybe (FieldName, ip) -> Doc
handleTakeAssign Nothing = fieldname ".."
handleTakeAssign (Just (s, e)) | isPVar e s = fieldname s
handleTakeAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> pretty e

handlePutAssign :: (ExprType e, Pretty e) => Maybe (FieldName, e) -> Doc
handlePutAssign Nothing = fieldname ".."
handlePutAssign (Just (s, e)) | isVar e s = fieldname s
handlePutAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> pretty e


-- top-level function
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~

-- typechecker errors/warnings
prettyTWE :: Int -> ContextualisedTcLog -> Doc
prettyTWE th (ectx, l) = pretty l <$> indent' (vcat (map (flip prettyCtx True ) (take th ectx)
                                                  ++ map (flip prettyCtx False) (drop th ectx)))

-- reorganiser errors
prettyRE :: (ReorganizeError, [(SourceObject, SourcePos)]) -> Doc
prettyRE (msg,ps) = pretty msg <$>
                    indent' (vcat (map (\(so,p) -> context "-" <+> pretty so
                                               <+> context "(" <> pretty p <> context ")") ps))

prettyPrint :: Pretty a => (Doc -> Doc) -> [a] -> SimpleDoc
prettyPrint f = renderSmart 1.0 120 . f . vcat . map pretty


