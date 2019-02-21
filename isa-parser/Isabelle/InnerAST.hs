--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DeriveDataTypeable #-}

module Isabelle.InnerAST where

-- system imports
import Data.Data
import Data.List
import Data.Typeable
import Text.Parsec.Expr (Assoc(..))
import Text.PrettyPrint.ANSI.Leijen
import Data.Char (ord)
import Text.Printf (printf)

-- friends
import Isabelle.PrettyHelper

--
-- The AST for the term language does NOT follow the definition in the ISAR Reference manual
-- exactly. This is because first-order and higher-order logic syntax is defined using Isabelle's
-- extensible syntax. Here we have amalgamated the base term language, and other admissible terms
-- defined in other theory files into one AST to simplify the implementation.
--
--
data Term = TermIdent      Ident
          | TermApp                   Term    Term
          | TermWithType              Term    Type  -- A :: bool
          | QuantifiedTerm Quantifier [Ident] Term  -- \\<
          | TermUnOp       TermUnOp   Term
          | TermBinOp      TermBinOp  Term    Term
          | AntiTerm       String
          | ConstTerm      Const
          | ListTerm       String     [Term]  String
          | CaseOf         Term       [(Term, Term)]
  deriving (Data, Typeable, Eq, Ord, Show)

data Const = TrueC | FalseC
           | IntLiteral    Integer
           | CharLiteral   Char
           | StringLiteral String
           | Top | Bottom
 deriving (Data, Typeable, Eq, Ord, Show)

data Quantifier = MetaBind    -- \<And>
                | Lambda
                | Forall      -- \<forall>
                | Exists      -- \<exists>
                | ExistsBang
  deriving (Data, Typeable, Eq, Ord, Show)

data TermBinOp =
              -- Isabelle/Pure
                 Equiv
               | MetaImp -- ==> or \<Longrightarrow>
              -- Isabelle/HOL
               | Eq
               | NotEq
               | Iff
               | Conj
               | Disj
               | Implies
  deriving (Data, Typeable, Eq, Ord, Show)

data TermUnOp =
  -- Isabelle/HOL
  Not deriving (Data, Typeable, Eq, Ord, Show)

type Id = String

data Ident = Id Id
           | Wildcard
           | TypedIdent Ident Type
  deriving (Data, Typeable, Eq, Ord, Show)

data PrimType = IntT
              | BoolT
              | NatT
  deriving (Data, Typeable, Eq, Ord, Show)

data Type = TyVar      String
          | TyDatatype String   [Type]
          | TyPrim     PrimType
          | TyArrow    Type     Type
          | AntiType   String
          | TyTuple    Type     Type
  deriving (Data, Typeable, Eq, Ord, Show)

-- typeToId :: Type -> Id
-- typeToId (TyDatatype s ts) = s
-- typeToId _ = error "panic: typeToId: must be datatype"

data Arity = Arity (Maybe [Sort]) Sort deriving (Data, Typeable, Eq, Ord, Show)

type Sort = Id  -- FIXME: zilinc

-- Smart constructors

mkId :: Id -> Term
mkId = TermIdent . Id

mkTru = ConstTerm TrueC
mkFls = ConstTerm FalseC

mkInt    = ConstTerm . IntLiteral
mkBool b = if b then mkTru else mkFls
mkChar   = ConstTerm . CharLiteral
mkString = ConstTerm . StringLiteral

tyTerm :: Term -> Type -> Term
tyTerm = TermWithType

mkApp :: Term -> [Term] -> Term
mkApp t0 [] = t0
mkApp t0 (t:ts) = mkApp (TermApp t0 t) ts

mkPair :: Term -> Term -> Term
mkPair a b = ListTerm "(" [a, b] ")"

mkList :: [Term] -> Term
mkList xs = ListTerm "[" xs "]"

mkTuple :: [Term] -> Term
mkTuple xs = ListTerm "(" xs ")"

lamTerm :: [Ident] -> Term -> Term
lamTerm ids t = QuantifiedTerm Lambda ids t

mkLambda :: [Id] -> Term -> Term
mkLambda vs t = lamTerm (map Id vs) t

subSym :: String
subSym = "\\<^sub>"

-- ^sub's a string
subSymStr :: String -> String
subSymStr = foldl (\s v -> s ++ subSym ++ [v]) []

--
-- The associativity, precedence and symbols for Isabelle/HOL terms can be found in the Isabelle
-- source at src/HOL/HOL.thy For Isabelle/Pure terms I don't know where to look for associativity
-- and precedence. I consulted a cheat sheet I found on the Internet.
--
termBinOpRec :: TermBinOp -> BinOpRec
termBinOpRec b = case b of
  Equiv     -> BinOpRec AssocRight 2  "\\<equiv>"
  MetaImp   -> BinOpRec AssocRight 1  "\\<Longrightarrow>"
  Eq        -> BinOpRec AssocLeft  50 "="
  NotEq     -> BinOpRec AssocLeft  50 "\\<noteq>"
  Iff       -> BinOpRec AssocRight 24 "\\<Leftrightarrow>"
  Conj      -> BinOpRec AssocRight 35 "\\<and>"
  Disj      -> BinOpRec AssocRight 30 "\\<or>"
  Implies   -> BinOpRec AssocRight 25 "\\<longrightarrow>"

-- You must include all binary operators in this list. Miss one and it doesn't get parsed.
-- Order does NOT matter. They are sorted by precedence.
binOps = [Equiv, MetaImp, Eq, NotEq, Iff, Conj, Disj, Implies]

termBinOpPrec :: TermBinOp -> Precedence
termBinOpPrec b = if p >= termAppPrec
               then error (show (binOpRecSym baux) ++
                     " should not have a precedence higher than that of application (termAppPrec)")
               else p
  where
    baux = termBinOpRec b
    p = binOpRecPrec baux

termBinOpSym :: TermBinOp -> String
termBinOpSym = binOpRecSym . termBinOpRec

termBinOpAssoc :: TermBinOp -> Assoc
termBinOpAssoc = binOpRecAssoc . termBinOpRec

-- Predence for a unary operator
--
-- The precedences for Isabelle/HOL terms can be found in the Isabelle source at src/HOL/HOL.thy
-- For Isabelle/Pure terms I don't know where to look. I consulted a cheat sheet.
--
termUnOpRec :: TermUnOp -> UnOpRec
termUnOpRec u = case u of
  Not -> UnOpRec 40 "\\<not>"

termUnOpPrec = unOpRecPrec . termUnOpRec
termUnOpSym = unOpRecSym . termUnOpRec

-- You must include all unary operators in this list. Miss one and it doesn't get parsed.
-- Order does NOT matter. They are sorted by precedence.
termUnOps = [Not]


data QuantifierRec = QuantifierRec { quantifierRecPrecedence :: Precedence, quantifierRecSymbol :: String }

--
-- The precedences for Isabelle/HOL terms can be found in the Isabelle source at src/HOL/HOL.thy
-- For Isabelle/Pure terms I don't know where to look. I consulted a cheat sheet.
--
quantifierAux :: Quantifier -> QuantifierRec
quantifierAux q = case q of
  MetaBind    -> QuantifierRec 0  "\\<And>"
  Lambda      -> QuantifierRec 3  "\\<lambda>"
  Forall      -> QuantifierRec 10 "\\<forall>"
  Exists      -> QuantifierRec 10 "\\<exists>"
  ExistsBang  -> QuantifierRec 10 "\\<exists>!"

quantifierPrec = quantifierRecPrecedence . quantifierAux
quantifierSym =  quantifierRecSymbol . quantifierAux

--
-- You must include all quantifiers in this list. Miss one and it doesn't get parsed.
-- Order does NOT matter. They are sorted by precedence.
--
quantifiers = [MetaBind, Lambda, Forall, Exists, ExistsBang]

--
-- Pretty printing
--

abstractor :: String -> [Doc] -> Doc -> Doc
abstractor s docs doc = string s <> hsep docs <> char '.' <+> doc

absTerm :: String -> [Ident] -> Term -> Doc
absTerm s idents term = abstractor s (map pretty idents) (pretty term)

binOp :: String -> Doc -> Doc -> Doc
binOp s d d' = d <+> string s <+> d'

binOpTerm p s t t' = binOp s (prettyTerm p t) (prettyTerm p t')

-- precedence of application. Nothing should be higher
termAppPrec = 100

prettyTerm :: Precedence -> Term -> Doc
prettyTerm p t = case t of
  TermIdent i           -> pretty i
  -- highest precedence and left associative
  TermApp t t'          -> prettyParen (p > termAppPrec) $ prettyTerm termAppPrec t <+>
                             prettyTerm (termAppPrec+1) t'
  TermWithType t typ    -> prettyParen True $ pretty t <+> string "::" <+> pretty typ
  QuantifiedTerm q is t -> prettyQuantifier p q is t
  TermBinOp b t t'      -> (case b of
                              MetaImp -> prettyMetaImp p t t'
                              _       -> prettyBinOpTerm p b t t')
  TermUnOp u t          -> prettyUnOpTerm p u t
  ListTerm l ts r       -> pretty l <> hcat (intersperse (string ", ") (map (prettyTerm termAppPrec) ts)) <> pretty r
  ConstTerm const       -> pretty const
  AntiTerm str          -> pretty str  -- FIXME: zilinc
  CaseOf e alts         -> parens (string "case" <+> pretty e <+> string "of" <+> sep (punctuate (text "|") (map prettyAlt alts)))

prettyAlt :: (Term, Term) -> Doc
prettyAlt (p, e) = pretty p <+> pretty "\\<Rightarrow>" <+> pretty e

prettyBinOpTerm :: Precedence -> TermBinOp -> Term -> Term -> Doc
prettyBinOpTerm p b = prettyBinOp p prettyTerm (termBinOpRec b) prettyTerm

prettyUnOpTerm :: Precedence -> TermUnOp -> Term -> Doc
prettyUnOpTerm p u = prettyUnOp p (termUnOpRec u) prettyTerm

--
-- [| P_1; ...; P_n |] ==> Q is syntactic sugar for P_1 ==> ... ==> P_n ==> Q
--
-- @prettyMetaImp@ takes care of printing it that way.
prettyMetaImp :: Precedence -> Term -> Term -> Doc
prettyMetaImp p t t' = case t' of
  t'@(TermBinOp MetaImp _ _) -> go [t] t'
  _                   -> prettyBinOpTerm p MetaImp t t'
  where
    p' = termBinOpPrec MetaImp
    go ts (TermBinOp MetaImp t t') = go (t:ts) t'
    go ts t                    =
      string "\\<lbrakk>" <>
      (hsep . punctuate semi . map (prettyTerm (p'+1)) . reverse $ ts) <>
      string "\\<rbrakk>" <+> string (termBinOpSym MetaImp) <+> prettyTerm p' t

prettyQuantifier :: Precedence -> Quantifier -> [Ident] -> Term -> Doc
prettyQuantifier p q is t = prettyParen (p > quantifierPrec q) $ string (quantifierSym q) <>
                              (hsep . map pretty $ is) <> char '.' <+> pretty t

instance Pretty Ident where
  pretty ident = case ident of
    Id id            -> string id
    Wildcard         -> string "_"
    TypedIdent id ty -> pretty id <+> string "::" <+> pretty ty

instance Pretty Term where
  pretty = prettyTerm 0

instance Pretty PrimType where
  pretty ty = string $ case ty of
    IntT  -> "int"
    BoolT -> "bool"
    NatT  -> "nat"

instance Pretty Type where
  pretty = prettyType 0

tyArrowSym = "\\<Rightarrow>"
tyTupleSym = "\\<times>"

prettyTypeVars :: [Type] -> Doc
prettyTypeVars [] = empty
prettyTypeVars [ty] = prettyType 100 ty -- application has highest precedence
prettyTypeVars tys = char '(' <> (hsep . punctuate (char ',') . map (prettyType 0) $ tys) <> char ')'  -- FIXME: not very pretty / zilinc

prettyType :: Precedence -> Type -> Doc
prettyType p ty =
    case ty of
      TyVar v          -> char '\'' <> string v
      TyDatatype s tys -> prettyTypeVars tys <+> string s
      TyPrim t         -> pretty t
      -- TyArrow is right associative
      TyArrow t t'     -> prettyParen (p > pa) $ prettyType (pa+1) t <+>
                          string tyArrowSym <+> prettyType pa t'
      -- TyTuple is right associative
      TyTuple t t'     -> prettyParen (p > pt) $ prettyType (pt+1) t <+>
                          string tyTupleSym <+> prettyType pt t'
      AntiType t       -> string t  -- FIXME: zilinc
  where
     pa = 1
     pt = 2

instance Pretty Const where
  pretty c = case c of
    TrueC  -> string "True"
    FalseC -> string "False"
    IntLiteral    i -> integer i
    CharLiteral   c -> string $ printf "CHR %#02x" $ ord c
    StringLiteral s | '\'' `elem` s -> string $ "[" ++ intercalate "," (map repr s) ++ "]"
                    | otherwise     -> string $ "''" ++ s ++ "''"
                        where repr = printf "CHR %#02x" . ord
    Top    -> string "\\<top>"
    Bottom -> string "\\<bottom>"

instance Pretty Arity where
  pretty (Arity Nothing n) = string n
  pretty (Arity (Just ns) n) = parens (sep $ punctuate comma $ map string ns) <+> string n

--------

idn = mkId

infixr 5 `imp`
imp = TermBinOp MetaImp

newtype Lines a = Lines [a]

instance Show a => Show (Lines a) where
  show (Lines xs) = concat . intersperse "\n" . map show  $ xs

test = pretty t0 <+> string "|" <+> pretty t1 <+> string "|" <+> pretty t2
  where conj = TermBinOp Conj
        disj = TermBinOp Disj
        t0 = (idn "A") `conj` (idn "B")
        t1 = ((idn "A") `conj` (idn "B")) `disj` (idn "C")  -- A \<and> B \<or> C
        t2 = (idn "A") `conj` ((idn "B") `disj` (idn "C"))  -- A \<and> (B \<or> C)

test2 = Lines [ pretty (idn "A" `imp` idn "B" `imp` idn "C" `imp` idn "D")
              , pretty ((idn "A" `imp` idn "B") `imp` idn "C")
              , pretty (TermBinOp Equiv (TermApp (idn "A") (idn "x")) (TermApp (idn "B") (idn "x"))) ]

testt = Lines [ pretty (v "x" ==> v "y" ==> v "z")
              , pretty ((v "x" ==> v "y") ==> v "z")
              , pretty (TyDatatype "option" [TyVar "a"])
              , pretty (TyDatatype "list" [TyVar "a"])
              , pretty (TyDatatype "option" [TyTuple (v "a") (TyTuple (v "b") (v "c"))])
              , pretty (TyDatatype "option" [v "a" ==> v "b"])
              , pretty (TyDatatype "twoparam" [TyTuple (v "a") (v "b"), (v "c")]) ]

  where
    v x = TyVar x
    infixr 5 ==>
    a ==> b = TyArrow a b
