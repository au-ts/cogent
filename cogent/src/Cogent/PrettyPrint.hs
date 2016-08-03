{-# LANGUAGE NamedFieldPuns #-}
--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE FlexibleInstances, FlexibleContexts, MultiWayIf, ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -fno-warn-missing-signatures #-}

module Cogent.PrettyPrint where

import qualified Cogent.Common.Syntax as S (associativity)
import Cogent.Common.Syntax hiding (associativity)
import Cogent.Common.Types
import Cogent.Compiler (__impossible)
import Cogent.Desugar (desugarOp)
import Cogent.Reorganizer (ReorganizeError(..), SourceObject(..))
import Cogent.Surface
import Cogent.TypeCheck.Base

import Control.Arrow (second)
import qualified Data.Map as M hiding (foldr)
#if __GLASGOW_HASKELL__ < 709
import Data.Monoid (mconcat)
import Prelude hiding (foldr)
#else
import Prelude hiding ((<$>), foldr)
#endif
import Text.Parsec.Pos
import Text.PrettyPrint.ANSI.Leijen hiding (tupled,indent)

indentation, ifIndentation :: Int
indentation = 3
ifIndentation = 3
position = string
varname = string
primop = blue . string
keyword = bold . string
typevar = blue . string
typename = blue . bold . string
literal = dullcyan
typesymbol = cyan . string
funname = dullyellow . string
fieldname = magenta . string
tagname = dullmagenta . string
symbol = string
kindsig = red . string
spaceList = encloseSep empty empty space
commaList = encloseSep empty empty (comma <> space)
dotList = encloseSep empty empty (symbol ".")
tupled = encloseSep lparen rparen (comma <> space)
tupled1 [x] = x
tupled1 x = encloseSep lparen rparen (comma <> space) x
typeargs x = encloseSep lbracket rbracket (comma <> space) x
err = red . string
warn = yellow . string
comment = black . string
context = black . string
letbangvar = dullgreen . string
record = encloseSep (lbrace <> space) (space <> rbrace) (comma <> space)
variant = encloseSep (langle <> space) rangle (symbol "|" <> space) . map (<> space)
indent = nest indentation
indent' = (string (replicate indentation ' ') <>) . nest indentation

level :: Associativity -> Int
level (LeftAssoc i) = i
level (RightAssoc i) = i
level (NoAssoc i) = i
level (Prefix) = 0

associativity :: String -> Associativity
associativity = S.associativity . desugarOp

class ExprType a where
  levelExpr :: a -> Int
  isVar :: a -> String -> Bool



instance ExprType (Expr a b c) where
  levelExpr (App {}) = 1
  levelExpr (PrimOp n [_,_]) = level (associativity n)
  levelExpr (Member {}) = 0
  levelExpr (Var {}) = 0
  levelExpr (IntLit {}) = 0
  levelExpr (BoolLit {}) = 0
  levelExpr (CharLit {}) = 0
  levelExpr (StringLit {}) = 0
  levelExpr (Tuple {}) = 0
  levelExpr (Unitel) = 0
  levelExpr _ = 100
  isVar (Var n) s = (n == s)
  isVar _ _ = False

pretty'IP e@(PTake {}) = parens (pretty e)
pretty'IP e = pretty e

pretty' :: (Pretty a, ExprType a) => Int -> a -> Doc
pretty' l x | levelExpr x < l = pretty x
            | otherwise       = parens (indent (pretty x))

handleTakeAssign :: (PrettyName b) => Maybe (FieldName, IrrefutablePattern b) -> Doc
handleTakeAssign Nothing = fieldname ".."
handleTakeAssign (Just (s, PVar x)) | isName x s = fieldname s
handleTakeAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> pretty e

handlePutAssign :: (ExprType e, Pretty e) => Maybe (FieldName, e) -> Doc
handlePutAssign Nothing = fieldname ".."
handlePutAssign (Just (s, e)) | isVar e s = fieldname s
handlePutAssign (Just (s, e)) = fieldname s <+> symbol "=" <+> pretty e


class PrettyName a where
  prettyName :: a -> Doc
  isName :: a -> String -> Bool

instance PrettyName VarName where
  prettyName = varname
  isName s = (==s)
instance Pretty Likelihood where
  pretty Likely   = symbol "=>"
  pretty Unlikely = symbol "~>"
  pretty Regular  = symbol "->"


instance PrettyName b => Pretty (IrrefutablePattern b) where
  pretty (PVar v) = prettyName v
  pretty (PTuple ps) = tupled (map pretty ps)
  pretty (PUnboxedRecord fs) = string "#" <> record (map handleTakeAssign fs)
  pretty (PUnderscore) = symbol "_"
  pretty (PUnitel) = string "()"
  pretty (PTake v fs) = prettyName v <+> record (map handleTakeAssign fs)

instance PrettyName b => Pretty (Pattern b) where
  pretty (PCon c [] )     = tagname c
  pretty (PCon c [p])     = tagname c <+> pretty'IP p
  pretty (PCon c ps )     = tagname c <+> spaceList (map pretty'IP ps)
  pretty (PIntLit i)      = literal (string $ show i)
  pretty (PBoolLit b)     = literal (string $ show b)
  pretty (PCharLit c)     = literal (string $ show c)
  pretty (PIrrefutable p) = pretty p

pretty'B (p, Just t, e) i
     = group (pretty p <+> symbol ":" <+> pretty t <+> symbol "=" <+> (if i then (pretty' 100) else pretty) e)
pretty'B (p, Nothing, e) i
     = group (pretty p <+> symbol "=" <+> (if i then (pretty' 100) else pretty) e)

instance (Pretty t, PrettyName b, Pretty e, ExprType e) => Pretty (Binding t b e) where
  pretty (Binding p t e []) = pretty'B (p,t,e) False
  pretty (Binding p t e bs)
     = pretty'B (p,t,e) True <+> hsep (map (letbangvar . ('!':)) bs)

instance (PrettyName b, Pretty e) => Pretty (Alt b e) where
  pretty (Alt p arrow e) = symbol "|" <+> pretty p <+> group (pretty arrow <+> pretty e)

instance Pretty Inline where
  pretty Inline = keyword "inline" <+> empty
  pretty NoInline = empty

instance (ExprType e, Pretty t, PrettyName b, Pretty e) => Pretty (Expr t b e) where
  pretty (Var x)             = varname x
  pretty (TypeApp x ts note) = pretty note <> varname x <> typeargs (map pretty ts)
  pretty (Member x f)        = pretty' 1 x <> symbol "." <> fieldname f
  pretty (IntLit i)          = literal (string $ show i)
  pretty (BoolLit b)         = literal (string $ show b)
  pretty (CharLit c)         = literal (string $ show c)
  pretty (StringLit s)       = literal (string $ show s)
  pretty (Unitel)            = string "()"
  pretty (PrimOp n [a,b])
     | LeftAssoc l  <- associativity n = pretty' (l+1) a <+> primop n <+> pretty' l b
     | RightAssoc l <- associativity n = pretty' l a <+> primop n <+> pretty' (l+1)  b
     | NoAssoc   l  <- associativity n = pretty' l a <+> primop n <+> pretty' l  b
  pretty (PrimOp n [e])      = primop n <+> pretty' 1 e
  pretty (PrimOp n es)       = primop n <+> tupled (map pretty es)
  pretty (App a b)           = pretty' 2 a <+> pretty' 1 b
  pretty (Con n [] )         = tagname n
  pretty (Con n [e])         = tagname n <+> pretty' 1 e
  pretty (Con n es )         = tagname n <+> spaceList (map (pretty' 1) es)
  pretty (Tuple es)          = tupled (map pretty es)
  pretty (UnboxedRecord fs)  = string "#" <> record (map (handlePutAssign . Just) fs)
  pretty (If c vs t e)       = group (keyword "if" <+> handleBangedIf vs (pretty' 100 c)
                                                   <$> indent (keyword "then" </> pretty t)
                                                   <$> indent (keyword "else" </> pretty e))
    where handleBangedIf []  = id
          handleBangedIf vs  = (<+> hsep (map (letbangvar . ('!':)) vs))
  pretty (Match e bs alts)   = handleLetBangs bs (pretty' 100 e)
                               <> mconcat (map ((hardline <>) . indent . pretty) alts)
    where handleLetBangs []  = id
          handleLetBangs bs  = (<+> hsep (map (letbangvar . ('!':)) bs))
  pretty (Seq a b)           = pretty' 100 a <> symbol ";" <$> pretty b
  pretty (Let []     e)      = __impossible "pretty (in RawExpr)"
  pretty (Let (b:[]) e)      = keyword "let" <+> indent (pretty b)
                                             <$> keyword "in" <+> nest (ifIndentation) (pretty e)
  pretty (Let (b:bs) e)      = keyword "let" <+> indent (pretty b)
                                             <$> vsep (map ((keyword "and" <+>) . indent . pretty) bs)
                                             <$> keyword "in" <+> nest 3 (pretty e)
  pretty (Put e fs)          = pretty' 1 e <+> record (map handlePutAssign fs)

instance ExprType RawExpr where
  levelExpr (RE e) = levelExpr e
  isVar (RE e) = isVar e
instance Pretty RawExpr where
  pretty (RE e) = pretty e

instance ExprType (TExpr t) where
  levelExpr (TE _ e) = levelExpr e
  isVar (TE _ e)     = isVar e
instance Pretty t => PrettyName (VarName, t) where
  prettyName (a, b) = prettyName a <+> comment "::" <+> pretty b
  isName (a, b) x = a == x

instance Pretty t => Pretty (TExpr t) where
  pretty (TE t e) = pretty e

class TypeType t where
  isCon :: t -> Bool
  isTakePut :: t -> Bool
  isFun :: t -> Bool

instance (Pretty t, TypeType t) => Pretty (Type t) where
  pretty (TCon n [] s) = ($ typename n) (if | s == ReadOnly -> (<> typesymbol "!")
                                            | s == Unboxed && (n `notElem` primTypeCons) -> (typesymbol "#" <>)
                                            | otherwise     -> id)
  pretty (TCon n as s) = (if | s == ReadOnly -> (<> typesymbol "!") . parens
                             | s == Unboxed  -> (typesymbol "#" <>)
                             | otherwise     -> id) $
                         typename n <+> hsep (map prettyT' as)
    where prettyT' e | isCon e || isTakePut e || isFun e = parens (pretty e)
                     | otherwise                         = pretty e
  pretty (TVar n b)  = typevar n
  pretty (TTuple ts) = tupled (map pretty ts)
  pretty (TUnit)     = typesymbol "()"
  pretty (TRecord ts s)
    | not . or $ map (snd . snd) ts = (if | s == Unboxed -> (typesymbol "#" <>)
                                          | s == ReadOnly -> (\x -> parens x <> typesymbol "!")
                                          | otherwise -> id) $
        record (map (\(a,(b,c)) -> fieldname a <+> symbol ":" <+> pretty b) ts)  -- all untaken
    | otherwise = pretty (TRecord (map (second . second $ const False) ts) s)
               <+> typesymbol "take" <+> tupled1 (map fieldname tk)
        where tk = map fst $ filter (snd .snd) ts
  pretty (TVariant ts) = variant (map (\(a,bs)-> case bs of
                                          [] -> tagname a
                                          _  -> tagname a <+> spaceList (map prettyT' bs)) $ M.toList ts)
    where prettyT' e | isCon e || isTakePut e || isFun e = parens (pretty e)
                     | otherwise                         = pretty e
  pretty (TFun t t') = prettyT' t <+> typesymbol "->" <+> pretty t'
    where prettyT' e | isFun e   = parens (pretty e)
                     | otherwise = pretty e
  pretty (TUnbox t) = typesymbol "#" <> prettyT' t
    where prettyT' e | isTakePut e || isFun e = parens (pretty e)
                     | otherwise              = pretty e
  pretty (TBang t) = prettyT' t <> typesymbol "!"
    where prettyT' e | isCon e || isTakePut e || isFun e = parens (pretty e)
                     | otherwise                         = pretty e
  pretty (TTake fs x) = prettyT' x <+> typesymbol "take"
                                   <+> case fs of Nothing  -> tupled (fieldname ".." : [])
                                                  Just fs' -> tupled1 (map fieldname fs')
    where prettyT' e | isTakePut e || isFun e = parens (pretty e)
                     | otherwise              = pretty e
  pretty (TPut fs x) = prettyT' x <+> typesymbol "put"
                                  <+> case fs of Nothing -> tupled (fieldname ".." : [])
                                                 Just fs' -> tupled1 (map fieldname fs')
    where prettyT' e | isTakePut e || isFun e = parens (pretty e)
                     | otherwise              = pretty e

instance TypeType (Type t) where
  isCon     (TCon {})  = True
  isCon     _          = False
  isFun     (TFun {})  = True
  isFun     _          = False
  isTakePut (TTake {}) = True
  isTakePut (TPut  {}) = True
  isTakePut _          = False

instance TypeType RawType where
  isCon (RT t)     = isCon t
  isTakePut (RT t) = isTakePut t
  isFun (RT t)     = isFun t
instance Pretty RawType where
  pretty (RT t) = pretty t

instance TypeType (TCType) where
  isCon     (T t) = isCon t
  isCon     _     = False
  isFun     (T t) = isFun t
  isFun     _     = False
  isTakePut (T t) = isTakePut t
  isTakePut _     = False

instance Pretty TCType where
  pretty (T t) = pretty t
  pretty (U v) = warn ("?" ++ show v)
  pretty (RemoveCase a b) = pretty a <+> string "(without pattern" <+> pretty b <+> string ")"

instance Pretty Kind where
  pretty k = kindsig (stringFor k)
    where stringFor k = (if canDiscard k then "D" else "")
                     ++ (if canShare   k then "S" else "")
                     ++ (if canEscape  k then "E" else "")

numOfArgs (PT x _) = length x

instance Pretty LocType where
  pretty t = pretty (stripLocT t)

instance Pretty t => Pretty (Polytype t) where
  pretty (PT [] t) = pretty t
  pretty (PT vs t) = keyword "all" <> tupled (map prettyKS vs) <> symbol "." <+> pretty t
    where prettyKS (v,K False False False) = typevar v
          prettyKS (v,k) = typevar v <+> symbol ":<" <+> pretty k

instance Pretty (TopLevel RawType VarName RawExpr) where
  pretty (TypeDec n vs t) = keyword "type" <+> typename n <> hcat (map ((space <>) . typevar) vs)
                                           <+> indent (symbol "=" </> pretty t)
  pretty (FunDef v pt [Alt (PIrrefutable p) Regular e]) = vcat [ funname v <+> symbol ":" <+> pretty pt
                                                               , funname v <+> pretty'IP p <+> group (indent (symbol "=" <$> pretty e))]
  pretty (AbsDec v pt) = funname v <+> symbol ":" <+> pretty pt
  pretty (FunDef v pt alts) = vcat [ funname v <+> symbol ":" <+> pretty pt
                                   , indent (funname v <> mconcat (map ((hardline <>) . indent . pretty) alts))]
  pretty (Include s) = keyword "include" <+> literal (string $ show s)
  pretty (IncludeStd s) = keyword "include <" <+> literal (string $ show s)
  pretty (AbsTypeDec n vs) = keyword "type" <+> typename n  <> hcat (map ((space <>) . typevar) vs)
  pretty (ConstDef v t e) = vcat [ funname v <+> symbol ":" <+> pretty t
                                 , funname v <+> group (indent (symbol "=" <+> pretty e))]


instance Pretty SourcePos where
  pretty p = position (show p)

instance Pretty Metadata where
  pretty (Reused {varName, boundAt, usedAt}) = err "the variable" <+> varname varName
                                               <+> err "(bound at" <+> pretty boundAt <> err ")"
                                               <+> err "was already used at" <+> pretty usedAt
  pretty (Unused {varName, boundAt}) = err "the variable" <+> varname varName
                                       <+> err "(bound at" <+> pretty boundAt <> err ")"
                                       <+> err "was never used."
  pretty (UnusedInOtherBranch { varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "(bound at" <+> pretty boundAt <> err ")"
    <+> err "was used in another branch of control at" <+> pretty usedAt
    <+> err "but not this one."
  pretty (UnusedInThisBranch { varName, boundAt, usedAt}) =
    err "the variable" <+> varname varName
    <+> err "(bound at" <+> pretty boundAt <> err ")"
    <+> err "was used in this branch of control at" <+> pretty usedAt
    <+> err "but not in all other branches."
  pretty Suppressed = err "a binder for a value of this type is being suppressed."
  pretty (UsedInMember { fieldName}) = err "the field" <+> fieldname fieldName
                                       <+> err "is being extracted without taking the field in a pattern."
  pretty UsedInLetBang = err "it is being returned from such a context."
  pretty (TypeParam { functionName , typeVarName }) = err "it is required by the type of" <+> funname functionName
                                                      <+> err "(type variable" <+> typevar typeVarName <+> err ")"
  pretty ImplicitlyTaken = err "it is implicitly taken via subtyping."

instance Pretty TypeError where
  pretty (FunctionNotFound fn)           = err "Function" <+> funname fn <+> err "not found"
  pretty (TooManyTypeArguments fn pt)    = err "Too many type arguments to function"
                                           <+> funname fn  <+> err "of type" <+> pretty pt
  pretty (NotInScope vn)                 = varname vn <+> err "not in scope"
  pretty (UnknownTypeVariable vn)        = err "Unknown type variable" <+> varname vn
  pretty (UnknownTypeConstructor tn)     = err "Unknown type constructor" <+> typename tn
  pretty (TypeArgumentMismatch tn i1 i2) = typename tn <+> err "expects"
                                           <+> int i1 <+> err "arguments, but has been given" <+> int i2
  pretty (TypeMismatch t1 t2)            = err "Mismatch between " <+> pretty t1 <+> err "and" <+> pretty t2
  pretty (RequiredTakenField f t)        = err "Required field" <+> fieldname f
                                           <+> err "of type" <+> pretty t <+> err "to be untaken"
  pretty (TypeNotShareable t m)          = err "Cannot share type" <+> pretty t
                                           <+> err "but this is needed as" <+> pretty m
  pretty (TypeNotEscapable t m)          = err "Cannot let type" <+> pretty t <+> err "escape from a !-ed context,"
  pretty (TypeNotDiscardable t m)        = err "Cannot discard type" <+> pretty t
                                           <+> err "but this is needed as" <+> pretty m
  pretty (PatternsNotExhaustive t tags)  = err "Patterns not exhaustive for type" <+> pretty t
                                           <$> err "cases not matched" <+> tupled1 (map tagname tags)
  pretty (UnsolvedConstraint c)          = err "Leftover constraint!" <$> pretty c
  pretty (RecordWildcardsNotSupported)   = err "Record wildcards are not supported"
  pretty (NotAFunctionType t)            = pretty t <+> err "is not a function type"
  pretty (DuplicateVariableInPattern vn pat)       = err "Duplicate variable " <+> varname vn <+> err "in pattern:"
                                                     <$> pretty pat
  pretty (DuplicateVariableInIrrefPattern vn ipat) = err "Duplicate variable " <+> varname vn <+> err "in pattern:"
                                                     <$> pretty ipat
instance Pretty ErrorContext where
  pretty _ = error "use `prettyCtx' instead!"
prettyCtx (SolvingConstraint c) i = context "from constraint " <+> pretty c
prettyCtx (ThenBranch) i = context "in the" <+> keyword "then" <+> context "branch"
prettyCtx (ElseBranch) i = context "in the" <+> keyword "else" <+> context "branch"
prettyCtx (InExpression e t) True = context "when checking that the expression at ("
                                                  <> pretty (posOfE e) <> context ")"
                                       <$> (indent' (pretty (stripLocE e)))
                                       <$> context "has type" <$> (indent' (pretty t))
prettyCtx (InExpression e t) False = context "when checking the expression at ("
                                                  <> pretty (posOfE e) <> context ")"
prettyCtx (InExpressionOfType e t) True = context "when checking that the expression at ("
                                                  <> pretty (posOfE e) <> context ")"
                                       <$> (indent' (pretty (stripLocE e)))
                                       <$> context "has type" <$> (indent' (pretty t))
prettyCtx (InExpressionOfType e t) False = context "when checking the expression at ("
                                                  <> pretty (posOfE e) <> context ")"
                                       -- <+> context "has type" <$> (indent' (pretty t))
prettyCtx (NthAlternative n p) _ = context "in the" <+> nth n <+> context "alternative (" <> pretty p <> context ")"
  where  nth 1 = context "1st"
         nth 2 = context "2nd"
         nth 3 = context "3rd"
         nth n = context (show n ++ "th")
prettyCtx (InDefinition p tl) _ = context "in the definition at (" <> pretty p <> context ")"
                               <$> context "for the" <+> helper tl
  where helper (TypeDec n _ _) = context "type synonym" <+> typename n
        helper (AbsTypeDec n _) = context "abstract type" <+> typename n
        helper (AbsDec n _) = context "abstract function" <+> varname n
        helper (ConstDef v _ _) = context "constant" <+> varname v
        helper (FunDef v _ _) = context "function" <+> varname v
        helper _  = __impossible "helper"
prettyCtx (AntiquotedType t) i = (if i then (<$> indent' (pretty (stripLocT t))) else id)
                               (context "in the antiquoted type at (" <> pretty (posOfT t) <> context ")" )
prettyCtx (AntiquotedExpr e) i = (if i then (<$> indent' (pretty (stripLocE e))) else id)
                               (context "in the antiquoted expression at (" <> pretty (posOfE e) <> context ")" )
{- 
prettyTWE :: Int -> (Either TypeError Warning, [ErrorContext]) -> Doc
prettyTWE th (Left  e, ctx) = prettyTWE' th (e, ctx)
prettyTWE th (Right w, ctx) = prettyTWE' th (w, ctx)
-} 
prettyTWE' :: Pretty we => Int -> ([ErrorContext], we) -> Doc
prettyTWE' threshold (ectx, we) = pretty we <$> indent' (vcat (map (flip prettyCtx True ) (take threshold ectx)
                                                            ++ map (flip prettyCtx False) (drop threshold ectx)))

instance Pretty SourceObject where
  pretty (TypeName n) = typename n
  pretty (ValName  n) = varname n

instance Pretty ReorganizeError where
  pretty CyclicDependency = err "cyclic dependency"
  pretty DuplicateTypeDefinition = err "duplicate type definition"
  pretty DuplicateValueDefinition = err "duplicate value definition"

prettyRE :: (ReorganizeError, [(SourceObject, SourcePos)]) -> Doc
prettyRE (msg,ps) = pretty msg <$>
                    indent' (vcat (map (\(so,p) -> context "-" <+> pretty so
                                               <+> context "(" <> pretty p <> context ")") ps))

prettyPrint :: Pretty a => (Doc -> Doc) -> [a] -> SimpleDoc
prettyPrint f = renderSmart 1.0 80 . f . vcat . map pretty



instance Pretty Constraint where
  pretty (a :<  b)        = pretty a <+> warn ":<"  <+> pretty b
  pretty (a :<~ b)        = pretty a <+> warn ":<~" <+> pretty b
  pretty (a :& b)         = pretty a <+> warn ":&" <+> pretty b
  pretty (Share  t m)     = warn "Share" <+> pretty t
  pretty (Drop   t m)     = warn "Drop" <+> pretty t
  pretty (Escape t m)     = warn "Escape" <+> pretty t
  pretty (Unsat e)        = warn "Unsat"
  pretty (Sat)            = warn "Sat"
  pretty (Exhaustive _ _) = warn "Exhaustive ..."
  pretty (x :@ _)         = pretty x
