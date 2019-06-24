-- |
-- Module      : Minigent.Syntax.PrettyPrint
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- This module is a fairly straightforward pretty-printing module.
-- Each function corresponds to a syntactic class from the parser.
--
-- It uses the @prettyprinter@ library and produces ANSI-coloured
-- output.
--
-- It expects to be imported unqualified.
{-# LANGUAGE OverloadedStrings #-}
module Minigent.Syntax.PrettyPrint where

import qualified Minigent.Syntax.PrettyPrint.Styles as S
import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Row as Row
import Minigent.Environment

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import qualified Data.Text as T
import qualified Data.Map as M

prettyPrimType t = annotate S.primType (viaShow (t :: PrimType))

prettyREntry (Entry v x tk) 
   =  annotate S.field (pretty v) 
  <+> annotate S.sym ":" 
  <+> prettyType x
  <>  if tk then space <> annotate S.keyword "take"
            else mempty

prettyVEntry (Entry v x tk) 
   =  annotate S.con (pretty v) 
  <+> prettyType x
  <>  if tk then space <> annotate S.keyword "take"
            else mempty

prettySigil ReadOnly = annotate S.sigil "!"
prettySigil Unboxed  = annotate S.sigil "#"
prettySigil (UnknownSigil s)  = annotate S.sigil (pretty s)
prettySigil _ = mempty


prettyVRow r@(Row _ Nothing)  = encloseSep langle rangle pipe (map prettyVEntry (Row.entries r))
prettyVRow r@(Row _ (Just v)) = encloseSep langle rangle pipe (map prettyVEntry (Row.entries r)
                                                            ++ [annotate S.var (pretty (v ++ "..."))])

prettyRRow r@(Row _ Nothing)  = encloseSep lbrace rbrace comma (map prettyREntry (Row.entries r))
prettyRRow r@(Row _ (Just v)) = encloseSep lbrace rbrace comma (map prettyREntry (Row.entries r)
                                                            ++ [annotate S.var (pretty (v ++ "...")) ])

prettyType ty = case ty of 
    Function t1 t2 -> align (sep [pretty' t1, annotate S.sym "->" <+> prettyType t2])
    Bang t         -> annotate S.typeOp "bang" <+> prettyA t
    _              -> pretty' ty
  where
    prettyA (TypeVar n) = annotate S.typeVar (pretty n)
    prettyA (UnifVar n) = annotate S.unifVar (pretty n)
    prettyA (TypeVarBang n) = annotate S.typeVar (pretty n) <> annotate S.sigil "!"
    prettyA (PrimType t) = prettyPrimType t
    prettyA (Record r s) = align (prettyRRow r)  <> prettySigil s
    prettyA (Variant r)  = align (prettyVRow r)
    prettyA (AbsType n s []) = annotate S.absType (pretty n) <> prettySigil s
    prettyA ty = parens (prettyType ty)

    pretty' ty = case ty of
      AbsType n s ts | not (null ts) -> annotate S.absType (pretty n) <> prettySigil s
                                    <+> align (sep (map prettyA ts))
      _ -> prettyA ty

prettyOp o | Just v <- lookup o (map (\(a,b) -> (b,a)) operators)
           = annotate S.op (pretty v)


prettyExp (Sig e t) = prettyExp e <+> annotate S.sym ":" <+> prettyType t
prettyExp e = prettyBool e

prettyBool (PrimOp o [e1,e2]) 
  | o `elem` boolOps = prettyBool e1 <+> prettyOp o <+> prettyComp e2
prettyBool e = prettyComp e

prettyComp (PrimOp o [e1,e2]) 
  | o `elem` compOps = prettySum e1 <+> prettyOp o <+> prettySum e2
prettyComp e = prettySum e

prettySum (PrimOp o [e1,e2]) 
  | o `elem` sumOps = prettySum e1 <+> prettyOp o <+> prettyProd e2
prettySum e = prettyProd e

prettyProd (PrimOp o [e1,e2]) 
  | o `elem` prodOps = prettyProd e1 <+> prettyOp o <+> prettyApp e2
prettyProd e = prettyApp e

prettyApp (Apply e1 e2) = prettyApp e1 <+> prettyAtom e2
prettyApp (Con c e) = annotate S.con (pretty c) <+> prettyAtom e
prettyApp (PrimOp Not [e]) = annotate S.op "~" <+> prettyAtom e
prettyApp e = prettyAtom e

prettyAtom (Literal l) = prettyLiteral l
prettyAtom (Var v) = annotate S.var (pretty v)
prettyAtom (TypeApp f ts) = annotate S.func (pretty f) <> align (list (map prettyType ts))
prettyAtom (If e1 e2 e3)
   = align (sep [ annotate S.keyword "if" <+> prettyExp e1
                , annotate S.keyword "then" <+> prettyExp e2
                , annotate S.keyword "else" <+> prettyExp e3
                , annotate S.keyword "end" ])
prettyAtom (Let v e1 e2) 
  = align (sep [ annotate S.keyword "let" <+> annotate S.var (pretty v)
                                          <+> annotate S.sym "="   
                                          <+> prettyExp e1
               , annotate S.keyword "in" <+> prettyExp e2
               , annotate S.keyword "end" ])  
prettyAtom (LetBang vs v e1 e2) 
  = align (sep [ annotate S.keyword "let" <> annotate S.sigil "!"
                                          <+> align (tupled (map (annotate S.var . pretty) vs))
                                          <+> annotate S.var (pretty v)
                                          <+> annotate S.sym "="   
                                          <+> prettyExp e1
               , annotate S.keyword "in" <+> prettyExp e2
               , annotate S.keyword "end" ])  
prettyAtom (Struct fs) = align . encloseSep lbrace rbrace comma
                           $ map (\(f, e) -> annotate S.field (pretty f)
                                         <+> annotate S.sym "="
                                         <+> prettyExp e) fs
prettyAtom (Case e c v1 e1 v2 e2) 
  = align (sep [ annotate S.keyword "case" <+> prettyExp e <+> annotate S.keyword "of",
                 indent 2 (annotate S.con (pretty c) <+> annotate S.var (pretty v1) 
                                                     <+> annotate S.sym "->" 
                                                     <+> prettyExp e1)
               , annotate S.sym "|" <+> hang 2 (annotate S.var (pretty v2 )
                                            <+> annotate S.sym "->" 
                                            <+> prettyExp e2)
               , annotate S.keyword "end"
               ])
prettyAtom (Esac e c v1 e1) 
  = align (sep [ annotate S.keyword "case" <+> prettyExp e <+> annotate S.keyword "of",
                 indent 2 (annotate S.con (pretty c) <+> annotate S.var (pretty v1) 
                                                     <+> annotate S.sym "->" 
                                                     <+> prettyExp e1)
               , annotate S.keyword "end"
               ])
prettyAtom (Take r f v e1 e2) 
  = align (sep [ annotate S.keyword "take" <+> annotate S.var (pretty r)
                                           <+> lbrace
                                           <+> annotate S.field (pretty f)
                                           <+> annotate S.sym "="   
                                           <+> annotate S.var (pretty v)
                                           <+> rbrace 
                                           <+> annotate S.sym "=" 
                                           <+> prettyExp e1
               , annotate S.keyword "in" <+> prettyExp e2
               , annotate S.keyword "end" ])  
prettyAtom (Put e1 f e2 ) 
  = align (sep [ annotate S.keyword "put" <+> prettyExp e1
                                          <>  annotate S.sym "."
                                          <>  annotate S.field (pretty f)
                                          <+> annotate S.sym ":=" 
                                          <+> prettyExp e2
               , annotate S.keyword "end" ])  
prettyAtom (Member e f) = prettyAtom e <> annotate S.sym "." <> annotate S.field (pretty f)
prettyAtom e = parens (prettyExp e)

prettyLiteral (BoolV b) = annotate S.literal (viaShow b)
prettyLiteral (IntV i) = annotate S.literal (viaShow i)
prettyLiteral (UnitV) = annotate S.literal "Unit"

prettyToplevel (TypeSig f t) =  annotate S.func (pretty f) 
                            <+> annotate S.sym ":" 
                            <+> prettyPolyType t
                            <>  annotate S.sym ";"
prettyToplevel (Equation f x t) =  annotate S.func (pretty f) 
                               <+> annotate S.var (pretty x)
                               <+> annotate S.sym "="
                               <+> prettyExp t
                               <>  annotate S.sym ";"

prettyGlobalEnvs (GlobalEnvs defns types) 
  = align . vsep . map prettyToplevel
  . flip concatMap (M.toList types) $
    \(f,t) -> TypeSig f t : case M.lookup f defns of
                              Just (x,e) -> [Equation f x e]
                              Nothing    -> []

prettySimpleConstraint c = case c of
  (Share     p) -> annotate S.constraintKeyword "Share"     <+> prettyType p
  (Drop      p) -> annotate S.constraintKeyword "Drop"      <+> prettyType p
  (Escape    p) -> annotate S.constraintKeyword "Escape"    <+> prettyType p
  (Exhausted p) -> annotate S.constraintKeyword "Exhausted" <+> prettyType p
  (t1 :<    t2) -> prettyType t1 <+> annotate S.constraintKeyword ":<" <+> prettyType t2
  (i :<=:   t)  -> annotate S.literal (viaShow i) 
                     <+> annotate S.constraintKeyword ":<=:" 
                     <+> prettyType t
  (t1 :=:   t2)  -> prettyType t1 <+> annotate S.constraintKeyword ":=:" <+> prettyType t2
  (Sat)         -> annotate S.constraintKeyword "Sat"
  (Unsat)       -> annotate S.constraintKeyword "Unsat"
  _             -> error "prettySimpleConstraint called on non-simple constraint"

prettyConstraint cs  = vsep (punctuate (space <> annotate S.constraintKeyword ":&:")
                         (map prettySimpleConstraint (flattenConstraint cs)))


prettyPolyType (Forall [] [] t) = prettyType t 
prettyPolyType (Forall ts c t) = align (sep [ list (map (prettyType . TypeVar) ts) 
                                            , sep (punctuate comma (map prettyConstraint c))
                                              <> annotate S.sym "."
                                            , prettyType t ] ) 



debugPrettyConstraints
   = T.unpack . renderStrict
   . layoutPretty defaultLayoutOptions
   . vcat .  map prettyConstraint

testPrettyToplevel
   = T.unpack . renderStrict . unAnnotateS
   . layoutPretty defaultLayoutOptions
   . prettyToplevel
