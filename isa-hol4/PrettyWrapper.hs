
{-# LANGUAGE FlexibleContexts #-}

module PrettyWrapper
where 

-- system imports 
import Text.Parsec.Expr (Assoc(..))
import Text.PrettyPrint.ANSI.Leijen 
import Prelude hiding ((<$>))
import Text.Printf (printf)
import Data.Char (ord, toUpper)
import Data.Data
import Data.List
import Data.Maybe (fromJust)
import Data.Typeable
import System.FilePath.Posix

-- Isabelle imports
import Isabelle.InnerAST
import Isabelle.OuterAST
import Isabelle.PrettyHelper

------------------------------------------------------------------------

---------------         Inner                ---------------------------

------------------------------------------------------------------------

newtype HOLIdent = HOLIdent Ident 
newtype HOLTerm  = HOLTerm Term 
newtype HOLPrimType = HOLPrimType PrimType
newtype HOLType  = HOLType Type 
newtype HOLConst = HOLConst Const 
newtype HOLArity = HOLArity Arity 

quantifierAuxHOL :: Quantifier -> QuantifierRec
quantifierAuxHOL q = case q of
  MetaBind    -> QuantifierRec 0  "/\\"
  Lambda      -> QuantifierRec 3  "\\"
  Forall      -> QuantifierRec 10 "!"
  Exists      -> QuantifierRec 10 "?"
  ExistsBang  -> QuantifierRec 10 "?!"

quantifierPrecHOL = quantifierRecPrecedence . quantifierAuxHOL
quantifierSymHOL =  quantifierRecSymbol . quantifierAuxHOL

instance Pretty HOLIdent where 
    pretty (HOLIdent ident) = case ident of 
        Id id            -> string $ unSymbolIdentHOL id
        Wildcard         -> string "_"
        TypedIdent id ty -> pretty (HOLIdent id) <+> string "::" <+> pretty (HOLType ty)

unSymbolIdentHOL :: String -> String 
unSymbolIdentHOL [] = []
unSymbolIdentHOL (x : xs) = if x == '\\'
                            then let (txt, rest) =
                                        span (/= '>') $ fromJust $ stripPrefix "<" xs
                                  in  (unSymbolMapping txt) ++ unSymbolIdentHOL (drop 1 rest)
                            else x : unSymbolIdentHOL xs
  where
    unSymbolMapping       p = map toUpper p --FIXME: zoeyc

instance Pretty HOLConst where 
    pretty (HOLConst c) = case c of 
        TrueC  -> string "T"
        FalseC -> string "F"
        IntLiteral    i -> pretty i
        CharLiteral   c -> pretty c
        StringLiteral s -> pretty s
        Top    -> string "\\top" 
        Bottom -> string "\\bot"

instance Pretty HOLArity where 
    pretty (HOLArity (Arity Nothing n)) = string n
    pretty (HOLArity (Arity (Just ns) n)) = parens (sep $ punctuate comma $ map string ns) <+> string n

instance Pretty HOLTerm where 
    pretty = prettyHOLTerm 0

termAppPrecHOL = 100

prettyHOLTerm :: Precedence -> HOLTerm -> Doc
prettyHOLTerm p (HOLTerm tm) = case tm of
  TermIdent i           -> pretty $ HOLIdent i
  -- highest precedence and left associative
  TermApp t t'          -> prettyParen (p > termAppPrecHOL) $ prettyHOLTerm termAppPrecHOL (HOLTerm t) <+>
                             prettyHOLTerm (termAppPrecHOL+1) (HOLTerm t')
  TermWithType t typ    -> prettyParen True $ pretty (HOLTerm t) <+> string "::" <+> pretty (HOLType typ)
  QuantifiedTerm q is t -> prettyQuantifierHOL p q is t
  TermBinOp b t t'      -> prettyBinOpTermHOL p b (HOLTerm t) (HOLTerm t')
  -- TermBinOp b t t'      -> (case b of
  --                             MetaImp -> prettyMetaImpHOL p t t'
  --                             _       -> prettyBinOpTermHOL p b t t')
  TermUnOp u t          -> prettyUnOpTermHOL p u (HOLTerm t)
  ListTerm l ts r       -> pretty l <> hcat (intersperse (string ", ") (map (prettyHOLTerm termAppPrecHOL . HOLTerm) ts)) <> pretty r
  ConstTerm const       -> pretty const
  AntiTerm str          -> empty
  CaseOf e alts         -> parens (string "case" <+> pretty (HOLTerm e) <+> string "of" <$> sep (map ((text "|" <+> ). (prettyAssisHOL "=>")) alts))
  RecordUpd upds        -> string "<|" <+> sep (punctuate (text ";") (map (prettyAssisHOL ":=") upds)) <+> string "|>"
  RecordDcl dcls        -> string "<|" <+> sep (punctuate (text ";") (map (prettyAssisHOL ":=") dcls)) <+> string "|>"
  IfThenElse cond c1 c2 -> parens (string "if" <+> prettyHOLTerm p (HOLTerm cond) <+> string "then" <+> 
                            prettyHOLTerm p (HOLTerm c1) <+> string "else" <+> prettyHOLTerm p (HOLTerm c2))
  DoBlock dos           -> string "do" <$> sep (punctuate (text ";") (map (pretty . HOLTerm) dos)) <$> string "od"
  DoItem  a b           -> pretty (HOLTerm a) <+> string "<-" <+> pretty (HOLTerm b) --F
  Set st                -> string "{" <> (case st of 
                              Quant q c -> pretty (HOLTerm q) <> string "." <+> pretty (HOLTerm c)
                              Range a b -> pretty (HOLTerm a) <> string ".." <> pretty (HOLTerm b) 
                              Listing lst -> sep (punctuate (text ";") (map (pretty . HOLTerm) lst))) <> string "}"
                          -- FIXME: zoeyc
  LetIn lt i            -> string "let" <+> vsep (punctuate (text ";") (map (prettyAssisHOL "=") lt)) <$$> string "in" <$$> pretty (HOLTerm i)
                          -- FIXME: make indentation better / zoeyc

prettyAssisHOL :: String -> (Term, Term) -> Doc 
prettyAssisHOL s (p, e) = pretty (HOLTerm p) <+> pretty s <+> pretty (HOLTerm e)

prettyBinOpTermHOL :: Precedence -> TermBinOp -> HOLTerm -> HOLTerm -> Doc
prettyBinOpTermHOL p b = prettyBinOp p prettyHOLTerm (termBinOpRecHOL b) prettyHOLTerm

prettyUnOpTermHOL :: Precedence -> TermUnOp -> HOLTerm -> Doc
prettyUnOpTermHOL p u = prettyUnOp p (termUnOpRecHOL u) prettyHOLTerm

termBinOpRecHOL :: TermBinOp -> BinOpRec
termBinOpRecHOL b = case b of
  Equiv     -> BinOpRec AssocRight 2   "="
  MetaImp   -> BinOpRec AssocRight 1   "==>"
  Eq        -> BinOpRec AssocLeft  50  "="
  NotEq     -> BinOpRec AssocLeft  50  "<>"
  Iff       -> BinOpRec AssocRight 24  "IFF"
  Conj      -> BinOpRec AssocRight 35  "/\\" --F
  Disj      -> BinOpRec AssocRight 30  "\\/" --F
  Implies   -> BinOpRec AssocRight 25  "==>" --F
  DollarApp -> BinOpRec AssocRight 10  "$"
  Bind      -> BinOpRec AssocRight 60  ">>=" --F
  Image     -> BinOpRec AssocRight 90  "`" --F
  Union     -> BinOpRec AssocLeft  65  "UNION"
  Ge        -> BinOpRec AssocRight 50  ">="
  Alt       -> BinOpRec AssocRight 20  "TODO: Alt" --F
  Append    -> BinOpRec AssocLeft  65  "@" --F
  Greater   -> BinOpRec AssocRight 50  ">"
  Minus     -> BinOpRec AssocLeft  65  "-"
  Less      -> BinOpRec AssocLeft  50  "<"
  In        -> BinOpRec AssocRight 50  "IN"
  Add       -> BinOpRec AssocLeft  65  "+"
  Times     -> BinOpRec AssocLeft  70  "*" --F
  BitAND    -> BinOpRec AssocLeft  64  "AND" --F
  BitOR     -> BinOpRec AssocLeft  59  "OR" --F
  BitXOR    -> BinOpRec AssocLeft  59  "XOR"--F
  Shiftl    -> BinOpRec AssocLeft  55  "<<" --F
  Shiftr    -> BinOpRec AssocLeft  55  ">>" --F
  TestBit   -> BinOpRec AssocLeft  100 "!!" --F
  Nth       -> BinOpRec AssocLeft  100 "!" --F
  SubSetEq  -> BinOpRec AssocRight 50  "SUBSET" --F
  RestrictMp-> BinOpRec AssocRight 110 "|`" -- FIXME: zoeyc
  Comp      -> BinOpRec AssocRight 55  "o"
  MapsTo    -> BinOpRec AssocRight 100 "->"
  MapUpd    -> BinOpRec AssocRight 100 "|->"

termUnOpRecHOL :: TermUnOp -> UnOpRec
termUnOpRecHOL u = case u of
  Not    -> UnOpRec 40 "\\<not>"--F
  Uminus -> UnOpRec 81 "-" --F

prettyQuantifierHOL :: Precedence -> Quantifier -> [Term] -> Term -> Doc
prettyQuantifierHOL p q is t = prettyParen (p > quantifierPrecHOL q) $ string (quantifierSymHOL q) <>
                              (hsep . map (prettyHOLTerm 0. HOLTerm) $ is) <> char '.' <+> pretty (HOLTerm t)

instance Pretty HOLPrimType where
  pretty (HOLPrimType ty) = string $ case ty of
    IntT  -> "int"
    BoolT -> "bool"
    NatT  -> "nat"

instance Pretty HOLType where
  pretty = prettyHOLType 0

tyArrowSymHOL = "->"
tyTupleSymHOL = "#"

prettyTypeVarsHOL :: [HOLType] -> Doc
prettyTypeVarsHOL [] = empty
prettyTypeVarsHOL [ty] = prettyHOLType 100 ty -- application has highest precedence
prettyTypeVarsHOL tys = char '(' <> (hsep . punctuate (char ',') . map (prettyHOLType 0) $ tys) <> char ')'  -- FIXME: not very pretty / zilinc

prettyHOLType :: Precedence -> HOLType -> Doc
prettyHOLType p (HOLType ty) =
    case ty of
      TyVar v          -> char '\'' <> string v
      TyDatatype s tys -> prettyTypeVarsHOL (map HOLType tys) <+> string s
      TyPrim t         -> pretty (HOLPrimType t)
      -- TyArrow is right associative
      TyArrow t t'     -> prettyParen (p > pa) $ prettyHOLType (pa+1) (HOLType t) <+>
                          string tyArrowSymHOL <+> prettyHOLType pa (HOLType t')
      -- TyTuple is right associative
      TyTuple t t'     -> prettyParen (p > pt) $ prettyHOLType (pt+1) (HOLType t) <+>
                          string tyTupleSymHOL <+> prettyHOLType pt (HOLType t')
      AntiType t       -> string t  -- FIXME: zilinc
  where
     pa = 1
     pt = 2

------------------------------------------------------------------------

---------------         Outer                ---------------------------

------------------------------------------------------------------------


newtype HOLTheory types terms = HOLTheory (Theory types terms)
newtype HOLTheoryDecl types terms = HOLTheoryDecl (TheoryDecl types terms)
newtype HOLContext types terms = HOLContext (Context types terms)
newtype HOLDcl types terms  = HOLDcl (Dcl types terms)
newtype HOLPrc types terms = HOLPrc (Prc types terms)
newtype HOLLemma types terms = HOLLemma (Lemma types terms)
newtype HOLLemmas types terms = HOLLemmas (Lemmas types terms)
newtype HOLTypeSyn types terms = HOLTypeSyn (TypeSyn types terms)
newtype HOLTypeDecl types terms = HOLTypeDecl (TypeDecl types terms)
newtype HOLConsts types terms = HOLConsts (Consts types terms)
newtype HOLRecord types terms = HOLRecord (Record types terms)
newtype HOLDTCons types terms = HOLDTCons (DTCons types terms)
newtype HOLDatatype types terms = HOLDatatype (Datatype types terms)
newtype HOLClass types terms = HOLClass (Class types terms)
newtype HOLClassSpec types terms = HOLClassSpec (ClassSpec types terms)
newtype HOLInstantiation types terms = HOLInstantiation (Instantiation types terms)
newtype HOLInstance types terms = HOLInstance (Instance types terms)
newtype HOLInstanceHead = HOLInstanceHead InstanceHead
newtype HOLClassRel = HOLClassRel ClassRel 
newtype HOLFunFunc types terms = HOLFunFunc (FunFunc types terms)
newtype HOLEquations types terms = HOLEquations (Equations types terms)
newtype HOLTheoremDecl = HOLTheoremDecl TheoremDecl 
newtype HOLAttribute = HOLAttribute Attribute
newtype HOLProof = HOLProof Proof 
newtype HOLProofEnd = HOLProofEnd ProofEnd
newtype HOLMethod = HOLMethod Method 
newtype HOLMethodModifier = HOLMethodModifier MethodModifier 
newtype HOLDef types terms = HOLDef (Def types terms)
newtype HOLSig types = HOLSig (Sig types)
newtype HOLAbbrev types terms = HOLAbbrev (Abbrev types terms)
newtype HOLTheoryImports = HOLTheoryImports TheoryImports

convert :: Theory Type Term -> HOLTheory HOLType HOLTerm
convert = HOLTheory . ffmap HOLType . fmap HOLTerm

instance (Pretty terms, Pretty types) =>  Pretty (HOLTheory terms types) where
  pretty (HOLTheory thy) = pretty (HOLTheoryImports (thyImports thy)) <$$>
                           enableDoBlock <$>
                           string "val _ = new_theory\"" <> string (thyName thy) <>
                           string "\"" <$$>
                           prettyThyDeclsHOL (map HOLTheoryDecl (thyBody thy)) <>
                           string "val _ = export_theory ()" <$$> empty

prettyThyDeclsHOL :: (Pretty terms, Pretty types) => [HOLTheoryDecl types terms] -> Doc
prettyThyDeclsHOL [] = empty
prettyThyDeclsHOL thyDecls = (vsepPad . map pretty $ thyDecls) <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLTheoryDecl types terms) where
  pretty (HOLTheoryDecl d)  = case d of
    Definition def        -> pretty $ HOLDef def
    OverloadedDef def sig -> empty
    Abbreviation abbrev   -> pretty $ HOLAbbrev abbrev
    ContextDecl c         -> pretty $ HOLContext c
    LemmaDecl d'          -> pretty $ HOLLemma d'
    LemmasDecl ld         -> pretty $ HOLLemmas ld
    TypeSynonym ts        -> pretty $ HOLTypeSyn ts
    TypeDeclDecl td       -> pretty $ HOLTypeDecl td
    ConstsDecl c          -> pretty $ HOLConsts c
    RecordDecl fs         -> pretty $ HOLRecord fs
    DataTypeDecl dt       -> pretty $ HOLDatatype dt
    FunFunction ff f      -> pretty $ HOLFunFunc f  --FIXME: zoeyc 
    TheoryString s        -> string s
    PrimRec pr            -> pretty $ HOLPrc pr
    Declare dc            -> pretty $ HOLDcl dc

instance (Pretty terms, Pretty types) => Pretty (HOLContext types terms) where
  pretty (HOLContext (Context name cDecls)) = string "context" <+> string name <+> string "begin" <$$> 
                                 prettyThyDeclsHOL (map HOLTheoryDecl cDecls) <> string "end" <$$> empty 
-- FIXME : check context syntax / zoeyc

instance (Pretty terms, Pretty types) => Pretty (HOLDcl types terms) where
  pretty (HOLDcl (Dcl dclName dclRules)) = if (elem "simp" dclRules) 
    then string "export_rewrites \"" <> pretty dclName <> string "_def\"" <$$> empty 
    else empty

instance (Pretty terms, Pretty types) => Pretty (HOLPrc types terms) where
  pretty (HOLPrc (Prc thmDecl recCases)) =  string "Definition" <+> 
    pretty (fmap HOLSig thmDecl) <> string "_def:" <$$> vsep (punctuate (text "/\\") (map prettyRecHOL recCases)) 
    <$$> string "End" <$$> empty

prettyRecHOL :: (Pretty terms) => (terms, terms) -> Doc
prettyRecHOL (p, e) = parens (pretty p <+> pretty "=" <+> pretty e)

instance (Pretty terms, Pretty types) => Pretty (HOLLemma types terms) where
  pretty (HOLLemma (Lemma schematic thmDecl props proof)) = string "Theorem" <+>
    pretty (fmap HOLTheoremDecl thmDecl) <> string ":" <$$> indent 2 (vsep (punctuate (text "/\\") (map (parens. pretty) props))) 
    <$$> indent 2 (pretty proof) <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLLemmas types terms) where
  pretty (HOLLemmas (Lemmas name lems)) = string "Theorem" <+>
    pretty name <+> string "=" <$$> indent 2 (vsep $ map pretty lems) <$$> empty --FIXME: zoeyc

instance (Pretty terms, Pretty types) => Pretty (HOLTypeSyn types terms) where
  pretty (HOLTypeSyn (TypeSyn mbName typs tvs)) = string "Type" <+>
    prettyTypeVars (map TyVar tvs) <+>
    pretty mbName <+> string "=" <+> (quote. pretty) typs <> string ";" <$$> empty

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLTypeDecl types terms) where
  pretty (HOLTypeDecl (TypeDecl tdName tvs)) = string "Datatype:" <$$>
    prettyTypeVars (map TyVar tvs) <+> pretty tdName

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLConsts types terms) where
  pretty (HOLConsts (Consts sig)) = string "consts" <+> pretty sig 

instance (Pretty terms, Pretty types) => Pretty (HOLRecord types terms) where
  pretty (HOLRecord (Record rName rFields tvs)) = string "Datatype:" <$$>
    -- prettyTypeVars (map TyVar tvs) <+>
    pretty rName <+> string "= <|" <$$> 
    (vsep (punctuate (string ";") (map (\rf -> let RecField n t = rf in indent 2 (pretty n <+> string ":" <+> pretty t)) rFields)))
    <$$> string "|>" <$$> string "End" <$$> empty

instance (Pretty terms, Pretty types) => Pretty (HOLDTCons types terms) where
  pretty (HOLDTCons (DTCons cn ts)) = pretty cn <+> (hsep . map pretty $ ts)

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLDatatype types terms) where
  pretty (HOLDatatype (Datatype dtName dtCons tvs)) = string "Datatype:" <$$>
    prettyTypeVars (map TyVar tvs) <+>
    pretty dtName <+> string "=" <$$> (vsep $ punctuate (char '|') $ map (indent 2 . pretty. HOLDTCons) dtCons) 
    <$$> string "End" <$$> empty

-- FIXME: HOL4 does not have such concept as a "class" / zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLClass types terms) where
  pretty (HOLClass (Class spec body)) = empty

instance (Pretty terms, Pretty types) => Pretty (HOLClassSpec types terms) where
  pretty (HOLClassSpec ClassSpec) = error "TODO: instance Pretty (ClassSpec types terms)"  -- TODO: zilinc

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLInstantiation types terms) where
  pretty (HOLInstantiation (Instantiation names arity body)) = empty
    -- string "instantiation" <+> sep (punctuate (string "and") (map pretty names))
    -- <+> string "::" <+> pretty arity
    -- <$> string "begin" 
    -- <$> prettyThyDecls body <> string "end" <$> empty

-- FIXME: zoeyc
instance (Pretty terms, Pretty types) => Pretty (HOLInstance types terms) where
  pretty i = empty
    -- string "instance" <+> pretty head
    -- <$> prettyThyDecls body

-- FIXME: zoeyc
instance Pretty HOLInstanceHead where
  pretty h = empty
  -- pretty (HOLInstanceHead InstanceHeadNo) = empty
  -- pretty (HOLInstanceHead (InstanceHeadTh names arity)) = 
  --   sep (punctuate (string "and") (map pretty names)) <+> string "::" <+> pretty arity
  -- pretty (HOLInstanceHead (InstanceHeadIn name rel super)) =
  --   pretty name <+> pretty rel <+> pretty super

-- FIXME: zoeyc
instance Pretty HOLClassRel where
  pretty cr = empty
  -- pretty (HOLClassRel ClassLessThan) = string "<"
  -- pretty (HOLClassRel ClassSubsetOf) = string "⊆"  -- FIXME: zilinc

-- FIXME: zoeyc
instance (Pretty types, Pretty terms) => Pretty (HOLFunFunc types terms) where
  pretty (HOLFunFunc (FunFunc sigs bd)) = string "Definition" <+>  (encloseSep empty empty (string "and" <> space) (map (pretty . HOLSig) sigs))
                            <+> string "_def:"
                            <$$> align (pretty (HOLEquations bd))

instance (Pretty types, Pretty terms) => Pretty (HOLEquations types terms) where
  pretty (HOLEquations (Equations terms)) = vsep $ punctuate (space <> string "/\\") $ map (parens. pretty) terms

instance Pretty HOLTheoremDecl where
  pretty (HOLTheoremDecl (TheoremDecl mbName attributes))
    | Nothing <- mbName, null attributes =
        error "In TheoremDecl, name == Nothing and attributes == [] is not allowed"
    | otherwise = maybe empty string mbName <> pattrs
       where pattrs =  case attributes of
                  [] -> empty
                  attrs -> findSimp attrs

findSimp :: [Attribute] -> Doc
findSimp attrs = case attrs of 
    []                     -> empty 
    (Attribute nm args):xs -> if nm == "simp" then string "[simp]" else findSimp xs  

instance Pretty HOLAttribute where
  pretty (HOLAttribute attr) = findSimp [attr] 

instance Pretty HOLProof where
  pretty (HOLProof (Proof methods proofEnd)) =
    (vsep (punctuate (string ">>") (map (\m -> string "APPLY_TAC" <+> brackets (pretty (HOLMethod m))) methods))) 
    <$$> pretty proofEnd
-- FIXME: proof translation needed / zoeyc

instance Pretty HOLProofEnd where
  pretty (HOLProofEnd e) = end <$$> string "QED" <$$> empty
    where end = case e of
                 ProofDone  -> empty
                 ProofSorry -> string "cheat"

instance Pretty HOLMethod where
  pretty = prettyMethodTopLevelHOL 0

prettyMethodTopLevelHOL p (HOLMethod m) = case m of
  Method name []      -> string name
  MethodModified m mm -> (parens $ prettyMethodHOL p m) <> pretty mm
  _                   -> parens $ prettyMethodHOL p m

prettyMethodHOL :: Int -> Method -> Doc
prettyMethodHOL p m = case m of
    Method name args ->
      hsep . map string $ name:args
    MethodModified m' mm -> prettyMethodTopLevelHOL p (HOLMethod m') <> pretty (HOLMethodModifier mm)
    MethodCompound binOp m' m'' -> 
      prettyBinOp p prettyMethodHOL (methodBinOpRec binOp) prettyMethodHOL m' m''
    
instance Pretty HOLMethodModifier where
  pretty (HOLMethodModifier m) = case m of
    MMOptional  -> string "?" -- FIXME: zoeyc 
    MMOneOrMore -> string "+" -- FIXME: zoeyc
    MMGoalRestriction mbI -> brackets $ maybe empty (string . show) $ mbI --FIXME: zoeyc

instance (Pretty terms, Pretty types) => Pretty (HOLDef types terms) where
  pretty (HOLDef def) = string "Definition" <+> mbSig <$$> indent 2 (pretty (defTerm def)) <$$> string "End"
    where mbSig = case defSig def of 
                    Just sig -> (string (sigName sig)) <> string "_def:" 
                    Nothing  -> empty

--FIXME: zoeyc
prettyOvHOL specDef sig = string "overloading" <> mbSig
                  <$$> string "begin"
                  <$$> indent 2 mbDefn
                  <$$> string "end"
    where mbSig = case defSig specDef of 
                    Just specSig ->
                      empty
                        <$$> indent 2 (pretty (HOLSig specSig))
                          <> string "="
                          <> pretty sig
                    _ -> empty
          mbDefn =
            case defSig specDef of 
              Just specSig ->
                string "Definition " <> pretty specSig <> string "_def: " <> quote (pretty (defTerm specDef))
              _ -> empty

instance Pretty types => Pretty (HOLSig types) where
  pretty (HOLSig d) = string (sigName d)

instance (Pretty terms, Pretty types) => Pretty (HOLAbbrev types terms) where
  pretty (HOLAbbrev a) = string "Overload" <+> mbSig <+> (indent 2 (holQuote (pretty (abbrevTerm a))))
    where mbSig = case abbrevSig a of 
                    Just sig -> pretty (HOLSig sig) <+> string "="
                    Nothing  -> empty

holQuote :: Doc -> Doc
holQuote doc = string "``" <>  doc <> string "``"

instance Pretty HOLTheoryImports where
  pretty (HOLTheoryImports (TheoryImports is)) = vsep (map openTheory is)

openTheory :: String -> Doc 
openTheory s = string  "open"
            <+> (string . takeFileName . dropWhile (== '\"') . dropWhileEnd (== '\"') $ s)
            <> string "Theory;"

enableDoBlock :: Doc 
enableDoBlock = string "val _ = ParseExtras.temp_loose_equality();\nval _ = patternMatchesLib.ENABLE_PMATCH_CASES();\nval _ = monadsyntax.temp_add_monadsyntax();"
-- smart constructor

mkComment :: String -> TheoryDecl types terms
mkComment s = TheoryString $ "(* " ++ s ++ " *)"
