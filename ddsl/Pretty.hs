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
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
    PatternGuards, OverlappingInstances #-}

module Pretty 
  ( prettyDs    -- FIXME: will be deprecated soon
  , prettyMods
  , prettyMod
  , prettyErr
  , prettyCheck
  , prettyDelta
  , prettyCogent
  , prettyCogent_
  , genPrefix
  , genPREFIX
  , Nameable
  , toName 
  , pShow
  ) where

import Syntax
-- import Parse
import Check
-- import Rewrite
import Kinds
import Util

import qualified COGENT.Syntax as CS
import COGENT.PrettyPrint (prettyPrint)

import Data.Char (ord)
import Data.List as L
import Data.Map  as M hiding (empty)
import Data.Maybe (fromJust)
import Data.Tuple.Select
import Text.PrettyPrint.ANSI.Leijen as P
import System.IO 

data Associativity = LeftAssoc  Integer 
                   | RightAssoc Integer 
                   | NoAssoc    Integer 
                   | Prefix 
                   deriving Eq

class Levelable t where
  level :: t -> Integer

instance Levelable Associativity where
  level (LeftAssoc i) = i
  level (RightAssoc i) = i
  level (NoAssoc i) = i
  level (Prefix) = 0

instance Levelable Expr where
  level (BinExpr op e1 e2 _) = level $ assocB op
  level (UnExpr  op e     _) = level $ assocU op
  level (App     f  as    _) = 2
  level _ = 0

instance Levelable Kind where 
  level (Arrow _ _) = 2
  level _ = 0

instance Levelable Type where
  level (Array  _ _ ) = 2
  level (CompTy _ []) = 0
  level (CompTy _ _ ) = 2
  level _ = 0

prettyLv :: (Levelable p, Pretty p) => Integer -> p -> Doc
prettyLv l x | level x < l = pretty x
             | otherwise = parens (pretty x)

-- DSyntax

assocB :: BinOp -> Associativity
assocB x | x `elem` [MulOp, DivOp, ModOp] = LeftAssoc 4
         | x `elem` [AddOp, SubOp] = LeftAssoc 6
         | x `elem` [BitAnd] = LeftAssoc 8
         | x `elem` [BitXor] = LeftAssoc 10
         | x `elem` [BitOr]  = LeftAssoc 12
         | x `elem` [Gt, Ge, Lt, Le] = NoAssoc 14
         | x `elem` [Eq, Ne] = LeftAssoc 16
         | x `elem` [And] = LeftAssoc 18
         | x `elem` [Or]  = LeftAssoc 20

assocU :: UnOp -> Associativity
assocU x = Prefix

instance Pretty Ident where
  pretty id = text id
instance Pretty OpIdent where
  pretty Nothing = text "_"
  pretty (Just id) = pretty id
instance Pretty Field where
  pretty (Field oid ty Nothing  _) = pretty oid <+> text "::" <+> pretty ty
  pretty (Field oid ty (Just c) _) = hang 2 $ pretty oid <+> text "::" <+> pretty ty </> 
                                       text "where" <+> align (pretty c)
instance Pretty BField where
  pretty (BField tag oid expr Nothing  _) = pretty tag <> pretty oid <+> text "::" <+> pretty expr
  pretty (BField tag oid expr (Just c) _) = hang 2 $ pretty tag <> pretty oid <+> text "::" <+> pretty expr </> 
                                              text "where" <+> align (pretty c)
instance Pretty Tag where
  pretty (Tag True)  = text "tag" <+> empty
  pretty (Tag False) = empty
instance Pretty Case where
  pretty (Case expr f _) = pretty expr <+> text "->" </> pretty f
instance Pretty [Param] where
  pretty [] = empty
  pretty ps = empty <+> (encloseSep lbrace rbrace (comma <+> empty) $ L.map pretty ps)
instance Pretty Param where
  pretty (oid, ty) = pretty oid <+> text "::" <+> pretty ty
instance Pretty TyConstraint where
  pretty Nothing = empty
  pretty (Just (Nothing , cons)) = empty </> (text "where" <+> align (pretty cons))
  pretty (Just (Just ins, cons)) = empty </> align (text "instance" <+> pretty ins </> 
                                               (text "where" <+> align (pretty cons)))
instance Pretty [Arg] where
  pretty [] = empty
  pretty as = empty <+> (hsep $ L.map (prettyLv 2) as)

instance Pretty Type where
  pretty Bool = text "Bool"
  pretty (UInt is View) = text "U" <> integer is
  pretty (UInt 8  (Phys _ )) = text "Pu8"
  pretty (UInt is (Phys en)) = text "P" <> (if en == LEn then text "le" else text "be") <> integer is
  pretty (Array  ty expr) = text "Array" <+> prettyLv 2 ty <+> prettyLv 2 expr
  pretty (CompTy id args) = pretty id <> pretty args

instance Pretty BinOp where
  pretty Or     = text "||"
  pretty And    = text "&&"
  pretty Eq     = text "=="
  pretty Ne     = text "/="
  pretty Gt     = text ">"
  pretty Ge     = text ">="
  pretty Lt     = text "<"
  pretty Le     = text "<="
  pretty BitOr  = text ".|."
  pretty BitXor = text ".^."
  pretty BitAnd = text ".&."
  pretty AddOp  = text "+"
  pretty SubOp  = text "-"
  pretty MulOp  = text "*"
  pretty DivOp  = text "/"
  pretty ModOp  = text "%"

instance Pretty UnOp where
  pretty Not     = text "!"
  pretty Plus    = text "+"
  pretty Minus   = text "-"
  pretty BitComp = text "~"

instance Pretty Expr where
  pretty (ILit  n _) = integer n
  pretty (BLit  b _) = text $ show b
  pretty (Var   v _) = pretty v
  pretty (BinExpr op e1 e2 _) 
    | LeftAssoc  l <- assocB op = pretty e1 <+> pretty op </> prettyLv l e2
    | RightAssoc l <- assocB op = prettyLv l e1 <+> pretty op </> pretty e2
    | NoAssoc    _ <- assocB op = pretty e1 <+> pretty op </> pretty e2 
  pretty (UnExpr op e _) = pretty op <> prettyLv 2 e
  pretty (App f args _) = pretty f <> pretty args
  pretty (Member e v _) = pretty e <> dot <> pretty v

instance Pretty Func where
  pretty (Func f) = pretty f

keyword = bold . magenta . text

instance Pretty DataDesc where
  pretty (DStruct id ps fs tc _) = 
    keyword "data" <+> pretty id <> pretty ps <+> equals <+> lbrace <$>
    indent 2 (align $ vsep $ punctuate comma (L.map pretty fs)) <$> rbrace <>
    pretty tc
  pretty (DBitfield id ps t bs tc _) = 
    keyword "data" <+> pretty id <> pretty ps <+> text "::" <+> pretty t <+> equals <+> lbrace <$>
    indent 2 (align $ vsep $ punctuate comma (L.map pretty bs)) <$> rbrace <>
    pretty tc
  pretty (DTUnion id ps t cs _) = 
    keyword "data" <+> pretty id <> pretty ps <+> equals </>
    text "case" <+> text "tag" <+> text "::" <+> pretty t <+> text "of" <$>
    indent 2 (align $ vsep $ punctuate semi (L.map pretty cs))
  pretty (DBUnion id ps t cs _) = 
    keyword "data" <+> pretty id <> pretty ps <+> text "::" <+> pretty t <+> equals </>
    text "case" <+> text "tag" <+> text "of" <$>
    indent 2 (align $ vsep $ punctuate semi (L.map pretty cs))
  pretty (DTypeSyn id ps t tc _) = 
    keyword "type" <+> pretty id <> pretty ps <+> equals </>
      pretty t <>
      pretty tc
  pretty (DEnum id t es _) = 
    keyword "enum" <+> pretty id <+> text "::" <+> pretty t <+> equals </>
    encloseSep (lbrace <+> empty) (empty <+> rbrace) (comma <+> empty) (L.map pretty es)
  pretty (DConst id t e _) = 
    keyword "const" <+> pretty id <+> text "::" <+> pretty t <+> equals </> pretty e

instance Pretty ModHead where
  pretty (ModHead []) = empty
  pretty (ModHead imps) = vsep (L.map (\imp -> keyword "import" <+> dquote <> pretty imp <> dquote) imps) <$> empty

instance Pretty [ModName] where
  pretty [] = empty
  pretty ns = hcat $ punctuate comma (L.map pretty ns)

instance Pretty ModName where
  pretty (ModName n) = string n

instance Pretty Module where
  pretty (Module name head ds) =     dullred (bold (pretty name <> string ":"))
                                 <$> dullblue (indent 2 
                                       (pretty head <//> vsep (L.map pretty ds))) 
                                 <$> empty

-------------------------------------------------------------------------------
-- DChecker

-- quotes
qt :: Doc -> Doc
qt x = text "`" <> x <> text "'"

instance Pretty Err where
  pretty (Err ph id msg ctx pos) = 
    text (sourceName pos) <> text ": Line" <+> integer (fromIntegral $ sourceLine pos) <+> parens (pretty ph) <> colon <$>
    indent 4 (pretty msg) <> 
    prettyErrContext ctx <$>
    indent 4 (text "In block" <+> qt (pretty id))

instance Pretty ErrPhase where
  pretty DepErr = text "Dependency"
  pretty WfkErr = text "Well-formedness and kinding"
  pretty ConErr = text "Constant folding"

instance Pretty ErrMsg where
  pretty (KindMismatch ke ka) = text "Kind mismatch:" <$> 
                            indent 2 (text "Expected kind:" <+> pretty ke) <$>
                            indent 2 (text "Actual kind:"   <+> pretty ka)
  pretty (SizeMismatch se sa) = text "Size mismatch:" <$> 
                            indent 2 (text "Expected size:" <+> pretty se) <$>
                            indent 2 (text "Actual size:"   <+> pretty sa)
  pretty (PosMismatch  pe pa) = text "Position mismatch:" <$> 
                            indent 2 (text "Expected position:" <+> pretty pe) <$>
                            indent 2 (text "Actual position:"   <+> pretty pa)
  pretty (IntOutOfRange n) = text "Integral out of range:" <+> integer n
  pretty NoField  = text "No field in a Struct"
  pretty NoBField = text "No b-field in a Bitfield"
  pretty NoCase   = text "No case in a Union"
  pretty (RedeclTopLevel id) = text "Redeclared top level data:" <+> pretty id
  pretty (CyclicType  id)  = text "Cyclic definition of type:" <+> pretty id
  pretty (UndeclType  id)  = text "Undeclared type:" <+> pretty id
  pretty (RedeclVar   id)  = text "Redeclared variable:" <+> pretty id
  pretty (UndeclVar   id)  = text "Variable" <+> qt (pretty id) <+> text "not in scope"
  pretty (CyclicConst id)  = text "Cyclic definition of constant:" <+> pretty id
  pretty (UndeclConst id)  = text "Constant" <+> qt (pretty id) <+> text "not in scope"
  pretty (UndeclFunc  f)   = text "Undefined function:" <+> pretty f
  pretty (TooManyArgs c)   = let c' = case c of
                                        Left (Func id) -> text "Function" <+> qt (pretty id)
                                        Right t | CompTy id _ <- t -> text "Type contructor" <+> qt (pretty id)  
                             in c' <+> text "is applied to too many arguments"
  pretty (TooFewArgs c)    = let c' = case c of
                                        Left (Func id) -> text "Function" <+> qt (pretty id)
                                        Right t | CompTy id _ <- t -> text "Type contructor" <+> qt (pretty id)  
                             in c' <+> text "is applied to too few arguments"
  pretty (NoArg       f)   = text "Function" <+> qt (pretty f) <+> text "is applied to no argument"
  pretty (FuncNoStatic f) = hang 2 $ text "Function" <+> qt (pretty f) <+> text "is dynamic," <+>
                               text "whereas a static term is expected"
  pretty (VarNoStatic id) = hang 2 $ text "Variable" <+> qt (pretty id) <+> text "is dynamic," <+>
                               text "whereas a static term is expected"
  pretty (CaseOverlap c c') = hang 2 $ text "Overlapping alternative identifiers:" <$>
                                qt (pretty c) <+> text "and" <$> qt (pretty c')
  pretty (TagOverlap c c') = hang 2 $ text "Overlapping cases:" <$>
                               qt (pretty c) <+> text "and" <$> qt (pretty c')
  pretty NoTagInBUnion = text "No tag in a Bitfield"
  pretty (DupTagInBUnion bf) = hang 2 $ text "Dupliacated tag on bit-field" <+> qt (pretty bf) </> 
                                 text "in a Bitfield"
  pretty (BinOpKind op t) = hang 2 $ text "Operator " <+> qt (pretty op) <+> text "does not have type:" </>
                              pretty t
  pretty (ExprsKindMismatch (e1, k1) (e2, k2)) = 
    hang 2 $ text "Expressions" <+> qt (pretty e1) <+> text "and" <+> qt (pretty e2) </>
      text "should be both Integral or Bool, but" <$>
      text "Expression:" <+> pretty e1 <+> text "::" <+> pretty k1 <$>
      text "Expression:" <+> pretty e2 <+> text "::" <+> pretty k2
  pretty (OtherErr s) = text (show s)

instance Pretty ErrKind where
  pretty (JustKind    k) = pretty k
  pretty (AtMostKind  k) = text "At most"  <+> qt (pretty k)
  pretty (AtLeastKind k) = text "At least" <+> qt (pretty k)
  pretty (KindClass   c) = pretty c
  pretty (KindOfSize  i) = integer i <> text "-bit Integral kind"
  pretty (MiscKind    t) = string t

instance Pretty KindClass where
  pretty AK  = text "Atomic kind"
  pretty BK  = text "Base kind"
  pretty IK  = text "Integral kind"
  pretty IPK = text "Integral physical kind"
  pretty IVK = text "Integral view kind"
  pretty PK  = text "Physical kind"

prettyErrContext :: ErrContext -> Doc
prettyErrContext NoErrContext = empty
prettyErrContext c = empty <$> indent 4 (pretty c)

instance Pretty ErrContext where
  pretty NoErrContext          = empty
  pretty ErrSizeOfBitfield     = text "In the size of Bitfield" 
  pretty (ErrSizeOfArr    e t) = text "In the expression:" <+> pretty e <$> 
                                 text "In the size of Array:" <+> pretty t
  pretty (ErrTypeOfSwitch   t) = text "In the switch type:" <+> pretty t 
  pretty (ErrTypeOfBitfield t) = text "In the Bitfield type:" <+> pretty t
  pretty (ErrTypeOfBUnion   t) = text "In the BUnion type:" <+> pretty t
  pretty (ErrTypeOfTypeSyn  t) = text "In the existing type:" <+> pretty t
  pretty (ErrTypeOfEnum     t) = text "In the Enum type:" <+> pretty t
  pretty (ErrTypeOfConst    t) = text "In the Const type:" <+> pretty t
  pretty (ErrTypeOfArrElem  t arr) = text "In the element type:" <+> pretty t <$>
                                     text "In the Array type:" <+> pretty arr
  pretty (ErrTypeOfCase   t c) = text "In the type of case:" <+> pretty t <$>
                                 text "In the case:" <+> pretty c
  pretty (ErrExpr           e) = text "In the expression:" <+> pretty e
  pretty (ErrParam          p) = text "In the parameter:" <+> pretty p
  pretty (ErrArg          a c) = text "In the argument:" <+> pretty a <$> 
                                 case c of
                                   Left (Func id) -> text "In the function:" <+> pretty id
                                   Right t | CompTy id _ <- t -> text "In the type:" <+> pretty id
  pretty (ErrEnumItem       e) = text "In the Enum item:" <+> pretty e
  pretty (ErrExprInConst    e) = text "In the Const expression:" <+> pretty e
  pretty (ErrField          f) = text "In the field:" <+> pretty f
  pretty (ErrBField         b) = text "In the b-field:" <+> pretty b
  pretty (ErrConstraint     e) = text "In the constraint:" <+> pretty e
  pretty (ErrTagInCase    e c) = text "In the tag:" <+> pretty e <$>
                                 text "In the case:" <+> pretty c
  pretty (ErrSizeOfTag      c) = text "In the size of tag in case:" <+> pretty c
  pretty (ErrPosOfTag       c) = text "In the position of tag in case:" <+> pretty c

instance Pretty Value where
  pretty BadV = text "Unknown value"
  pretty (IConst n) = integer n
  pretty (BConst b) = text $ show b
  pretty (IEnum ns) = encloseSep lbrace rbrace comma (L.map pretty ns)

-------------------------------------------------------------------------------
--DKind

instance Pretty Kind where
  pretty (Atom  s  ) = pretty s
  pretty (Arrow s k) = prettyLv 2 s <+> text "->" <+> prettyLv 2 k
  pretty BadK        = text "Erroneous kind"

instance Pretty TagInfo where
  pretty Nothing       = langle <> text "_"  <> comma <+> text "_"  <> rangle
  pretty (Just (p, s)) = langle <> integer p <> comma <+> integer s <> rangle

instance Pretty CtnInfo where
  pretty Nothing  = langle <> text "_" <> rangle
  pretty (Just k) = langle <> pretty k <> rangle

instance Pretty Singleton where
  pretty KBool  = text "Bool"
  pretty (KUInt is en) = pretty $ UInt is en
  pretty (KArray s) = lbracket <> pretty s <> rbracket
  pretty (KEnum  s) = lbrace   <> pretty s <> rbrace
  pretty (KStruct   id) = text "Struct"   <+> pretty id
  pretty (KTUnion   id) = text "TUnion"   <+> pretty id
  pretty (KBitfield id c) = text "Bitfield" <+> pretty id <+> pretty c
  pretty (KBUnion   id c t) = text "BUnion" <+> pretty id <+> pretty c <+> pretty t
  pretty KAny = text "*"

-------------------------------------------------------------------------------

prettyMods :: [Module] -> IO ()
prettyMods = mapM_ prettyMod

prettyMod :: Module -> IO ()
prettyMod m = displayIO stdout $ renderPretty 1 100 $ pretty m

prettyDs :: [DataDesc] -> IO ()
prettyDs ds = displayIO stdout $ renderPretty 1 100 $ dullblue $ 
                indent 2 (vsep $ L.map pretty ds) <$> empty

prettyErr :: [Err] -> IO ()
prettyErr errs = displayIO stdout $ renderPretty 1 100 $
                   vcat (L.map pretty errs) <$> empty

heading :: Doc -> Doc
heading = bold . onyellow 

prettyCheck :: (Def, Delta, Pi) -> IO ()
prettyCheck (def, del, pii) = do
  displayIO stdout $ renderPretty 1 100 $ dullblue $ indent 2 $
    (heading . text) "1) Dependencies" <$>
    indent 2 (vsep (L.map
      (\(k, v) -> fillBreak width (pretty k) <+> text "|" <+> integer (snd v))
      (toList def))) <$>
    (heading . text) "2) Delta" <$>
    indent 2 (vsep (L.map
      (\(t, k) -> fillBreak width (pretty t) <+> text "|" <+> pretty k) (toList del))) <$>
    (heading . text) "3) Pi" <$> 
    indent 2 (vsep (L.map
      (\(c, (k, v)) -> fillBreak width (pretty c) <+> 
        text "::" <+> pretty k <+> equals <+> pretty v) 
      (toList pii))) 
  putDoc (empty <$> empty)
  where width = (sum $ L.map length (keys def)) `div` size def + 10

prettyDelta :: Delta -> IO ()
prettyDelta del = do
  displayIO stdout $ renderPretty 1 100 $ dullblue $ indent 2 $ 
    (heading . text) "*) Delta" <$>
    indent 2 (vsep (L.map
      (\(t, k) -> fillBreak width (pretty t) <+> text "|" <+> pretty k) (toList del)))
  putDoc (empty <$> empty)
  where width = (sum $ L.map length (keys del)) `div` size del + 10

prettyCogent :: [CS.Definition CS.RawStmt CS.RawExpr] -> IO ()
prettyCogent = prettyPrint

prettyCogent_ :: FilePath -> [CS.Definition CS.RawStmt CS.RawExpr] -> IO ()
prettyCogent_ f x = do h <- openFile f WriteMode
                     hPutStrLn h "-- FIXME: change `include' statement to the correct path to `lib.cogent'\n"
                     displayIO h $ renderPretty 1 100 $ plain $ vcat $ L.map pretty x
                     hClose h   

-------------------------------------------------------------------------------
-- Code gen

genPrefix = "dg_"
genPREFIX = "DG_"

arrayPrefix = genPREFIX ++ "Array_"

class Nameable c where
  toName :: c -> String

instance Nameable Ident where
  toName id = id

instance Nameable OpIdent where
  toName = toName . fromJust

instance Nameable Type where
  toName (CompTy id _) = toName id
  toName (Array ty _) = arrayPrefix ++ toName ty
  toName ty = pShow ty

instance Nameable BinOp where
  toName op = pShow op

instance Nameable UnOp where
  toName op = pShow op

pShow :: Pretty t => t -> String
pShow = show . plain . pretty
