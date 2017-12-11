module Syntax (
  module Syntax
, module P
) where

import Text.Parsec.Pos as P

type Ident          = String
type OpIdent        = Maybe Ident
type Param          = (OpIdent, Type)
type Arg            = Expr
type Instance       = Ident
type TyConstraint   = Maybe (Maybe Instance, Constraint)
type Constraint     = Expr

data Field          = Field  { fIdent       :: OpIdent
                             , fType        :: Type 
                             , fConstraint  :: (Maybe Constraint) 
                             , fPosition    :: !SourcePos }

data BField         = BField { bfTag        :: Tag
                             , bfIdent      :: OpIdent
                             , bfNoB        :: Expr
                             , bfConstraint :: (Maybe Constraint)
                             , bfPosition   :: !SourcePos }

data Case           = Case   { cCase        :: Expr
                             , cField       :: Field
                             , cPosition    :: !SourcePos }

data Func           = Func { func :: Ident } deriving (Eq)
data Tag            = Tag  { tag  :: Bool  } deriving (Eq)


data Physable       = Phys Endian | View deriving (Eq)
data Endian         = LEn | BEn deriving (Eq)

instance Ord Physable where
  compare (Phys en1) (Phys en2) = compare en1 en2
  compare (Phys _  ) View = LT 

instance Ord Endian where
  compare LEn BEn = LT

data Type           = Bool
                    | UInt   Integer Physable
                    | Array  Type    Expr
                    | CompTy Ident   [Arg]

instance Eq Type where
    Bool                == Bool                = True
    UInt   8   (Phys _) == UInt   8   (Phys _) = True
    UInt   is1 en1      == UInt   is2 en2      = (is1 == is2) && (en1 == en2)
    CompTy id1 _        == CompTy id2 _        = id1 == id2
    Array  ty1 _        == Array  ty2 _        = ty1 == ty2
    _                   == _                   = False

instance Ord Type where
    Bool <= (UInt _ _)  = True
    (UInt is1 en1) <= (UInt is2 en2) = 
      if en1 == en2 then is1 <= is2 else en1 <= en2
    (UInt  _ _) <= (Array  _ _) = True
    (Array _ _) <= (CompTy _ _) = True
    (CompTy id1 _) <= (CompTy id2 _) = id1 <= id2
    (Array  ty1 _) <= (Array  ty2 _) = ty1 <= ty2
    ty1 <= ty2 = ty1 == ty2

data Expr           = ILit Integer            !SourcePos   
                    | BLit Bool               !SourcePos
                    | Var Ident               !SourcePos
                    | BinExpr BinOp Expr Expr !SourcePos
                    | UnExpr UnOp Expr        !SourcePos
                    | App Func [Arg]          !SourcePos
                    | Member Expr Ident       !SourcePos

data BinOp          = Or                        -- Lowest Precedence
                    | And
                    | Eq | Ne
                    | Gt | Ge | Lt | Le
                    | BitOr
                    | BitXor
                    | BitAnd
                    | AddOp | SubOp
                    | MulOp | DivOp | ModOp     -- Highest Precedence
                      deriving (Eq)

data UnOp           = Not
                    | Plus | Minus | BitComp
                      deriving (Eq)

data DataDesc       = DStruct   Ident [Param]      [Field]    TyConstraint !SourcePos
                    | DBitfield Ident [Param] Type [BField]   TyConstraint !SourcePos
                    | DTUnion   Ident [Param] Type [Case]                  !SourcePos
                    | DBUnion   Ident [Param] Type [Case]                  !SourcePos
                    | DTypeSyn  Ident [Param] Type            TyConstraint !SourcePos
                    | DEnum     Ident         Type [Expr]                  !SourcePos
                    | DConst    Ident         Type  Expr                   !SourcePos

getIdent :: DataDesc -> Ident
getIdent (DStruct   id _ _ _   _) = id 
getIdent (DBitfield id _ _ _ _ _) = id 
getIdent (DTUnion   id _ _ _   _) = id 
getIdent (DBUnion   id _ _ _   _) = id 
getIdent (DTypeSyn  id _ _ _   _) = id 
getIdent (DEnum     id _ _     _) = id
getIdent (DConst    id _ _     _) = id

getPos :: DataDesc -> SourcePos
getPos (DStruct   _ _ _ _   pos) = pos  
getPos (DBitfield _ _ _ _ _ pos) = pos  
getPos (DTUnion   _ _ _ _   pos) = pos  
getPos (DBUnion   _ _ _ _   pos) = pos  
getPos (DTypeSyn  _ _ _ _   pos) = pos  
getPos (DEnum     _ _ _     pos) = pos 
getPos (DConst    _ _ _     pos) = pos 

isBaseType :: Type -> Bool
isBaseType (Array  _ _) = False
isBaseType (CompTy _ _) = False
isBaseType _ = True


