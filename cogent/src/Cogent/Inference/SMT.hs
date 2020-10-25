--
-- Copyright 2019, Data61
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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Cogent.Inference.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax as S
import Cogent.Common.Types
import Cogent.Core
import Cogent.PrettyPrint (indent', warn)
import Cogent.TypeCheck.Util (traceTc)

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State
import Data.Nat
import Data.Fin
import Data.IntMap as IM
import Data.Map    as M
import Data.Maybe (fromMaybe)
import Data.SBV as SMT hiding (proveWith)
import Data.SBV.Dynamic as SMT
import Data.Vec hiding (repeat, splitAt, length, zipWith, zip, unzip)
import Lens.Micro.Mtl
import Lens.Micro.TH
import Prelude as P
import qualified Text.PrettyPrint.ANSI.Leijen as L

upshiftVarLExpr :: LExpr t b -> LExpr t b
upshiftVarLExpr (LVariable (t, b)) = LVariable (Suc t, b)
upshiftVarLExpr (LOp opr es) = LOp opr (P.map upshiftVarLExpr es)
upshiftVarLExpr (LApp a b) = LApp (upshiftVarLExpr a) (upshiftVarLExpr b)
upshiftVarLExpr (LCon tn e t) = LCon tn (upshiftVarLExpr e) t
upshiftVarLExpr (LLet a e1 e2) = LLet a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
upshiftVarLExpr (LLetBang bs a e1 e2) = LLetBang bs a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
upshiftVarLExpr (LTuple e1 e2) = LTuple (upshiftVarLExpr e1) (upshiftVarLExpr e2)
upshiftVarLExpr (LStruct fs) = LStruct $ P.map (\(fn, e) -> (fn, upshiftVarLExpr e)) fs
upshiftVarLExpr (LIf c t e) = LIf (upshiftVarLExpr c) (upshiftVarLExpr t) (upshiftVarLExpr e)
upshiftVarLExpr (LCase e tn (v1, a1) (v2, a2)) = LCase (upshiftVarLExpr e) tn (v1, upshiftVarLExpr a1) (v2, upshiftVarLExpr a2)
upshiftVarLExpr (LEsac e) = LEsac $ upshiftVarLExpr e
upshiftVarLExpr (LSplit (v1, v2) e1 e2) = LSplit (v1, v2) (upshiftVarLExpr e1) (upshiftVarLExpr e2)
upshiftVarLExpr (LMember x f) = LMember (upshiftVarLExpr x) f
upshiftVarLExpr (LTake (a,b) rec f e) = LTake (a,b) rec f (upshiftVarLExpr e)
upshiftVarLExpr (LPut rec f v) = LPut rec f (upshiftVarLExpr v)
upshiftVarLExpr (LPromote t e) = LPromote t (upshiftVarLExpr e)
upshiftVarLExpr (LCast t e) = LCast t (upshiftVarLExpr e)
upshiftVarLExpr x = x
-- also upshift in refinement type preds in context?

data NatVec :: Nat -> * -> * where
  NvNil :: NatVec Zero a
  NvCons :: a -> NatVec n a -> NatVec (Suc n) a
deriving instance Show a => Show (NatVec n a)
deriving instance Eq a => Eq (NatVec n a)

instance Foldable (NatVec n) where
  foldMap f NvNil = mempty
  foldMap f (NvCons x y) = f x <> foldMap f y

nvAt :: NatVec a t -> Nat -> t
nvAt NvNil _ = __impossible "`nvAt' called with empty Vector"
nvAt (NvCons x xs) Zero     = x
nvAt (NvCons x xs) (Suc s)  = nvAt xs s

tcVecToNatVec :: TcVec t v b -> NatVec v (Maybe (Type t b))
tcVecToNatVec Nil = NvNil
tcVecToNatVec (Cons x xs) = NvCons x (tcVecToNatVec xs)

-- State from the core TC monad
type TcVec t v b = Vec v (Maybe (Type t b))
type NatTcVec t v b = NatVec v (Maybe (Type t b))

data SmtTransState b = SmtTransState {
                                   _vars  :: Map b SVal
                                   , _fresh :: Int
                                   , _target :: Maybe b
                                   }

makeLenses ''SmtTransState

-- Int is the fresh variable count
type SmtStateM b = StateT (SmtTransState b) Symbolic

getSmtExpression :: (Show b, Ord b) => String -> TcVec t v b -> [LExpr t b] -> Type t b -> Type t b -> Symbolic SVal
getSmtExpression dir v e (TRefine t1 p) (TRefine t2 q) = do
  let nv = tcVecToNatVec v
  (e', se) <- runStateT (extract (NvCons Nothing nv) e) (SmtTransState M.empty 0 Nothing) -- we chuck a nothing here so that upshifting makes sense
  (p', sp) <- runStateT (lexprToSmt (NvCons (Just t1) nv) p) se
  (q', sp) <- runStateT (lexprToSmt (NvCons (Just t2) nv) q) sp
  return $ case dir of
    "Subtype"   -> (svOr (svNot (svAnd p' e')) q') -- ~(P ^ E) v Q
    "Supertype" -> (svOr (svNot (svAnd q' e')) p') -- ~(Q ^ E) v P
    -- "Subtype"   -> e' -- ~(P ^ E) v Q
    -- "Supertype"   -> e' -- ~(P ^ E) v Q

-- rename all LVariable (Zero, vn) to LVariable (Zero, "target")
-- alphaRename :: LExpr t b -> LExpr t b
-- alphaRename (LOp opr [a,b]) = LOp opr [alphaRename a, alphaRename b]
-- alphaRename (LOp opr [e]) = LOp opr [alphaRename e]
-- alphaRename (LOp opr es)  = LOp opr $ P.map alphaRename es
-- alphaRename (LVariable (Zero, _)) = LVariable (Zero, "target")
-- alphaRename (LFun fn ts ls) = LFun fn (P.map alphaRenameT ts) ls -- data layout?
-- alphaRename (LApp a b) = LApp (alphaRename a) (alphaRename b)
-- alphaRename (LLet a e1 e2) = LLet a (alphaRename e1) (alphaRename e2) -- care with binding. do we touch it?
-- alphaRename (LLetBang bs a e1 e2) = LLetBang bs a (alphaRename e1) (alphaRename e2) -- care with binding
-- alphaRename (LTuple e1 e2) = LTuple (alphaRename e1) (alphaRename e2)
-- alphaRename (LStruct fs) = LStruct $ P.map (\(n,e) -> (n, alphaRename e)) fs
-- alphaRename (LCon tn e t) = LCon tn (alphaRename e) (alphaRenameT t)
-- alphaRename (LIf c t e) = LIf (alphaRename c) (alphaRename t) (alphaRename e)
-- alphaRename (LCase e tn (v1,a1) (v2,a2)) = LCase (alphaRename e) tn (v1, alphaRename a1) (v2, alphaRename a2)
-- alphaRename (LEsac e) = LEsac (alphaRename e)
-- alphaRename (LSplit (v1,v2) e1 e2) = LSplit (v1,v2) (alphaRename e1) (alphaRename e2)
-- alphaRename (LMember x f) = LMember (alphaRename x) f
-- alphaRename (LTake (a,b) rec f e) = LTake (a,b) rec f (alphaRename e) -- unsure
-- alphaRename (LPut rec f v) = LPut rec f (alphaRename v)
-- alphaRename (LPromote t e) = LPromote (alphaRenameT t) (alphaRename e)
-- alphaRename (LCast t e) = LCast (alphaRenameT t) (alphaRename e)
-- alphaRename x = x

-- alphaRenameT :: Type t b -> Type t b
-- alphaRenameT (TRefine t b) = TRefine t (alphaRename b)
-- alphaRenameT x = x

extract :: (Show b, Ord b) => NatTcVec t v b -> [LExpr t b] -> (SmtStateM b) SVal
extract v ls = do
                  initialSVal <- return $ return svTrue
                  vecPreds <- P.foldr (extractVec v) initialSVal v
                  ctxPreds <- P.foldr (extractLExprs v) initialSVal ls
                  return $ svAnd vecPreds ctxPreds

extractVec :: (Show b, Ord b) => NatTcVec t v b -> Maybe (Type t b) -> (SmtStateM b) SVal -> (SmtStateM b) SVal
extractVec vec t acc = case t of
  Just (TRefine _ p)  -> svAnd <$> acc <*> (lexprToSmt vec p)
  _                   -> acc

extractLExprs :: (Show b, Ord b) => NatTcVec t v b -> LExpr t b -> (SmtStateM b) SVal -> (SmtStateM b) SVal
extractLExprs vec l acc = svAnd <$> acc <*> lexprToSmt vec l

strToPrimInt:: [Char] -> PrimInt
strToPrimInt "U8"  = U8
strToPrimInt "U16" = U16
strToPrimInt "U32" = U32
strToPrimInt "U64" = U64

primIntToSmt :: PrimInt -> SMT.Kind
-- it shouldn't be bool, we do bool case first
-- primIntToSmt Boolean = return KBool
primIntToSmt u
  = let w = if | u == U8  -> 8
               | u == U16 -> 16
               | u == U32 -> 32
               | u == U64 -> 64
               | u == Boolean -> 1 -- fixme
      in KBounded False w

bopToSmt :: Op -> (SVal -> SVal -> SVal)
bopToSmt Plus = svPlus
bopToSmt Minus = svMinus
bopToSmt Times = svTimes
bopToSmt Divide = svDivide
bopToSmt Mod = svRem -- care with the defn, x rem 0 = 0
bopToSmt And = svAnd
bopToSmt Or = svOr 
bopToSmt Gt = svGreaterThan 
bopToSmt Lt = svLessThan
bopToSmt Le = svLessEq
bopToSmt Ge = svGreaterEq
bopToSmt Eq = svEqual
bopToSmt NEq = svNotEqual
bopToSmt BitAnd = svAnd
bopToSmt BitOr = svOr
bopToSmt BitXor = svXOr
bopToSmt LShift = svShiftLeft
bopToSmt RShift = svShiftRight

uopToSmt :: Op -> (SVal -> SVal)
uopToSmt Not = svNot
uopToSmt Complement = svNot

lexprToSmt :: (Show b, Ord b) => NatTcVec t v b -> LExpr t b -> (SmtStateM b) SVal
lexprToSmt vec (LVariable (t, vn)) =
  case t of
    Zero -> do 
            tar <- use target
            newvn <- case tar of
              Nothing   -> do 
                              target <<.= (Just vn) 
                              return vn
              Just name -> return name
            m <- use vars
            case M.lookup newvn m of
              Nothing -> let Just t' = vec `nvAt` t in
                do
                  t'' <- typeToSmt vec t'
                  sv <- mkQSymVar SMT.ALL (show newvn) t''
                  vars %= (M.insert newvn sv)
                  return sv
              Just sv -> return sv
    _  -> do
            m <- use vars
            case M.lookup vn m of
              Nothing -> let Just t' = vec `nvAt` t in
                do
                  t'' <- typeToSmt vec t'
                  sv <- mkQSymVar SMT.ALL (show vn) t''
                  vars %= (M.insert vn sv)
                  return sv
              Just sv -> return sv
-- lexprToSmt (LFun fn ts ls) = LFun fn (map upshiftVarType ts) ls
lexprToSmt vec (LOp op [e]) = (liftA $ uopToSmt op) $ lexprToSmt vec e
lexprToSmt vec (LOp op [e1, e2]) = (liftA2 $ bopToSmt op) (lexprToSmt vec e1) (lexprToSmt vec e2)
-- lexprToSmt (LApp a b) = LApp (upshiftVarLExpr a) (upshiftVarLExpr b)
-- lexprToSmt (LCon tn e t) = LCon tn (upshiftVarLExpr e) (upshiftVarType t)
-- lexprToSmt (LUnit) =
-- lexprToSmt vec (LILit i Boolean)
--   = case i of
--       0 -> return svFalse
--       1 -> return svTrue
lexprToSmt vec (LILit i pt) = 
  return $ case pt of
    U8      -> svInteger (KBounded False 8 ) i
    U16     -> svInteger (KBounded False 16) i
    U32     -> svInteger (KBounded False 32) i
    U64     -> svInteger (KBounded False 64) i
    Boolean -> case i of
      0 -> svFalse
      1 -> svTrue
lexprToSmt vec (LSLit s) = return $ svUninterpreted KString "" Nothing []
-- lexprToSmt (LLet a e1 e2) = LLet a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LLetBang bs a e1 e2) = LLetBang bs a (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LTuple e1 e2) = LTuple (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LStruct fs) = LStruct $ map (\(fn, e) -> (fn, upshiftVarLExpr e)) fs
lexprToSmt vec (LIf c t e) = do
    c' <- lexprToSmt vec c
    t' <- lexprToSmt vec t
    e' <- lexprToSmt vec e
    let thenBranch = svOr (svNot c') t'   -- c => t
        elseBranch = svOr c' e'           -- ~c => e
    return $ svAnd thenBranch elseBranch 
-- lexprToSmt (LCase e tn (v1, a1) (v2, a2)) = LCase (upshiftVarLExpr e) tn (v1, upshiftVarLExpr a1) (v2, upshiftVarLExpr a2)
-- lexprToSmt (LEsac e) = LEsac $ upshiftVarLExpr e
-- lexprToSmt (LSplit (v1, v2) e1 e2) = LSplit (v1, v2) (upshiftVarLExpr e1) (upshiftVarLExpr e2)
-- lexprToSmt (LMember x f) = LMember (upshiftVarLExpr x) f
-- lexprToSmt (LTake (a,b) rec f e) = LTake (a,b) rec f (upshiftVarLExpr e)
-- lexprToSmt (LPut rec f v) = LPut rec f (upshiftVarLExpr v)
-- lexprToSmt (LPromote t e) = LPromote (upshiftVarType t) (upshiftVarLExpr e)
-- lexprToSmt (LCast t e) = LCast (upshiftVarType t) (upshiftVarLExpr e)
lexprToSmt _ _ = freshVal >>= \vn -> return $ svUninterpreted KString vn Nothing []

-- toBaseType :: Type t b -> Type t b
-- toBaseType (TRefine t _) = t
-- toBaseType x = x

-- typeToSmt :: Type t b -> TC t v b (Kind)
-- typeToSmt :: (MonadState (TcState t v b) m, t ~ v) => Type t b -> m (SmtStateM SMT.Kind)
typeToSmt :: NatTcVec t v b -> Type t b -> (SmtStateM b) SMT.Kind
typeToSmt vec (TVar v) = do
    case (vec `nvAt` (finNat v)) of
      Just t' -> typeToSmt vec t'
typeToSmt vec (TVarBang v) = varIndexToSmt vec v
typeToSmt vec (TVarUnboxed v) = varIndexToSmt vec v
typeToSmt vec (TPrim pt) = return $ primIntToSmt pt
-- typeToSmt (TString) = typename "String"
typeToSmt vec (TUnit) = return $ KTuple []
typeToSmt vec (TProduct t1 t2) = do 
  ts <- mapM (typeToSmt vec) [t1, t2]
  return $ KTuple ts
-- typeToSmt (TSum alts) = variant (map (\(n,(t,b)) -> tagname n L.<> prettyTaken b <+> pretty t) alts)
-- typeToSmt (TFun t1 t2) = prettyT' t1 <+> typesymbol "->" <+> pretty t2
-- typeToSmt (TRecord rp fs s) = pretty rp <+> record (map (\(f,(t,b)) -> fieldname f <+> symbol ":" L.<> prettyTaken b <+> pretty t) fs)
typeToSmt vec (TCon "Bool" [] Unboxed) = return $ KBool
typeToSmt vec (TCon "String" [] Unboxed) = return $ KString
typeToSmt vec (TCon n [] Unboxed) = return $ primIntToSmt $ strToPrimInt n
typeToSmt vec (TRefine t _) = typeToSmt vec t
typeToSmt vec t = freshVal >>= \s -> return (KUninterpreted s (Left s)) -- check

varIndexToSmt :: NatTcVec t v b -> Fin t -> (SmtStateM b) SMT.Kind
varIndexToSmt vec i = do
  case (vec `nvAt` (finNat i)) of
    Just t' -> typeToSmt vec t'

smtProveVerbose :: (L.Pretty b, Show b, Ord b) => TcVec t v b -> [LExpr t b] -> Type t b -> Type t b -> IO (Bool, Bool)
smtProveVerbose v ls rt1 rt2 = do
    -- traceTc "infer/smt" (pretty ls)
    dumpMsgIfTrue True (L.text "Running core-tc SMT on types"
                      L.<$> indent' (L.pretty rt1)
                      L.<$> indent' (L.text $ show rt1)
                      L.<$> indent' (L.pretty rt2)
                      L.<$> indent' (L.text $ show rt2)
                      L.<$> L.text "Vec"
                      L.<$> indent' (L.pretty v)
                      L.<$> indent' (L.text $ show v)
                      L.<$> L.text "Context"
                      L.<$> indent' (P.foldr prettyLExprs (L.text "") ls)
                      L.<$> indent' (L.text $ show ls)
                      L.<> L.hardline
                      )
    let toProve1 = getSmtExpression "Subtype" v ls rt1 rt2
        toProve2 = getSmtExpression "Supertype" v ls rt1 rt2
        solver = z3 { -- verbose = __cogent_ddump_smt
                   verbose = True
                   , redirectVerbose = Just $ fromMaybe "/dev/stderr" __cogent_ddump_to_file
                   }
    smtRes1 <- liftIO (proveWith solver toProve1)
    smtRes2 <- liftIO (proveWith solver toProve2)
    -- if its sat, then its not a subtype
    let ret = (not $ modelExists smtRes1, not $ modelExists smtRes2)
    dumpMsgIfTrue True $ L.text (show ret) L.<> L.hardline
    return ret

prettyLExprs :: (L.Pretty b) => LExpr t b -> L.Doc -> L.Doc
prettyLExprs l d = (L.pretty l) L.<$> d

mkQSymVar :: SMT.Quantifier -> String -> SMT.Kind -> (SmtStateM b) SVal
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (Just q) k (Just nm)

freshVal :: (SmtStateM b) String
freshVal = (("smt_val_" ++) . show) <$> (fresh <<%= succ)