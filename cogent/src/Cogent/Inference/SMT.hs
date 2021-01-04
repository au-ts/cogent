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
#if MIN_VERSION_sbv(8,8,0)
import Data.SBV.Internals (VarContext(NonQueryVar))
#endif
import Data.Vec hiding (repeat, splitAt, length, zipWith, zip, unzip)
import Lens.Micro.Mtl
import Lens.Micro.TH
import Prelude as P
import qualified Text.PrettyPrint.ANSI.Leijen as L

tcVecToList :: Int -> TcVec t v b -> [Maybe (Type t b)]
tcVecToList n Nil = []
tcVecToList n (Cons x xs) = case x of
  Just (TRefine t p)  -> (Just (TRefine t (upshiftVarLExpr n p))) : (tcVecToList (n+1) xs)
  t2                  -> t2 : (tcVecToList (n+1) xs)

-- State from the core TC monad
type TcVec t v b = Vec v (Maybe (Type t b))

data SmtTransState b = SmtTransState { _vars  :: Map String SVal
                                     , _fresh :: Int
                                     }

makeLenses ''SmtTransState

-- Int is the fresh variable count
type SmtStateM b = StateT (SmtTransState b) Symbolic

getSmtExpression :: (Show b, Ord b)
                 => [Maybe (Type t b)] -> [LExpr t b] -> Type t b -> Type t b -> Symbolic SVal
getSmtExpression v e (TRefine t1 p) (TRefine t2 q) = do
  (e', se) <- runStateT (extract (Nothing:v) e) (SmtTransState M.empty 0) -- we chuck a nothing here so that upshifting makes sense
  (p', sp) <- runStateT (lexprToSmt ((Just t1):v) p) se
  (q', sp) <- runStateT (lexprToSmt ((Just t2):v) q) sp
  return $ svOr (svNot (svAnd p' e')) q' -- ~(P ^ E) v Q

extract :: (Show b, Ord b) => [Maybe (Type t b)] -> [LExpr t b] -> (SmtStateM b) SVal
extract v ls = do initialSVal <- return $ return svTrue
                  vecPreds <- P.foldr (extractVec v) initialSVal v
                  ctxPreds <- P.foldr (extractLExprs v) initialSVal ls
                  return $ svAnd vecPreds ctxPreds

extractVec :: (Show b, Ord b)
           => [Maybe (Type t b)] -> Maybe (Type t b) -> (SmtStateM b) SVal -> (SmtStateM b) SVal
extractVec vec t acc = case t of
  Just (TRefine _ p)  -> svAnd <$> acc <*> (lexprToSmt vec p)
  _                   -> acc

extractLExprs :: (Show b, Ord b)
              => [Maybe (Type t b)] -> LExpr t b -> (SmtStateM b) SVal -> (SmtStateM b) SVal
extractLExprs vec l acc = svAnd <$> acc <*> lexprToSmt vec l

strToPrimInt :: [Char] -> PrimInt
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

bopToSmt :: Op -> SVal -> SVal -> SVal
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

uopToSmt :: Op -> SVal -> SVal
uopToSmt Not = svNot
uopToSmt Complement = svNot

lexprToSmt :: (Show b, Ord b) => [Maybe (Type t b)] -> LExpr t b -> (SmtStateM b) SVal
lexprToSmt vec (LVariable (t, vn)) = 
  do m <- use vars
     let newn = show t
     case M.lookup newn m of
       Nothing -> let Just t' = vec !! (natToInt t) in
                   do t'' <- typeToSmt vec t'
                      sv <- mkQSymVar SMT.ALL newn t''
                      vars %= (M.insert newn sv)
                      return sv
       Just sv -> return sv

lexprToSmt vec (LOp op [e]) = (liftA $ uopToSmt op) $ lexprToSmt vec e
lexprToSmt vec (LOp op [e1, e2]) =
  (liftA2 $ bopToSmt op) (lexprToSmt vec e1) (lexprToSmt vec e2)
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
lexprToSmt vec (LIf c t e) = do
    c' <- lexprToSmt vec c
    t' <- lexprToSmt vec t
    e' <- lexprToSmt vec e
    let thenBranch = svOr (svNot c') t'   -- c => t
        elseBranch = svOr c' e'           -- ~c => e
    return $ svAnd thenBranch elseBranch 
lexprToSmt _ _ = freshVal >>= \vn -> return $ svUninterpreted KString vn Nothing []

typeToSmt :: [Maybe (Type t b)] -> Type t b -> (SmtStateM b) SMT.Kind
typeToSmt vec (TVar v) = do
    case (vec !! (finInt v)) of
      Just t' -> typeToSmt vec t'
typeToSmt vec (TVarBang v) = varIndexToSmt vec (finInt v)
typeToSmt vec (TVarUnboxed v) = varIndexToSmt vec (finInt v)
typeToSmt vec (TPrim pt) = return $ primIntToSmt pt
typeToSmt vec (TUnit) = return $ KTuple []
typeToSmt vec (TProduct t1 t2) = do 
  ts <- mapM (typeToSmt vec) [t1, t2]
  return $ KTuple ts
typeToSmt vec (TRefine t _) = typeToSmt vec t
#if MIN_VERSION_sbv(8,8,0)
typeToSmt vec t = freshVal >>= \s -> return (KUserSort s (Just [s])) -- check
#else
typeToSmt vec t = freshVal >>= \s -> return (KUninterpreted s (Left s)) -- check
#endif

varIndexToSmt :: [Maybe (Type t b)] -> Int -> (SmtStateM b) SMT.Kind
varIndexToSmt vec i = do
  case (vec !! i) of
    Just t' -> typeToSmt vec t'

smtProve :: (L.Pretty b, Show b, Ord b)
         => TcVec t v b -> [LExpr t b] -> Type t b -> Type t b -> IO Bool
smtProve v ls rt1@(TRefine t1 p1) rt2@(TRefine t2 p2) = do
    -- traceTc "infer/smt" (pretty ls)
    let v' = tcVecToList 1 v
        ls' = P.map (upshiftVarLExpr 1) ls
        toProve = getSmtExpression v' ls' rt1 rt2
        solver = z3 { -- verbose = __cogent_ddump_smt
                   verbose = False
                   , redirectVerbose = Just $ fromMaybe "/dev/stderr" __cogent_ddump_to_file
                   }
    -- ugly dump
    dumpMsgIfTrue False (L.hardline L.<> L.text "Running core-tc SMT on refinement types:"
                      L.<$>              L.text "----------------------------------------"
                      L.<$> indent' (L.pretty rt1)
                      L.<$> indent' (L.pretty rt2)
                      L.<$> L.text "Types in context:"
                      L.<$> indent' (L.pretty v)
                      L.<$> indent' (L.text (show v))
                      L.<$> L.text "Other predicates:"
                      L.<$> indent' (L.pretty ls)
                      L.<$> indent' (L.text (show ls))
                      L.<> L.hardline
                      )
    -- pretty
    dumpMsgIfTrue True (
      L.text "Gamma =" L.<+> (prettyGamma v' ls')
      L.<$> L.text "Gamma" L.<+> L.dullyellow (L.text "|-")
      L.<+> (L.pretty rt1) L.<+> L.dullyellow (L.text "<:") L.<+> (L.pretty rt2)
      -- L.<$> L.text "Gamma: " L.<+> (L.pretty v') L.<+> (L.pretty ls')
      -- L.<$> L.text "extract(Gamma) /\\" L.<+> (L.pretty p1) L.<+> L.text "==>" L.<+> (L.pretty p2) L.<> L.hardline
      L.<$> (prettyProofObligation ((typeListToPreds v') ++ ls') p1 p2) L.<> L.hardline
      )
    smtRes <- liftIO (proveWith solver toProve)
    -- if its sat, then its not a subtype
    let ret = not $ modelExists smtRes
    dumpMsgIfTrue True $ L.text ("Subtyping Result: " ++ show ret) L.<$> L.hardline
    return ret

-- pretty print the context
prettyGamma :: (L.Pretty b) => [Maybe (Type t b)] -> [LExpr t b] -> L.Doc
prettyGamma [] [] = L.empty
prettyGamma [t] [] = L.pretty t
prettyGamma (t:ts) ls = (L.pretty t) L.<> (L.text ",") L.<+> (prettyGamma ts ls)
prettyGamma [] [l] = (L.pretty l)
prettyGamma [] (l:ls) = (L.pretty l) L.<> (L.text ",") L.<+> (prettyGamma [] ls)

typeListToPreds :: [Maybe (Type t b)] -> [LExpr t b]
typeListToPreds [] = []
typeListToPreds (t:ts) = case t of
  Just (TRefine t1 p1)  -> p1:typeListToPreds(ts)
  _                     -> typeListToPreds(ts)

-- extract(Gamma) /\ p1 ==> p2 
prettyProofObligation :: (L.Pretty b) => [LExpr t b] -> LExpr t b -> LExpr t b -> L.Doc
prettyProofObligation [] p1 p2 = (L.pretty p1) L.<+> L.dullyellow (L.text "==>") L.<+> (L.pretty p2)
prettyProofObligation [l] p1 p2 = (L.pretty l) L.<+> L.dullyellow (L.text ("/\\")) L.<+> (prettyProofObligation [] p1 p2)
prettyProofObligation (l:ls) p1 p2 = (L.pretty l) L.<+> L.dullyellow (L.text "/\\") L.<+> (prettyProofObligation ls p1 p2) 

mkQSymVar :: SMT.Quantifier -> String -> SMT.Kind -> (SmtStateM b) SVal
#if MIN_VERSION_sbv(8,8,0)
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just q)) k (Just nm)
#else
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (Just q) k (Just nm)
#endif

freshVal :: (SmtStateM b) String
freshVal = (("smt_val_" ++) . show) <$> (fresh <<%= succ)
