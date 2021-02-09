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
{-# LANGUAGE ViewPatterns #-}

module Cogent.Inference.SMT where

import Cogent.Compiler
import Cogent.Common.Syntax as S
import Cogent.Common.Types
import Cogent.Core
import Cogent.PrettyPrint (indent', warn)
import Cogent.TypeCheck.Util (traceTc)
import Data.Nat
import Data.Fin
import Data.Vec as Vec (length, toList, update, Vec (..))

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State
import Data.IntMap as IM
import Data.Map    as M
import Data.Maybe (catMaybes, fromMaybe)
import Data.SBV as SMT hiding (proveWith)
import Data.SBV.Dynamic as SMT
#if MIN_VERSION_sbv(8,8,0)
import Data.SBV.Internals (VarContext(NonQueryVar))
#endif
import Data.SBV.Internals (SVal(..))
import Data.Vec hiding (repeat, splitAt, length, zipWith, zip, unzip)
import Lens.Micro.GHC
import Lens.Micro.Mtl
import Lens.Micro.TH
import Prelude as P
import qualified Text.PrettyPrint.ANSI.Leijen as L

-- import Debug.Trace
traceM _ = pure ()
trace = flip const


data SmtTransState t b = SmtTransState { _vars    :: [Maybe SVal]
                                       , _ut      :: Map (Type t b) String
                                       , _ue      :: Map (LExpr t b) String
                                       , _fresh   :: Int
                                       }

makeLenses ''SmtTransState

-- Int is the fresh variable count
type SmtStateM t b = StateT (SmtTransState t b) Symbolic

{-
traceX s vec p = do
  m <- use vars
  traceM ("******** extract " ++ s ++ " ****************")
  traceM $ ("st = " ++ show m)
  traceM $ ("vec = " ++ show (L.pretty vec))
  traceM $ ("p = " ++ show (L.pretty p))
-}

-- When extracting the logic predicates from the context and from the subtyping relation
-- as in Γ ⊢ {v : B | p} ⊑ {v : B | q}, we need to line up the indices in Γ and in p and q.
-- For all of them, we use a context B ▸ Γ, and making the indices upshifted, non-telescopic.
-- E.g.
-- +-----+----------+------------+---------+
-- | [0] | [0] == 1 | [0] == [1] | [0] < 2 | (the telescope goes to the right,
-- +-----+----------+------------+---------+  and the context extends to the left)
-- will become:
-- +-----+----------+------------+---------+
-- | [0] | [1] == 1 | [2] == [3] | [3] < 2 |
-- +-----+----------+------------+---------+
-- And the context are always the full context, and doesn't need to be popped when
-- a binder goes out of scope.
--
getSmtExpression :: (L.Pretty b, Show b, Ord b)
                 => Vec v (Maybe (Type t b))
                 -> Vec v [LExpr t b]
                 -> Type t b -> LExpr t b -> LExpr t b -> Symbolic SVal
getSmtExpression tvec pvec β p q = do
  traceM ("@@@@ β = " ++ show (L.pretty β))
  (e',p',q') <- flip evalStateT (SmtTransState (replicate (toInt $ Vec.length tvec) Nothing) M.empty M.empty 0) $ do
    vars %= (Nothing :)
    traceM "==================== Context ============================"
    e' <- P.foldr svAnd svTrue <$> extract tvec pvec
    let tvec' = fmap (fmap toBaseType) $ Vec.toList $ Just β `Cons` tvec
    traceM "==================== type p ============================"
    p' <- lexprToSmt tvec' p
    traceM "==================== type q ============================"
    q' <- lexprToSmt tvec' q
    vars %= P.tail
    return (e',p',q')
  return $ svOr (svNot (svAnd p' e')) q'  -- (E ∧ P) ⟶ Q

extract :: (L.Pretty b, Show b, Ord b)
        => Vec v (Maybe (Type t b)) -> Vec v [LExpr t b] -> SmtStateM t b [SVal]
extract tvec pvec = go 1 ((Nothing :) . Vec.toList $ fmap (fmap toBaseType) tvec)
                       (fmap (fmap upshiftIdxsT) $ Vec.toList tvec)
                       (fmap (fmap $ insertIdxAtLE Zero) $ Vec.toList pvec)
  where 
    go :: (L.Pretty b, Show b, Ord b)
       => Int -> [Maybe (Type t b)] -> [Maybe (Type t b)] -> [[LExpr t b]] -> SmtStateM t b [SVal]
    go _ _ [] [] = return []
    go ι γ (mt:ts) (p:ps) = do
      rest <- go (ι + 1) γ (fmap (fmap upshiftIdxsT) ts) (fmap (fmap $ insertIdxAtLE Zero) ps)
      case (mt,p) of
        (Nothing,[]) -> return rest
        (Just t,ls)  -> do
          mt' <- extractT ι γ t
          ls' <- mapM (lexprToSmt γ) ls
          case mt' of
            Nothing -> pure $ ls' ++ rest
            Just t  -> return $ t : ls' ++ rest
    go _ _ _ _ = __impossible "extract: tvec and pvec are of different lengths"

-- This is irrelevant for now, as we only handle top-level refinment.
-- XXX | It doesn't assume that the vec is normalised. That ι is specifically for that:
-- XXX | when the type is not normalised, say <A {x : U8 | x > 3} | B ()>, then that index
-- XXX | <0> in the refinement is not the <ι>-th in the context, which is the variant type.
-- XXX | But here <0> is that U8.
extractT :: (L.Pretty b, Show b, Ord b)
         => Int -> [Maybe (Type t b)] -> Type t b -> SmtStateM t b (Maybe SVal)
extractT ι vec (TRefine t p) = Just <$> lexprToSmt (vec & ix ι .~ Just t) p
extractT _ _ _ = pure Nothing

primIntToSmt :: PrimInt -> SMT.Kind
primIntToSmt Boolean = KBool
primIntToSmt u
  = let w = if | u == U8  -> 8
               | u == U16 -> 16
               | u == U32 -> 32
               | u == U64 -> 64
               -- | u == Boolean -> 1 -- fixme
      in KBounded False w

bopToSmt :: Op -> SVal -> SVal -> SVal
bopToSmt Plus = svPlus
bopToSmt Minus = svMinus
bopToSmt Times = svTimes
bopToSmt Divide = svDivide
bopToSmt Mod = svRem  -- care with the defn, x rem 0 = 0
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


-- ASSUME: the vec contains only base types.
lexprToSmt :: (L.Pretty b, Show b, Ord b)
           => [Maybe (Type t b)] -> LExpr t b -> SmtStateM t b SVal
lexprToSmt vec (LVariable (natToInt -> v, vn)) = 
  do m <- use vars
     traceM ("#### vec = " ++ show (L.pretty vec))
     case m !! v of
       Nothing -> do n <- freshVal
                     let Just t = vec !! v
                     __assert (isBaseType t) $ "lexprToSmt: vec contains non-base type: " ++ show (L.pretty t)
                     t' <- typeToSmt t
                     sv <- mkQSymVar SMT.ALL n t'
                     vars %= (ix v .~ Just sv)
                     traceM ("**** Generating " ++ show n ++ "; on var " ++ show vn ++ " <" ++ show v ++ ">\n  ... with type " ++ show (L.pretty t))
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
lexprToSmt vec (LSLit s) = return $ SVal KString (Left $ CV KString (CString s))
lexprToSmt vec (LIf c t e) = do
    c' <- lexprToSmt vec c
    t' <- lexprToSmt vec t
    e' <- lexprToSmt vec e
    let thenBranch = svOr (svNot c') t'   -- c => t
        elseBranch = svOr c' e'           -- ~c => e
    return $ svAnd thenBranch elseBranch
-- lexprToSmt vec (LLet a e1 e2) = undefined
lexprToSmt vec e = do
  m <- use ue
  case M.lookup e m of
    Nothing -> do f <- freshVal
                  ue %= (M.insert e f)
                  traceM ("**** Generating " ++ show f ++ "; on expression " ++ show (L.pretty e))
                  return $ svUninterpreted KString f Nothing []  -- FIXME: KString
    Just f  -> return $ svUninterpreted KString f Nothing []   -- FIXME: ditto

typeToSmt :: (L.Pretty b, Show b, Ord b) => Type t b -> SmtStateM t b SMT.Kind
typeToSmt (TPrim pt) = return $ primIntToSmt pt
typeToSmt (TString) = return KString
typeToSmt (TUnit) = return $ KTuple []
typeToSmt (TProduct t1 t2) = KTuple <$> mapM typeToSmt [t1, t2]
typeToSmt (TRefine t _) = typeToSmt t
typeToSmt t = do
  u <- use ut
  case M.lookup t u of
    Nothing -> do s <- freshSort
                  ut %= M.insert t s
#if MIN_VERSION_sbv(8,8,0)
                  return (trace ("@@@@ t = " ++ show (L.pretty t) ++ "\n sort = " ++ show s) $ KUserSort s (Just [s]))
    Just s -> return (KUserSort s (Just [s]))
#else
                  return (KUninterpreted s (Left s))
    Just s -> return (KUninterpreted s (Left s))
#endif

smtProve :: (L.Pretty b, Show b, Ord b)
         => Vec v (Maybe (Type t b))
         -> Vec v [LExpr t b]
         -> Type t b -> LExpr t b -> LExpr t b -> IO Bool
smtProve tvec pvec β p1 p2 = do
    let toProve = getSmtExpression tvec pvec β p1 p2
        solver = z3 { verbose = __cogent_ddump_core_smt
                    , redirectVerbose = Just $ fromMaybe "/dev/stderr" __cogent_ddump_to_file
                    }
    -- pretty
    dumpMsgIfTrue __cogent_ddump_core_smt (
      L.text "Γ =" L.<+> prettyGamma (Just β `Cons` tvec) (Cons [] pvec)
      L.<$> L.text "Γ" L.<+> L.dullyellow (L.text "⊢")
      L.<+> L.pretty p1 L.<+> L.dullyellow (L.text "==>") L.<+> L.pretty p2
      L.<$> L.empty
      )
    smtRes <- liftIO (proveWith solver toProve)
    -- if its sat, then its not a subtype
    let ret = not $ modelExists smtRes
    dumpMsgIfTrue __cogent_ddump_core_smt $ L.text ("Subtyping Result: " ++ show ret) L.<$> L.hardline
    return ret

-- pretty print the context
prettyGamma :: (L.Pretty b) => Vec v (Maybe (Type t b)) -> Vec v [LExpr t b] -> L.Doc
prettyGamma ts ls = L.pretty (fmap prettyMb ts) L.<> L.semi L.<+> L.pretty (fmap L.pretty ls)
  where prettyMb Nothing  = L.text "✗"
        prettyMb (Just t) = L.pretty t


mkQSymVar :: SMT.Quantifier -> String -> SMT.Kind -> SmtStateM t b SVal
#if MIN_VERSION_sbv(8,8,0)
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (NonQueryVar (Just q)) k (Just nm)
#else
mkQSymVar q nm k = symbolicEnv >>= liftIO . svMkSymVar (Just q) k (Just nm)
#endif

freshVal :: SmtStateM t b String
freshVal = (("smt_val_" ++) . show) <$> (fresh <<%= succ)

freshSort :: SmtStateM t b String
freshSort = (("smt_sort_" ++) . show) <$> (fresh <<%= succ)

