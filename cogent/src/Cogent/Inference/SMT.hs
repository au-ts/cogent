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
import Data.Vec as Vec (toList)

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
import Data.Vec hiding (repeat, splitAt, length, zipWith, zip, unzip)
import Lens.Micro.GHC
import Lens.Micro.Mtl
import Lens.Micro.TH
import Prelude as P
import qualified Text.PrettyPrint.ANSI.Leijen as L

-- import Debug.Trace

data SmtTransState t b = SmtTransState { _vars    :: [Maybe SVal]
                                       , _unintrp :: Map (Type t b) String
                                       , _fresh   :: Int
                                       }

makeLenses ''SmtTransState

-- Int is the fresh variable count
type SmtStateM t b = StateT (SmtTransState t b) Symbolic

getSmtExpression :: (Show b, Ord b)
                 => [Maybe (Type t b)]
                 -> [LExpr t b]
                 -> Type t b -> LExpr t b -> LExpr t b -> Symbolic SVal
getSmtExpression vec ls β p q = do
  (e',p',q') <- flip evalStateT (SmtTransState (replicate (length vec) Nothing) M.empty 0) $ do
     e' <- P.foldr svAnd svTrue <$> extract vec ls
     vars %= (Nothing :)
     p' <- lexprToSmt (Just β : vec) p
     vars %= (ix 0 .~ Nothing)
     q' <- lexprToSmt (Just β : vec) q
     vars %= P.tail
     return (e',p',q')
  return $ svOr (svNot (svAnd p' e')) q'  -- (E ∧ P) ⟶ Q

extract :: (Show b, Ord b) => [Maybe (Type t b)] -> [LExpr t b] -> SmtStateM t b [SVal]
extract vec ls = (++) <$> (catMaybes <$> mapM (extractT vec) vec) <*> mapM (extractL vec) ls

extractT :: (Show b, Ord b)
         => [Maybe (Type t b)] -> Maybe (Type t b) -> SmtStateM t b (Maybe SVal)
extractT vec (Just (TRefine t p)) = Just <$> lexprToSmt (Just t : vec) p
extractT _ _ = pure Nothing

extractL :: (Show b, Ord b) => [Maybe (Type t b)] -> LExpr t b -> SmtStateM t b SVal
extractL vec l = lexprToSmt vec l

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

lexprToSmt :: (Show b, Ord b) => [Maybe (Type t b)] -> LExpr t b -> SmtStateM t b SVal
lexprToSmt vec (LVariable (natToInt -> v, vn)) = 
  do m <- use vars
     case m !! v of
       Nothing -> do n <- freshVal
                     let Just t = vec !! v
                     t' <- typeToSmt t
                     sv <- mkQSymVar SMT.ALL n t'
                     vars %= (ix v .~ Just sv)
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
lexprToSmt _ _ = freshVal >>= \vn -> return $ svUninterpreted KString vn Nothing []  -- FIXME: KString

typeToSmt :: (Ord b) => Type t b -> SmtStateM t b SMT.Kind
typeToSmt (TPrim pt) = return $ primIntToSmt pt
typeToSmt (TUnit) = return $ KTuple []
typeToSmt (TProduct t1 t2) = KTuple <$> mapM typeToSmt [t1, t2]
typeToSmt (TRefine t _) = typeToSmt t
typeToSmt t = do
  u <- use unintrp
  case M.lookup t u of
    Nothing -> do s <- freshSort
                  unintrp %= M.insert t s
#if MIN_VERSION_sbv(8,8,0)
                  return (KUserSort s (Just [s]))
    Just s -> return (KUserSort s (Just [s]))
#else
                  return (KUninterpreted s (Left s))
    Just s -> return (KUninterpreted s (Left s))
#endif

smtProve :: (L.Pretty b, Show b, Ord b)
         => Vec v (Maybe (Type t b))
         -> [LExpr t b]
         -> Type t b -> LExpr t b -> LExpr t b -> IO Bool
smtProve (Vec.toList -> vec) ls β p1 p2 = do
    let ls' = P.map (upshiftVarLExpr 1) ls
        toProve = getSmtExpression vec ls' β p1 p2
        solver = z3 { verbose = True
                    , redirectVerbose = Just $ fromMaybe "/dev/stderr" __cogent_ddump_to_file
                    }
    -- pretty
    dumpMsgIfTrue True (
      L.text "Γ =" L.<+> (prettyGamma vec ls')
      L.<$> L.pretty β L.<> L.comma L.<+> L.text "Γ" L.<+> L.dullyellow (L.text "⊢")
      L.<+> (L.pretty p1) L.<+> L.dullyellow (L.text "==>") L.<+> L.pretty p2
      L.<$> L.empty
      )
    smtRes <- liftIO (proveWith solver toProve)
    -- if its sat, then its not a subtype
    let ret = not $ modelExists smtRes
    dumpMsgIfTrue True $ L.text ("Subtyping Result: " ++ show ret) L.<$> L.hardline
    return ret

-- pretty print the context
prettyGamma :: (L.Pretty b) => [Maybe (Type t b)] -> [LExpr t b] -> L.Doc
prettyGamma ts ls = L.list (fmap prettyMb ts) L.<> L.comma L.<+> L.list (fmap L.pretty ls)
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

