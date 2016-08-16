--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{- LANGUAGE FlexibleContexts -}
{- LANGUAGE FlexibleInstances -}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{- LANGUAGE MultiParamTypeClasses -}
{-# LANGUAGE MultiWayIf #-}
{- LANGUAGE OverlappingInstances -}
{- LANGUAGE PackageImports -}
{- LANGUAGE RankNTypes -}
{-# LANGUAGE ScopedTypeVariables #-}
{- LANGUAGE StandaloneDeriving -}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Simplify where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core
import Cogent.Inference hiding (kindcheck, lookupKind, withBinding)
import Cogent.Util (Flip(..), secondM)
import Cogent.Vec as V

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Control.Lens hiding (Context)
import Data.Biapplicative ((<<*>>))
-- import qualified Data.Bifunctor as B
import Data.Function.Flippers
import Data.List as L
import Data.Map as M
import Data.Maybe (catMaybes, fromJust)
import Control.Monad.Extra
import Data.Monoid
import Data.Monoid.Cancellative

-- import Debug.Trace
import Unsafe.Coerce

type InExpr  t v = TypedExpr t v (VarName, OccInfo)
type OutExpr t v = TypedExpr t v VarName

type InVar  = Fin
type OutVar = Fin

type InAlt  t v = InExpr  t v
type OutAlt t v = OutExpr t v

-- ////////////////////////////////////////////////////////////////////////////
-- Occurrence Analyser

type OccEnv v = (FuncEnv, Vec v OccInfo)

emptyOccVec :: SNat v -> Vec v OccInfo
emptyOccVec = flip V.repeat Dead

newtype Occ v a = Occ { unOcc :: State (OccEnv v) a }
                deriving (Functor, Applicative, Monad,
                          MonadState (OccEnv v))

evalOcc :: OccEnv v -> Occ v a -> a
evalOcc = (. unOcc) . flip evalState

execOcc :: OccEnv v -> Occ v a -> OccEnv v
execOcc = (. unOcc) . flip execState

runOcc :: OccEnv v -> Occ v a -> (a, OccEnv v)
runOcc = (. unOcc) . flip runState

parallel :: Occ v a -> Occ v b -> (OccEnv v -> OccEnv v -> OccEnv v) -> Occ v (a, b)
parallel ma mb f = do s <- get
                      a <- ma
                      sa <- get
                      put s
                      b <- mb
                      sb <- get
                      put $ f sa sb
                      return (a, b)

sequential :: SNat v -> Occ v a -> (OccEnv v -> OccEnv v -> OccEnv v) -> Occ v a
sequential v mx f = do s@(fenv,_) <- get
                       put $ (fmap (second $ const Dead) fenv, emptyOccVec v)
                       x <- mx
                       s' <- get
                       put $ f s s'
                       return x

data OccInfo = Dead
             | OnceSafe
             -- | OnceUnsafe
             | MultiSafe
             | MultiUnsafe
             | LetBanged
             deriving (Eq, Ord, Show)

markOcc :: SNat v -> TypedExpr t v VarName -> Occ v (InExpr t v)
markOcc sv (TE tau (Variable (v, n))) = do
  modify $ second $ modifyAt v (OnceSafe <>)
  return . TE tau $ Variable (v, (n, OnceSafe))
markOcc sv (TE tau (Fun fn ts note)) = do
  modify (first $ M.adjust (second $ (OnceSafe <>)) fn)
  return . TE tau $ Fun fn ts note
markOcc sv (TE tau (Op opr es)) = TE tau . Op opr <$> mapM (markOcc sv) es
markOcc sv (TE tau (App f e)) = TE tau <$> (App <$> markOcc sv f <*> markOcc sv e)
markOcc sv (TE tau (Con tag e)) = TE tau <$> (Con tag <$> markOcc sv e)
markOcc sv (TE tau (Unit)) = return $ TE tau Unit
markOcc sv (TE tau (ILit n pt)) = return $ TE tau (ILit n pt)
markOcc sv (TE tau (SLit s)) = return $ TE tau (SLit s)
markOcc sv (TE tau (Let n e1 e2)) = do
  e1' <- markOcc sv e1
  (e2',occ) <- getVOcc1 $ markOcc (SSuc sv) e2
  return $ TE tau $ Let (n,occ) e1' e2'
markOcc sv (TE tau (LetBang bs n e1 e2)) = do
  e1' <- markOcc sv e1
  mapM_ (\(b,_) -> modify . second $ V.modifyAt b (seqOcc LetBanged)) bs  -- !'ed vars cannot be inlined
  (e2',occ) <- getVOcc1 $ markOcc (SSuc sv) e2
  return $ TE tau $ LetBang (L.map (second $ (,OnceSafe)) bs) (n,LetBanged) e1' e2'
markOcc sv (TE tau (Tuple e1 e2)) = TE tau <$> (Tuple <$> markOcc sv e1 <*> markOcc sv e2)
markOcc sv (TE tau (Struct fs)) = TE tau <$> (Struct <$> mapM (secondM $ markOcc sv) fs)
markOcc sv (TE tau (If c th el)) = do
  c' <- markOcc sv c
  (th',el') <- flip (sequential sv) concatEnv $ parallel (markOcc sv th) (markOcc sv el) branchEnv
  return $ TE tau $ If c' th' el'
markOcc sv (TE tau (Case e tag (l1,a1,e1) (l2,a2,e2))) = do
  e' <- markOcc sv e
  ((e1',occ1),(e2',occ2)) <- flip (sequential sv) concatEnv $
                               parallel (getVOcc1 $ markOcc (SSuc sv) e1) (getVOcc1 $ markOcc (SSuc sv) e2) branchEnv
  return $ TE tau $ Case e' tag (l1,(a1,occ1),e1') (l2,(a2,occ2),e2')
markOcc sv (TE tau (Esac e)) = TE tau <$> (Esac <$> markOcc sv e)
markOcc sv (TE tau (Split (n1, n2) e1 e2)) = do
  e1' <- markOcc sv e1
  (e2',occ1,occ2) <- getVOcc2 $ markOcc (SSuc (SSuc sv)) e2
  return $ TE tau $ Split ((n1,occ1), (n2,occ2)) e1' e2'
markOcc sv (TE tau (Member rec fld)) = TE tau <$> (Member <$> markOcc sv rec <*> pure fld)
markOcc sv (TE tau (Take (fn, recn) rec fld e)) = do
  rec' <- markOcc sv rec
  (e',occf,occr) <- getVOcc2 $ markOcc (SSuc (SSuc sv)) e
  return $ TE tau $ Take ((fn,occf), (recn,occr)) rec' fld e'
markOcc sv (TE tau (Put rec fld e)) = TE tau <$> (Put <$> markOcc sv rec <*> pure fld <*> markOcc sv e)
markOcc sv (TE tau (Promote t e)) = TE tau . Promote t <$> markOcc sv e

branchEnv, concatEnv :: OccEnv v -> OccEnv v -> OccEnv v
branchEnv = (<<*>>) . ((branchFuncEnv, V.zipWith parOcc) <<*>>)
concatEnv = (<<*>>) . ((concatFuncEnv, V.zipWith seqOcc) <<*>>)

branchFuncEnv, concatFuncEnv :: FuncEnv -> FuncEnv -> FuncEnv
branchFuncEnv = M.unionWith $ (<<*>>) . ((const, parOcc) <<*>>)
concatFuncEnv = M.unionWith $ (<<*>>) . ((const, seqOcc) <<*>>)

instance Monoid OccInfo where
  mempty = Dead

  mappend x y | x > y = mappend y x
  mappend _ LetBanged   = LetBanged
  mappend Dead        x = x
  mappend OnceSafe    _ = MultiUnsafe
  mappend MultiSafe   _ = MultiUnsafe
  mappend MultiUnsafe _ = MultiUnsafe
  mappend _ _ = __exhaustivity "mappend (in Monoid OccInfo)"

seqOcc, parOcc :: OccInfo -> OccInfo -> OccInfo
seqOcc = (<>)
parOcc OnceSafe OnceSafe = MultiSafe
parOcc occ1 occ2 = occ1 `max` occ2

instance CommutativeMonoid OccInfo

getVOccs :: SNat v' -> Occ (v :+: v') a -> Occ v (a, OccEnv v')
getVOccs v' ma = do (fenv,venv) <- get
                    (a,(fenv',venv')) <- return $ runOcc (fenv,venv <++> emptyOccVec v') ma
                    let (venv1,venv2) = V.splitAt v' venv'
                    put (fenv',venv2)
                    return (a,(fenv',venv1))

getVOcc1 :: Occ ('Suc v) a -> Occ v (a, OccInfo)
getVOcc1 ma = do (a,(_,Cons occ Nil)) <- getVOccs s1 ma
                 return (a,occ)

getVOcc2 :: Occ ('Suc ('Suc v)) a -> Occ v (a, OccInfo, OccInfo)
getVOcc2 ma = do (a,(_,Cons occ1 (Cons occ2 Nil))) <- getVOccs s2 ma
                 return (a,occ1,occ2)

-- ////////////////////////////////////////////////////////////////////////////
-- Top level

type FuncEnv = M.Map FunName (Definition TypedExpr VarName, OccInfo)  -- funcname |-> (def, occ)

data SimpEnv t = SimpEnv { _funcEnv  :: FuncEnv
                         , _kindEnv  :: Vec t Kind
                         , _varCount :: Int
                         }

makeLenses ''SimpEnv

newtype Simp t a = Simp { unSimp :: State (SimpEnv t) a }
                 deriving (Functor, Applicative, Monad,
                           MonadState (SimpEnv t))

evalSimp :: SimpEnv t -> Simp t a -> a
evalSimp = (. unSimp) . flip evalState

execSimp :: SimpEnv t -> Simp t a -> SimpEnv t
execSimp = (. unSimp) . flip execState

runSimp :: SimpEnv t -> Simp t a -> (a, SimpEnv t)
runSimp = (. unSimp) . flip runState

simplify :: [Definition TypedExpr VarName] -> [Definition TypedExpr VarName]
simplify ds = let fenv = fmap (,Dead) . M.fromList . catMaybes $ L.map (\d -> (,d) <$> getFuncId d) ds
               in flip evalState (fenv, 0) $ mapM simplify1 ds

simplify1 :: Definition TypedExpr VarName -> State (FuncEnv, Int) (Definition TypedExpr VarName)
simplify1 (FunDef attr fn tvs ti to e) = do
  fenv <- use _1
  vcnt <- use _2
  (d',env) <- return $ runSimp (SimpEnv fenv (fmap snd tvs) vcnt) (FunDef attr fn tvs ti to <$> simplifyExpr __cogent_fsimplifier_iterations e)
  _1 .= env^.funcEnv
  _1 %= M.adjust (first $ const d') (getDefinitionId d')
  _2 .= env^.varCount
  return d'
simplify1 d = pure d

simplifyExpr :: Int -> TypedExpr t ('Suc 'Zero) VarName -> Simp t (TypedExpr t ('Suc 'Zero) VarName)
simplifyExpr 0 e = pure e
simplifyExpr n e = do fenv <- use funcEnv
                      let (e',(fenv',_)) = runOcc (fenv, emptyOccVec s1) $ markOcc s1 e
                      funcEnv .= fenv'
                      simplifyExpr (n-1) =<< simplExpr s1 (emptySubst s1) (emptyInScopeSet s1) e' Stop

-- ////////////////////////////////////////////////////////////////////////////
-- Simplifier

type Subst  t v    = Subst' t v v  -- in-var -> binding
type Subst' t v v' = Vec v (Maybe (SubstRng t v'))

emptySubst :: SNat v -> Subst t v
emptySubst = flip V.repeat Nothing

data SubstRng t v = DoneEx (OutExpr t v)
                  | SuspEx (InExpr  t v) (Subst t v)
                  deriving (Show)

type InScopeSet  t v    = InScopeSet' t v v  -- out-var -> definition
type InScopeSet' t v v' = Vec v (Maybe (VarDef t v'))

emptyInScopeSet :: SNat v -> InScopeSet t v
emptyInScopeSet = flip V.repeat (Just Unknown)

data VarDef t v = Unknown  -- new var introduced by other continuations that no out-expr is present
                | BoundTo (OutExpr t v) OccInfo
                -- | NotAmong [TagName]
                deriving (Show)

data Context t v = Stop
                 | AppCxt (InExpr t v) (Subst t v) (Context t v)            -- <hole> e
                 | CaseCxt (InVar v) [InAlt t v] (Subst t v) (Context t v)  -- case <hole> of alt1 alt2
                 | ArgCxt (OutExpr t v -> OutExpr t v)                      -- f <hole>
                 | InlineCxt (Context t v)

-- FIXME: basically ignore Context for now, and just do recursion on this function, instead of mutual recursion / zilinc
-- needs a stats as well (IO)
simplExpr :: (v ~ 'Suc v') => SNat v -> Subst t v -> InScopeSet t v -> InExpr t v -> Context t v -> Simp t (OutExpr t v)
simplExpr sv subst ins (TE tau (Variable (v,(n,o)))) cont = case subst `V.at` v of  -- `v' here is an in-var
  Nothing           -> considerInline sv ins (v,n,tau) cont  -- `v' here is an out-var
  Just (SuspEx e s) -> simplExpr sv s ins e cont
  Just (DoneEx e)   -> do fenv <- use funcEnv
                          simplExpr sv (emptySubst sv) ins (evalOcc (fenv, emptyOccVec sv) $ markOcc sv e) cont
-- NOTE: We cannot do anything here. Function inlining has to happen at App (Fun _) _ because lack of lambda / zilinc
simplExpr sv subst ins (TE tau (Fun fn tys note)) cont = return (TE tau (Fun fn tys note))
simplExpr sv subst ins (TE tau (Op opr es)) cont = TE tau . Op opr <$> mapM (flip (simplExpr sv subst ins) cont) es
simplExpr sv subst ins (TE tau (App (TE tau1 (Fun fn tys note)) e2)) cont
  | note `elem` [InlineMe, InlinePlease], ExI (Flip tys') <- V.fromList tys = do
  e2' <- simplExpr sv subst ins e2 cont
  def <- fst . fromJust . M.lookup fn <$> use funcEnv
  case def of
    FunDef attr fn ts ti to fb -> do
      env <- get
      fb' <- return $ evalSimp (SimpEnv (env^.funcEnv) (fmap snd ts) (env^.varCount)) $
               simplExpr s1 (emptySubst s1) (emptyInScopeSet s1) (evalOcc (env^.funcEnv, emptyOccVec s1) $ markOcc s1 fb) Stop
      betaR fb' s0 sv e2' (unsafeCoerce tys')  -- FIXME
    AbsDecl attr fn ts ti to    -> return $ TE tau $ App (TE tau1 (Fun fn tys note)) e2'
    _ -> __impossible "simplExpr"
simplExpr sv subst ins (TE tau (App e1 e2))  cont = TE tau <$> (App <$> simplExpr sv subst ins e1 cont <*> simplExpr sv subst ins e2 cont)
simplExpr sv subst ins (TE tau (Con cn e))   cont = TE tau . Con cn <$> simplExpr sv subst ins e cont
simplExpr sv subst ins (TE tau (Unit))       cont = return . TE tau $ Unit
simplExpr sv subst ins (TE tau (ILit i pt))  cont = return . TE tau $ ILit i pt
simplExpr sv subst ins (TE tau (SLit s))     cont = return . TE tau $ SLit s
simplExpr sv subst ins xx@(TE tau (Let (n,o) e1 e2)) cont = do
  nle1 <- noLinear e1
  if | o == Dead && nle1 -> lowerExpr0 sv <$> simplExpr (SSuc sv) (extSubst subst) (extInScopeSet ins) e2 (liftContext cont)
     -- Pre-inline unconditionally
     | o == OnceSafe -> let subst' = Cons (Just $ SuspEx e1 subst) subst
                        in  lowerExpr0 sv <$> simplExpr (SSuc sv) (liftSubst subst') (extInScopeSet ins) e2 (liftContext cont)
     -- Post-inline unconditionally
     | otherwise -> do
        e1' <- simplExpr sv subst ins e1 cont
        nle1' <- noLinear e1'
        if isTrivial e1' && nle1' && o /= LetBanged
          then let subst' = Cons (Just $ DoneEx e1') subst
               in  lowerExpr0 sv <$> simplExpr (SSuc sv) (liftSubst subst') (extInScopeSet ins) e2 (liftContext cont)
          -- Call-site inline, decided by heuristics
          else let ins' = Cons (Just $ BoundTo e1' o) ins
               in TE tau . Let n e1' <$> simplExpr (SSuc sv) (extSubst subst) (liftInScopeSet ins') e2 (liftContext cont)
simplExpr sv subst ins (TE tau (LetBang vs (n,o) e1 e2)) cont = do
  e1'  <- simplExpr sv subst ins e1 cont
  let ins' = Cons (Just $ BoundTo e1' o) ins
  TE tau . LetBang (L.map (second fst) vs) n e1' <$> simplExpr (SSuc sv) (extSubst subst) (liftInScopeSet ins') e2 (liftContext cont)
simplExpr sv subst ins (TE tau (Tuple e1 e2)) cont = TE tau <$> (Tuple <$> simplExpr sv subst ins e1 cont <*> simplExpr sv subst ins e2 cont)
simplExpr sv subst ins (TE tau (Struct fs)) cont = TE tau . Struct <$> mapM (secondM $ flip (simplExpr sv subst ins) cont) fs
simplExpr sv subst ins (TE tau (If c th el)) cont = do
  c'  <- simplExpr sv subst ins c cont
  th' <- simplExpr sv subst ins th cont
  el' <- simplExpr sv subst ins el cont
  return $ TE tau $ If c' th' el'
simplExpr sv subst ins (TE tau (Case e tn (l1,n1,e1) (l2,n2,e2))) cont = do  -- FIXME
  e'  <- simplExpr sv subst ins e cont
  e1' <- simplExpr (SSuc sv) (extSubst subst) (liftInScopeSet $ Cons (Just Unknown) ins) e1 (liftContext cont)
  e2' <- simplExpr (SSuc sv) (extSubst subst) (liftInScopeSet $ Cons (Just Unknown) ins) e2 (liftContext cont)
  return . TE tau $ Case e' tn (l1,fst n1,e1') (l2,fst n2,e2')
simplExpr sv subst ins (TE tau (Esac e)) cont = TE tau . Esac <$> simplExpr sv subst ins e cont
simplExpr sv subst ins (TE tau (Split nn e1 e2)) cont = do
  e1'  <- simplExpr sv subst ins e1 cont
  let ins' = liftInScopeSet $ Cons (Just Unknown) $ liftInScopeSet $ Cons (Just Unknown) ins
  e2'  <- simplExpr (SSuc (SSuc sv)) (extSubst $ extSubst subst) ins' e2 (liftContext $ liftContext cont)
  return . TE tau $ Split (join (***) fst nn) e1' e2'
simplExpr sv subst ins (TE tau (Member rec fld)) cont = TE tau <$> (Member <$> simplExpr sv subst ins rec cont <*> pure fld)
simplExpr sv subst ins (TE tau (Take nn rec fld e)) cont = do  -- FIXME
  rec' <- simplExpr sv subst ins rec cont
  let ins' = liftInScopeSet $ Cons (Just Unknown) $ liftInScopeSet $ Cons (Just Unknown) ins
  e'   <- simplExpr (SSuc (SSuc sv)) (extSubst $ extSubst subst) ins' e (liftContext $ liftContext cont)
  return . TE tau $ Take (join (***) fst nn) rec' fld e'
simplExpr sv subst ins (TE tau (Put rec fld e)) cont = TE tau <$> (Put <$> simplExpr sv subst ins rec cont <*> pure fld <*> simplExpr sv subst ins e cont)
simplExpr sv subst ins (TE tau (Promote ty e)) cont = TE tau . Promote ty <$> simplExpr sv subst ins e cont

-- Ininlining at occurrence site
considerInline :: (v ~ 'Suc v') => SNat v -> InScopeSet t v -> (OutVar v, VarName, Type t) -> Context t v -> Simp t (OutExpr t v)
considerInline sv ins (v,n,tau) cont = case ins `V.at` v of
  Nothing -> __impossible "considerInline"  -- not in scope
  Just (BoundTo rhs occ) -> do
    ifM (inline rhs occ cont)
      (do fenv <- use funcEnv
          simplExpr sv (emptySubst sv) ins (evalOcc (fenv, emptyOccVec sv) $ markOcc sv rhs) cont)
      (rebuild (TE tau $ Variable (v,n)) cont)
  Just _ -> rebuild (TE tau $ Variable (v,n)) cont

rebuild :: OutExpr t v -> Context t v -> Simp t (OutExpr t v)
rebuild e Stop = return e

-- ////////////////////////////////////////////////////////////////////////////
-- Heuristics

-- NOTE: This function has also to guarantee that linearity is preverved if the expression
--   in question is duplicated / zilinc
isTrivial :: OutExpr t v -> Bool
isTrivial (TE _ (Variable _)) = True  -- If this var is linear, then the binder has to be linear as well
isTrivial (TE _ (Unit)) = True
isTrivial (TE _ (ILit {})) = True
isTrivial (TE _ (SLit {})) = True
isTrivial (TE _ (Fun {})) = __fixme True  -- ???
isTrivial _ = False

inline :: OutExpr t v -> OccInfo -> Context t v -> Simp t Bool
inline rhs OnceSafe _ = __impossible "inline"
-- inline rhs OnceUnsafe cont = noWorkDup rhs && not (veryBoring cont)
inline rhs MultiSafe cont = return $ inlineMulti rhs cont
inline rhs MultiUnsafe cont = andM [pure $ noWorkDup rhs, noLinear rhs, pure $ inlineMulti rhs cont]  -- FIXME: need to check if not let!'ed var / zilinc
inline rhs LetBanged cont = return $ False
inline _ _ _ = __impossible "inline"

-- FIXME: these heuristics are now taking the most conservative decisions

noLinear :: TypedExpr t v a -> Simp t Bool
noLinear (TE tau e) = typeNotLinear tau &&^ noLinear' e
  where
    noLinear' (Variable (v,a)) = return True
    noLinear' (Fun {}) = return True
    noLinear' (Op _ es) = and <$> mapM noLinear es
    noLinear' (App e1 e2) = noLinear e1 &&^ noLinear e2
    noLinear' (Con _ e) = noLinear e
    noLinear' (Unit) = return True
    noLinear' (ILit {}) = return True
    noLinear' (SLit {}) = return True
    noLinear' (Let a e1 e2) = noLinear e1 &&^ noLinear e2
    noLinear' (LetBang _ a e1 e2) = noLinear e1 &&^ noLinear e2
    noLinear' (Tuple e1 e2) = noLinear e1 &&^ noLinear e2
    noLinear' (Struct fs) = and <$> mapM (noLinear . snd) fs
    noLinear' (If e1 e2 e3) = andM [noLinear e1, noLinear e2, noLinear e3]
    noLinear' (Case e _ (_,_,e1) (_,_,e2)) = andM [noLinear e, noLinear e1, noLinear e2]
    noLinear' (Esac e) = noLinear e
    noLinear' (Split a e1 e2) = noLinear e1 &&^ noLinear e2
    noLinear' (Member rec _) = noLinear rec
    noLinear' (Take a rec _ e) = noLinear rec &&^ noLinear e
    noLinear' (Put rec _ e) = noLinear rec &&^ noLinear e
    noLinear' (Promote ty e) = noLinear e

noWorkDup :: OutExpr t v -> Bool
noWorkDup _ = __fixme False

veryBoring :: Context t v -> Bool
veryBoring _ = __fixme True

inlineMulti :: OutExpr t v -> Context t v -> Bool
inlineMulti rhs cont | noSizeIncrease rhs cont = True
                     | boring rhs cont = False
                     | otherwise = smallEnough rhs cont

noSizeIncrease :: OutExpr t v -> Context t v -> Bool
noSizeIncrease _ _ = __fixme False

boring :: OutExpr t v -> Context t v -> Bool
boring _ _ = __fixme True

smallEnough :: OutExpr t v -> Context t v -> Bool
smallEnough _ _ = __fixme False

-- ////////////////////////////////////////////////////////////////////////////
-- misc.

lowerExpr0 :: (Show a, v ~ 'Suc v') => SNat v -> TypedExpr t ('Suc v) a -> TypedExpr t v a
lowerExpr0 v = lowerExpr v f0

-- lowerFin (|var|-1) idx var: if var < idx, then var; otherwise var - 1 (idx /= var)
lowerFin :: (v ~ 'Suc v') => SNat v -> Fin ('Suc v) -> Fin ('Suc v) -> Fin v
lowerFin _ FZero FZero = __impossible "lowerFin"
lowerFin _ FZero (FSuc v) = v
lowerFin _ (FSuc i) FZero = FZero
lowerFin (SSuc SZero) (FSuc FZero) (FSuc FZero) = __impossible "lowerFin"
lowerFin (SSuc (SSuc n)) (FSuc i) (FSuc v) = FSuc $ lowerFin (SSuc n) i v
#if __GLASGOW_HASKELL__ < 711
lowerFin _ _ _ = __ghc_t4139 "lowerFin"
#endif
lowerExpr :: (Show a, v ~ 'Suc v') => SNat v -> Fin ('Suc v) -> TypedExpr t ('Suc v) a -> TypedExpr t v a
lowerExpr w i (TE tau (Variable (v,a)))     = TE tau $ Variable (lowerFin w i v, a)
lowerExpr w i (TE tau (Fun fn tys  note))   = TE tau $ Fun fn tys note
lowerExpr w i (TE tau (Op opr es))          = TE tau $ Op opr (L.map (lowerExpr w i) es)
lowerExpr w i (TE tau (App e1 e2))          = TE tau $ App (lowerExpr w i e1) (lowerExpr w i e2)
lowerExpr w i (TE tau (Con cn e))           = TE tau $ Con cn (lowerExpr w i e)
lowerExpr w i (TE tau (Unit))               = TE tau $ Unit
lowerExpr w i (TE tau (ILit n pt))          = TE tau $ ILit n pt
lowerExpr w i (TE tau (SLit s))             = TE tau $ SLit s
lowerExpr w i (TE tau (Let a e1 e2))        = TE tau $ Let a (lowerExpr w i e1) (lowerExpr (SSuc w) (FSuc i) e2)
lowerExpr w i (TE tau (LetBang vs a e1 e2)) = TE tau $ LetBang (L.map (first $ lowerFin w i) vs) a (lowerExpr w i e1) (lowerExpr (SSuc w) (FSuc i) e2)
lowerExpr w i (TE tau (Tuple e1 e2))        = TE tau $ Tuple (lowerExpr w i e1) (lowerExpr w i e2)
lowerExpr w i (TE tau (Struct fs))          = TE tau $ Struct (L.map (second $ lowerExpr w i) fs)
lowerExpr w i (TE tau (If e1 e2 e3))        = TE tau $ If (lowerExpr w i e1) (lowerExpr w i e2) (lowerExpr w i e3)
lowerExpr w i (TE tau (Case e tn (l1,a1,e1) (l2,a2,e2))) = TE tau $ Case (lowerExpr w i e) tn (l1, a1, lowerExpr (SSuc w) (FSuc i) e1) (l2, a2, lowerExpr (SSuc w) (FSuc i) e2)
lowerExpr w i (TE tau (Esac e))             = TE tau $ Esac (lowerExpr w i e)
lowerExpr w i (TE tau (Split a e1 e2))      = TE tau $ Split a (lowerExpr w i e1) (lowerExpr (SSuc (SSuc w)) (FSuc (FSuc i)) e2)
lowerExpr w i (TE tau (Member rec fld))     = TE tau $ Member (lowerExpr w i rec) fld
lowerExpr w i (TE tau (Take a rec fld e))   = TE tau $ Take a (lowerExpr w i rec) fld (lowerExpr (SSuc (SSuc w)) (FSuc (FSuc i)) e)
lowerExpr w i (TE tau (Put rec fld e))      = TE tau $ Put (lowerExpr w i rec) fld (lowerExpr w i e)
lowerExpr w i (TE tau (Promote ty e))       = TE tau $ Promote ty (lowerExpr w i e)

liftExpr :: Show a => Fin ('Suc v) -> TypedExpr t v a -> TypedExpr t ('Suc v) a
liftExpr i (TE tau (Variable (v,a)))     = TE tau $ Variable (liftIdx i v,a)
liftExpr i (TE tau (Fun fn tys note))    = TE tau $ Fun fn tys note
liftExpr i (TE tau (Op opr es))          = TE tau $ Op opr (L.map (liftExpr i) es)
liftExpr i (TE tau (App e1 e2))          = TE tau $ App (liftExpr i e1) (liftExpr i e2)
liftExpr i (TE tau (Con cn e))           = TE tau $ Con cn (liftExpr i e)
liftExpr i (TE tau (Unit))               = TE tau $ Unit
liftExpr i (TE tau (ILit n pt))          = TE tau $ ILit n pt
liftExpr i (TE tau (SLit s))             = TE tau $ SLit s
liftExpr i (TE tau (Let a e1 e2))        = TE tau $ Let a (liftExpr i e1) (liftExpr (FSuc i) e2)
liftExpr i (TE tau (LetBang vs a e1 e2)) = TE tau $ LetBang (L.map (first $ liftIdx i) vs) a (liftExpr i e1) (liftExpr (FSuc i) e2)
liftExpr i (TE tau (Tuple e1 e2))        = TE tau $ Tuple (liftExpr i e1) (liftExpr i e2)
liftExpr i (TE tau (Struct fs))          = TE tau $ Struct (L.map (second $ liftExpr i) fs)
liftExpr i (TE tau (If e1 e2 e3))        = TE tau $ If (liftExpr i e1) (liftExpr i e2) (liftExpr i e3)
liftExpr i (TE tau (Case e tn (l1,a1,e1) (l2,a2,e2))) = TE tau $ Case (liftExpr i e) tn (l1, a1, liftExpr (FSuc i) e1) (l2, a2, liftExpr (FSuc i) e2)
liftExpr i (TE tau (Esac e))             = TE tau $ Esac (liftExpr i e)
liftExpr i (TE tau (Split a e1 e2))      = TE tau $ Split a (liftExpr i e1) (liftExpr (FSuc $ FSuc i) e2)
liftExpr i (TE tau (Member rec fld))     = TE tau $ Member (liftExpr i rec) fld
liftExpr i (TE tau (Take a rec fld e))   = TE tau $ Take a (liftExpr i rec) fld (liftExpr (FSuc $ FSuc i) e)
liftExpr i (TE tau (Put rec fld e))      = TE tau $ Put (liftExpr i rec) fld (liftExpr i e)
liftExpr i (TE tau (Promote ty e))       = TE tau $ Promote ty (liftExpr i e)

upshiftExpr :: Show a => SNat n -> SNat v -> Fin ('Suc v) -> TypedExpr t v a -> TypedExpr t (v :+: n) a
upshiftExpr SZero _ v e = e
upshiftExpr (SSuc n) sv v e | Refl <- addSucLeft sv n
  = let a = upshiftExpr n sv v e in liftExpr (widenN v n) a

extSubst :: Subst t v -> Subst t ('Suc v)
extSubst s = Cons Nothing (fmap (fmap liftSubstRng) s)

liftSubst :: Subst' t ('Suc v) v -> Subst t ('Suc v)
liftSubst = fmap $ fmap liftSubstRng

liftSubstRng :: SubstRng t v -> SubstRng t ('Suc v)
liftSubstRng (DoneEx e  ) = DoneEx (liftExpr f0 e)
liftSubstRng (SuspEx e s) = SuspEx (liftExpr f0 e) (extSubst s)

extInScopeSet :: InScopeSet t v -> InScopeSet t ('Suc v)
extInScopeSet s = Cons Nothing (fmap (fmap liftVarDef) s)

liftInScopeSet :: InScopeSet' t ('Suc v) v -> InScopeSet t ('Suc v)
liftInScopeSet = fmap $ fmap liftVarDef

liftVarDef :: VarDef t v -> VarDef t ('Suc v)
liftVarDef (Unknown) = Unknown
liftVarDef (BoundTo e occ) = BoundTo (liftExpr f0 e) occ
-- liftVarDef (NotAmong tags) = NotAmong tags

liftContext :: Context t v -> Context t ('Suc v)
liftContext Stop = Stop

-- substFin var (|var_body|-1==idx) |var_arg| arg
-- It performs substitution [var |-> arg], the substituted variable must be the one of largest index.
-- Returned env is constituted by `init (var_body) ++ var_arg'
substFin :: Fin ('Suc v') -> SNat v' -> SNat v -> TypedExpr t v VarName -> Either (Fin (v :+: v')) (TypedExpr t (v :+: v') VarName)
substFin FZero SZero _ arg = Right arg
substFin FZero (SSuc _) _ _ = Left FZero
substFin (FSuc _) SZero _ _ = __impossible "substFin"  -- idx must be the largest var
substFin (FSuc v) (SSuc n') n arg = case substFin v n' n arg of
  Left v' -> Left  $ FSuc v'
  Right e -> Right $ liftExpr f0 e

-- betaR body (|var_body|-1==idx) |var_arg| arg ts
betaR :: (v ~ 'Suc v0) => TypedExpr t' ('Suc v') VarName -> SNat v' -> SNat v -> TypedExpr t v VarName -> Vec t' (Type t) -> Simp t (TypedExpr t (v :+: v') VarName)
betaR (TE tau (Variable (v,a)))  idx n arg ts
  = case substFin v idx n arg of
      Left v' -> pure $ TE (substitute ts tau) $ Variable (v',a)
      Right e -> pure e
betaR (TE tau (Fun fn tys note)) idx n arg ts = pure . TE (substitute ts tau) $ Fun fn (L.map (substitute ts) tys) note
betaR (TE tau (Op opr es))       idx n arg ts = TE (substitute ts tau) <$> (Op opr <$> mapM (flip5 betaR ts arg n idx) es)
betaR (TE tau (App e1 e2))       idx n arg ts = TE (substitute ts tau) <$> (App <$> betaR e1 idx n arg ts <*> betaR e2 idx n arg ts)
betaR (TE tau (Con cn e))        idx n arg ts = TE (substitute ts tau) <$> (Con cn <$> betaR e idx n arg ts)
betaR (TE tau (Unit))            idx n arg ts = pure . TE (substitute ts tau) $ Unit
betaR (TE tau (ILit i pt))       idx n arg ts = pure . TE (substitute ts tau) $ ILit i pt
betaR (TE tau (SLit s))          idx n arg ts = pure . TE (substitute ts tau) $ SLit s
betaR (TE tau (Let a e1 e2))     idx n arg ts = TE (substitute ts tau) <$> (Let a <$> betaR e1 idx n arg ts <*> betaR e2 (SSuc idx) n arg ts)
betaR e@(TE tau (LetBang vs a e1 e2)) idx n@(SSuc n0) arg ts
  | (maxFin idx) `elem` (L.map fst vs) = do  -- NOTE: arg is in the let!'ed set, which means it hasn't been used and is safe to be lifted out / zilinc
  -- XXX | (\x -> let e1 !vs e2) arg ===> let x' = arg in (\x -> let e1 !vs e2) x' ===> let x' = arg in (let e1[x'/x] !vs[x'/x] in e2[x'/x])
      vc <- use varCount
      varCount += 1
      let vn = "simp_var_" ++ show vc
      case sym (addSucLeft n idx) of
        Refl -> do varg  <- pure $ TE (exprType arg) (Variable (f0,vn))
                   arg'  <- pure $ upshiftExpr idx n f0 arg
                   body' <- betaR e idx (SSuc n) varg ts
                   return $ TE (substitute ts tau) $ (Let vn arg' body')
  | Refl <- sym (addSucLeft' n idx) = TE (substitute ts tau) <$> (LetBang (L.map (first $ flip widenN n0) vs) a <$> betaR e1 idx n arg ts <*> betaR e2 (SSuc idx) n arg ts)
betaR (TE tau (Tuple e1 e2)) idx n arg ts = TE (substitute ts tau) <$> (Tuple <$> betaR e1 idx n arg ts <*> betaR e2 idx n arg ts)
betaR (TE tau (Struct fs))   idx n arg ts = TE (substitute ts tau) <$> (Struct <$> mapM (secondM $ flip5 betaR ts arg n idx) fs)
betaR (TE tau (If e1 e2 e3)) idx n arg ts = TE (substitute ts tau) <$> (If <$> betaR e1 idx n arg ts <*> betaR e2 idx n arg ts <*> betaR e3 idx n arg ts)
betaR (TE tau (Case e tn (l1,a1,e1) (l2,a2,e2))) idx n arg ts = do
  e'  <- betaR e  idx n arg ts
  e1' <- betaR e1 (SSuc idx) n arg ts
  e2' <- betaR e2 (SSuc idx) n arg ts
  pure . TE (substitute ts tau) $ Case e' tn (l1, a1, e1') (l2, a2, e2')
betaR (TE tau (Esac e))           idx n arg ts = TE (substitute ts tau) <$> (Esac <$> betaR e idx n arg ts)
betaR (TE tau (Split a e1 e2))    idx n arg ts = TE (substitute ts tau) <$> (Split a <$> betaR e1 idx n arg ts <*> betaR e2 (SSuc (SSuc idx)) n arg ts)
betaR (TE tau (Member rec fld))   idx n arg ts = TE (substitute ts tau) <$> (Member <$> betaR rec idx n arg ts <*> pure fld)
betaR (TE tau (Take a rec fld e)) idx n arg ts = TE (substitute ts tau) <$> (Take a <$> betaR rec idx n arg ts <*> pure fld <*> betaR e (SSuc (SSuc idx)) n arg ts)
betaR (TE tau (Put rec fld e))    idx n arg ts = TE (substitute ts tau) <$> (Put <$> betaR rec idx n arg ts <*> pure fld <*> betaR e idx n arg ts)
betaR (TE tau (Promote ty e))     idx n arg ts = TE (substitute ts tau) <$> (Promote (substitute ts ty) <$> betaR e idx n arg ts)
#if __GLASGOW_HASKELL__ < 711
betaR _ _ _ _ _ = __ghc_t4139 "betaR"
#endif

lookupKind :: Fin t -> Simp t Kind
lookupKind f = (`V.at` f) <$> use kindEnv

kindcheck :: Type t -> Simp t Kind
kindcheck (TVar v)         = lookupKind v
kindcheck (TVarBang v)     = bangKind <$> lookupKind v
kindcheck (TUnit)          = return mempty
kindcheck (TProduct t1 t2) = mappend <$> kindcheck t1 <*> kindcheck t2
kindcheck (TSum ts)        = mconcat <$> (mapM (kindcheck . fst . snd) ts)
kindcheck (TFun ti to)     = return mempty
kindcheck (TRecord ts s)   = mappend (sigilKind s) <$> (mconcat <$> (mapM (kindcheck . fst . snd) (L.filter (not . snd .snd) ts)))
kindcheck (TPrim i)        = return mempty
kindcheck (TString)        = return mempty
kindcheck (TCon n vs s)    = mapM_ kindcheck vs >> return (sigilKind s)

typeNotLinear :: Type t -> Simp t Bool
typeNotLinear t = kindcheck t >>= \k -> return (canDiscard k && canShare k)  -- NOTE: depending on definition of linear types, judgement may change / zilinc
