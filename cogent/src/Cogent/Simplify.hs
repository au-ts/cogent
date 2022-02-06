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
import Cogent.Util (Flip(..), secondM, ifM, flip3, andM)
import Data.Ex
import Data.Fin
import Data.Nat
import Data.PropEq
import Data.Vec as V

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Control.Arrow
import Control.Monad
import Control.Monad.State
import Data.List as L
import Data.Map as M
import Data.Maybe (catMaybes, fromJust)
import Data.Monoid
import Lens.Micro.Mtl
import Lens.Micro
import Lens.Micro.TH
-- import Debug.Trace
import Unsafe.Coerce

type InExpr  t v b = PosTypedExpr t v (VarName, OccInfo) b
type OutExpr t v b = PosTypedExpr t v VarName            b

type InVar  = Fin
type OutVar = Fin

type InAlt  t v b = InExpr  t v b
type OutAlt t v b = OutExpr t v b

-- ////////////////////////////////////////////////////////////////////////////
-- Occurrence Analyser

type OccEnv v b = (FuncEnv b, Vec v OccInfo)

emptyOccVec :: SNat v -> Vec v OccInfo
emptyOccVec = flip V.repeat Dead

newtype Occ v b x = Occ { unOcc :: State (OccEnv v b) x }
                  deriving (Functor, Applicative, Monad,
                            MonadState (OccEnv v b))

#if MIN_VERSION_base(4,13,0)
instance MonadFail (Occ v b) where
  fail = __impossible
#endif

evalOcc :: OccEnv v b -> Occ v b x -> x
evalOcc = (. unOcc) . flip evalState

execOcc :: OccEnv v b -> Occ v b x -> OccEnv v b
execOcc = (. unOcc) . flip execState

runOcc :: OccEnv v b -> Occ v b x -> (x, OccEnv v b)
runOcc = (. unOcc) . flip runState

parallel :: Occ v b x -> Occ v b y -> (OccEnv v b -> OccEnv v b -> OccEnv v b) -> Occ v b (x, y)
parallel ma mb f = do s <- get
                      a <- ma
                      sa <- get
                      put s
                      b <- mb
                      sb <- get
                      put $ f sa sb
                      return (a, b)

sequential :: SNat v -> Occ v b x -> (OccEnv v b -> OccEnv v b -> OccEnv v b) -> Occ v b x
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

markOcc :: SNat v -> PosTypedExpr t v VarName b -> Occ v b (InExpr t v b)
markOcc sv (TE tau (Variable (v, n) loc)) = do
  modify $ second $ modifyAt v (OnceSafe <>)
  return . TE tau $ Variable (v, (n, OnceSafe)) loc
markOcc sv (TE tau (Fun fn ts ls note loc)) = do
  modify (first $ M.adjust (second $ (OnceSafe <>)) (unCoreFunName fn))
  return . TE tau $ Fun fn ts ls note loc
markOcc sv (TE tau (Op opr es)) = TE tau . Op opr <$> mapM (markOcc sv) es
markOcc sv (TE tau (App f e)) = TE tau <$> (App <$> markOcc sv f <*> markOcc sv e)
markOcc sv (TE tau (Con tag e t)) = TE tau <$> (Con tag <$> markOcc sv e <*> pure t)
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
markOcc sv (TE tau (Cast t e)) = TE tau . Cast t <$> markOcc sv e

branchEnv, concatEnv :: OccEnv v b -> OccEnv v b -> OccEnv v b
branchEnv (fe, v) (fe', v') = (branchFuncEnv fe fe', V.zipWith parOcc v v')
concatEnv (fe, v) (fe', v') = (concatFuncEnv fe fe', V.zipWith seqOcc v v')

branchFuncEnv, concatFuncEnv :: FuncEnv b -> FuncEnv b -> FuncEnv b
branchFuncEnv = M.unionWith $ \(a,b) (_,d) -> (a, parOcc b d)
concatFuncEnv = M.unionWith $ \(a,b) (_,d) -> (a, seqOcc b d)

#if __GLASGOW_HASKELL__ < 803
instance Monoid OccInfo where
  mempty = Dead

  mappend x y | x > y = mappend y x
  mappend _ LetBanged   = LetBanged
  mappend Dead        x = x
  mappend OnceSafe    _ = MultiUnsafe
  mappend MultiSafe   _ = MultiUnsafe
  mappend MultiUnsafe _ = MultiUnsafe
  mappend _ _ = __exhaustivity "mappend (in Monoid OccInfo)"
#else
instance Semigroup OccInfo where
  (<>) x y | x > y = y <> x
  (<>) _ LetBanged   = LetBanged
  (<>) Dead        x = x
  (<>) OnceSafe    _ = MultiUnsafe
  (<>) MultiSafe   _ = MultiUnsafe
  (<>) MultiUnsafe _ = MultiUnsafe
  (<>) _ _ = __exhaustivity "mappend (in Monoid OccInfo)"
instance Monoid OccInfo where
  mempty = Dead
#endif

seqOcc, parOcc :: OccInfo -> OccInfo -> OccInfo
seqOcc = (<>)
parOcc OnceSafe OnceSafe = MultiSafe
parOcc occ1 occ2 = occ1 `max` occ2

getVOccs :: SNat v' -> Occ (v :+: v') b x -> Occ v b (x, OccEnv v' b)
getVOccs v' ma = do (fenv,venv) <- get
                    (a,(fenv',venv')) <- return $ runOcc (fenv,venv <++> emptyOccVec v') ma
                    let (venv1,venv2) = V.splitAt v' venv'
                    put (fenv',venv2)
                    return (a,(fenv',venv1))

getVOcc1 :: Occ ('Suc v) b x -> Occ v b (x, OccInfo)
getVOcc1 ma = do (a,(_,Cons occ Nil)) <- getVOccs s1 ma
                 return (a,occ)

getVOcc2 :: Occ ('Suc ('Suc v)) b x -> Occ v b (x, OccInfo, OccInfo)
getVOcc2 ma = do (a,(_,Cons occ1 (Cons occ2 Nil))) <- getVOccs s2 ma
                 return (a,occ1,occ2)

-- ////////////////////////////////////////////////////////////////////////////
-- Top level

type FuncEnv b = M.Map FunName (Definition PosTypedExpr VarName b, OccInfo)  -- funcname |-> (def, occ)

data SimpEnv t b = SimpEnv { _funcEnv  :: FuncEnv b
                           , _kindEnv  :: Vec t Kind
                           , _varCount :: Int
                           }

makeLenses ''SimpEnv

newtype Simp t b x = Simp { unSimp :: State (SimpEnv t b) x }
                   deriving (Functor, Applicative, Monad,
                             MonadState (SimpEnv t b))

evalSimp :: SimpEnv t b -> Simp t b x -> x
evalSimp = (. unSimp) . flip evalState

execSimp :: SimpEnv t b -> Simp t b x -> SimpEnv t b
execSimp = (. unSimp) . flip execState

runSimp :: SimpEnv t b -> Simp t b x -> (x, SimpEnv t b)
runSimp = (. unSimp) . flip runState

simplify :: [Definition PosTypedExpr VarName b] -> [Definition PosTypedExpr VarName b]
simplify ds = let fenv = fmap (,Dead) . M.fromList . catMaybes $ L.map (\d -> (,d) <$> getFuncId d) ds
               in flip evalState (fenv, 0) $ mapM simplify1 ds

simplify1 :: Definition PosTypedExpr VarName b -> State (FuncEnv b, Int) (Definition PosTypedExpr VarName b)
simplify1 (FunDef attr fn tvs lvs ti to e) = do
  fenv <- use _1
  vcnt <- use _2
  (d',env) <- return $ runSimp (SimpEnv fenv (fmap snd tvs) vcnt) (FunDef attr fn tvs lvs ti to <$> simplifyExpr __cogent_fsimplifier_iterations e)
  _1 .= env^.funcEnv
  _1 %= M.adjust (first $ const d') (getDefinitionId d')
  _2 .= env^.varCount
  return d'
simplify1 d = pure d

simplifyExpr :: Int -> PosTypedExpr t ('Suc 'Zero) VarName b -> Simp t b (PosTypedExpr t ('Suc 'Zero) VarName b)
simplifyExpr 0 e = pure e
simplifyExpr n e = do fenv <- use funcEnv
                      let (e',(fenv',_)) = runOcc (fenv, emptyOccVec s1) $ markOcc s1 e
                      funcEnv .= fenv'
                      simplifyExpr (n-1) =<< simplExpr s1 (emptySubst s1) (emptyInScopeSet s1) e' Stop

-- ////////////////////////////////////////////////////////////////////////////
-- Simplifier

type Subst  t v    b = Subst' t v v b  -- in-var -> binding
type Subst' t v v' b = Vec v (Maybe (SubstRng t v' b))

emptySubst :: SNat v -> Subst t v b
emptySubst = flip V.repeat Nothing

data SubstRng t v b = DoneEx (OutExpr t v b)
                    | SuspEx (InExpr  t v b) (Subst t v b)
                    deriving (Show)

type InScopeSet  t v    b = InScopeSet' t v v b  -- out-var -> definition
type InScopeSet' t v v' b = Vec v (Maybe (VarDef t v' b))

emptyInScopeSet :: SNat v -> InScopeSet t v b
emptyInScopeSet = flip V.repeat (Just Unknown)

data VarDef t v b = Unknown  -- new var introduced by other continuations that no out-expr is present
                  | BoundTo (OutExpr t v b) OccInfo
                  -- \| NotAmong [TagName]
                  deriving (Show)

data Context t v b = Stop
                   | AppCxt (InExpr t v b) (Subst t v b) (Context t v b)            -- <hole> e
                   | CaseCxt (InVar v) [InAlt t v b] (Subst t v b) (Context t v b)  -- case <hole> of alt1 alt2
                   | ArgCxt (OutExpr t v b -> OutExpr t v b)                        -- f <hole>
                   | InlineCxt (Context t v b)

-- FIXME: basically ignore Context for now, and just do recursion on this function, instead of mutual recursion / zilinc
-- needs a stats as well (IO)
simplExpr :: (v ~ 'Suc v') => SNat v -> Subst t v b -> InScopeSet t v b -> InExpr t v b -> Context t v b -> Simp t b (OutExpr t v b)
simplExpr sv subst ins (TE tau (Variable (v,(n,o)) loc)) cont = case subst `V.at` v of  -- `v' here is an in-var
  Nothing           -> considerInline sv ins (v,n,tau) cont  -- `v' here is an out-var
  Just (SuspEx e s) -> simplExpr sv s ins e cont
  Just (DoneEx e)   -> do fenv <- use funcEnv
                          simplExpr sv (emptySubst sv) ins (evalOcc (fenv, emptyOccVec sv) $ markOcc sv e) cont
-- NOTE: We cannot do anything here. Function inlining has to happen at App (Fun _) _ because lack of lambda / zilinc
simplExpr sv subst ins (TE tau (Fun fn ts ls note loc)) cont = return (TE tau (Fun fn ts ls note loc))
simplExpr sv subst ins (TE tau (Op opr es)) cont = TE tau . Op opr <$> mapM (flip (simplExpr sv subst ins) cont) es
simplExpr sv subst ins (TE tau (App (TE tau1 (Fun fn tys lvs note loc)) e2)) cont
  | note `elem` [InlineMe, InlinePlease], ExI (Flip tys') <- V.fromList tys = do
  e2' <- simplExpr sv subst ins e2 cont
  def <- fst . fromJust . M.lookup (unCoreFunName fn) <$> use funcEnv
  case def of
    FunDef attr fn ts ls ti to fb -> do
      env <- get
      fb' <- return $ evalSimp (SimpEnv (env^.funcEnv) (fmap snd ts) (env^.varCount)) $
               simplExpr s1 (emptySubst s1) (emptyInScopeSet s1) (evalOcc (env^.funcEnv, emptyOccVec s1) $ markOcc s1 fb) Stop
      betaR fb' s0 sv e2' (unsafeCoerce tys')  -- FIXME
    AbsDecl attr fn ts ls ti to    -> return $ TE tau $ App (TE tau1 (Fun (unsafeCoreFunName fn) tys lvs note loc)) e2'  -- FIXME
    _ -> __impossible "simplExpr"
simplExpr sv subst ins (TE tau (App e1 e2))  cont = TE tau <$> (App <$> simplExpr sv subst ins e1 cont <*> simplExpr sv subst ins e2 cont)
simplExpr sv subst ins (TE tau (Con cn e t)) cont = TE tau <$> (Con cn <$> simplExpr sv subst ins e cont <*> pure t)
simplExpr sv subst ins (TE tau (Unit))       cont = return . TE tau $ Unit
simplExpr sv subst ins (TE tau (ILit i pt))  cont = return . TE tau $ ILit i pt
simplExpr sv subst ins (TE tau (SLit s))     cont = return . TE tau $ SLit s
simplExpr sv subst ins (TE tau (Let (n,o) e1 e2)) cont = do
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
simplExpr sv subst ins (TE tau (Cast ty e)) cont = TE tau . Cast ty <$> simplExpr sv subst ins e cont

-- Ininlining at occurrence site
considerInline :: (v ~ 'Suc v') => SNat v -> InScopeSet t v b -> (OutVar v, VarName, Type t b) -> Context t v b -> Simp t b (OutExpr t v b)
considerInline sv ins (v,n,tau) cont = case ins `V.at` v of
  Nothing -> __impossible "considerInline"  -- not in scope
  Just (BoundTo rhs occ) -> do
    ifM (inline rhs occ cont)
      (do fenv <- use funcEnv
          simplExpr sv (emptySubst sv) ins (evalOcc (fenv, emptyOccVec sv) $ markOcc sv rhs) cont)
      (rebuild (TE tau $ Variable (v,n) __dummyPos) cont)
  Just _ -> rebuild (TE tau $ Variable (v,n) __dummyPos) cont

rebuild :: OutExpr t v b -> Context t v b -> Simp t b (OutExpr t v b)
rebuild e Stop = return e
rebuild _ _ = __todo "rebuild: not implemented yet"

-- ////////////////////////////////////////////////////////////////////////////
-- Heuristics

-- NOTE: This function has also to guarantee that linearity is preverved if the expression
--   in question is duplicated / zilinc
isTrivial :: OutExpr t v b -> Bool
isTrivial (TE _ (Variable _ _)) = True  -- If this var is linear, then the binder has to be linear as well
isTrivial (TE _ (Unit)) = True
isTrivial (TE _ (ILit {})) = True
isTrivial (TE _ (SLit {})) = True
isTrivial (TE _ (Fun {})) = __fixme True  -- ???
isTrivial _ = False

inline :: OutExpr t v b -> OccInfo -> Context t v b -> Simp t b Bool
inline rhs OnceSafe _ = __impossible "inline"
-- inline rhs OnceUnsafe cont = noWorkDup rhs && not (veryBoring cont)
inline rhs MultiSafe cont = return $ inlineMulti rhs cont
inline rhs MultiUnsafe cont = andM [pure $ noWorkDup rhs, noLinear rhs, pure $ inlineMulti rhs cont]  -- FIXME: need to check if not let!'ed var / zilinc
inline rhs LetBanged cont = return $ False
inline _ _ _ = __impossible "inline"

-- FIXME: these heuristics are now taking the most conservative decisions

noLinear :: PosTypedExpr t v a b -> Simp t b Bool
noLinear (TE tau e) = (&&) <$> typeNotLinear tau <*> noLinear' e
  where
    noLinear' (Variable (v,a) _) = return True
    noLinear' (Fun {}) = return True
    noLinear' (Op _ es) = and <$> mapM noLinear es
    noLinear' (App e1 e2) = (&&) <$> noLinear e1 <*> noLinear e2
    noLinear' (Con _ e _) = noLinear e
    noLinear' (Unit) = return True
    noLinear' (ILit {}) = return True
    noLinear' (SLit {}) = return True
    noLinear' (Let a e1 e2) = (&&) <$> noLinear e1 <*> noLinear e2
    noLinear' (LetBang _ a e1 e2) = (&&) <$> noLinear e1 <*> noLinear e2
    noLinear' (Tuple e1 e2) = (&&) <$> noLinear e1 <*> noLinear e2
    noLinear' (Struct fs) = and <$> mapM (noLinear . snd) fs
    noLinear' (If e1 e2 e3) = andM [noLinear e1, noLinear e2, noLinear e3]
    noLinear' (Case e _ (_,_,e1) (_,_,e2)) = andM [noLinear e, noLinear e1, noLinear e2]
    noLinear' (Esac e) = noLinear e
    noLinear' (Split a e1 e2) = (&&) <$> noLinear e1 <*> noLinear e2
    noLinear' (Member rec _) = noLinear rec
    noLinear' (Take a rec _ e) = (&&) <$> noLinear rec <*> noLinear e
    noLinear' (Put rec _ e) = (&&) <$> noLinear rec <*> noLinear e
    noLinear' (Promote ty e) = noLinear e
    noLinear' (Cast ty e) = noLinear e

noWorkDup :: OutExpr t v b -> Bool
noWorkDup _ = __fixme False

veryBoring :: Context t v b -> Bool
veryBoring _ = __fixme True

inlineMulti :: OutExpr t v b -> Context t v b -> Bool
inlineMulti rhs cont | noSizeIncrease rhs cont = True
                     | boring rhs cont = False
                     | otherwise = smallEnough rhs cont

noSizeIncrease :: OutExpr t v b -> Context t v b -> Bool
noSizeIncrease _ _ = __fixme False

boring :: OutExpr t v b -> Context t v b -> Bool
boring _ _ = __fixme True

smallEnough :: OutExpr t v b -> Context t v b -> Bool
smallEnough _ _ = __fixme False

-- ////////////////////////////////////////////////////////////////////////////
-- misc.

lowerExpr0 :: (Show a, v ~ 'Suc v') => SNat v -> PosTypedExpr t ('Suc v) a b -> PosTypedExpr t v a b
lowerExpr0 v = lowerExpr v f0

-- lowerFin (|var|-1) idx var: if var < idx, then var; otherwise var - 1 (idx /= var)
lowerFin :: (v ~ 'Suc v') => SNat v -> Fin ('Suc v) -> Fin ('Suc v) -> Fin v
lowerFin _ FZero FZero = __impossible "lowerFin"
lowerFin _ FZero (FSuc v) = v
lowerFin _ (FSuc i) FZero = FZero
lowerFin (SSuc SZero) (FSuc _) (FSuc _) = __impossible "lowerFin"
lowerFin (SSuc (SSuc n)) (FSuc i) (FSuc v) = FSuc $ lowerFin (SSuc n) i v
#if __GLASGOW_HASKELL__ < 711
lowerFin _ _ _ = __ghc_t3927 "lowerFin"
#endif

lowerExpr :: (Show a, v ~ 'Suc v') => SNat v -> Fin ('Suc v) -> PosTypedExpr t ('Suc v) a b -> PosTypedExpr t v a b
lowerExpr w i (TE tau (Variable (v,a) loc))     = TE tau $ Variable (lowerFin w i v, a) loc
lowerExpr w i (TE tau (Fun fn ts ls note loc))  = TE tau $ Fun fn ts ls note loc
lowerExpr w i (TE tau (Op opr es))          = TE tau $ Op opr (L.map (lowerExpr w i) es)
lowerExpr w i (TE tau (App e1 e2))          = TE tau $ App (lowerExpr w i e1) (lowerExpr w i e2)
lowerExpr w i (TE tau (Con cn e t))         = TE tau $ Con cn (lowerExpr w i e) t
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
lowerExpr w i (TE tau (Cast ty e))       = TE tau $ Cast ty (lowerExpr w i e)

liftExpr :: Show a => Fin ('Suc v) -> PosTypedExpr t v a b -> PosTypedExpr t ('Suc v) a b
liftExpr i (TE tau (Variable (v,a) loc))     = TE tau $ Variable (liftIdx i v,a) loc
liftExpr i (TE tau (Fun fn ts ls note loc))  = TE tau $ Fun fn ts ls note loc
liftExpr i (TE tau (Op opr es))          = TE tau $ Op opr (L.map (liftExpr i) es)
liftExpr i (TE tau (App e1 e2))          = TE tau $ App (liftExpr i e1) (liftExpr i e2)
liftExpr i (TE tau (Con cn e t))         = TE tau $ Con cn (liftExpr i e) t
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
liftExpr i (TE tau (Cast ty e))          = TE tau $ Cast ty (liftExpr i e)

upshiftExpr :: Show a => SNat n -> SNat v -> Fin ('Suc v) -> PosTypedExpr t v a b -> PosTypedExpr t (v :+: n) a b
upshiftExpr SZero _ v e = e
upshiftExpr (SSuc n) sv v e | Refl <- addSucLeft sv n
  = let a = upshiftExpr n sv v e in liftExpr (widenN v n) a

extSubst :: Subst t v b -> Subst t ('Suc v) b
extSubst s = Cons Nothing (fmap (fmap liftSubstRng) s)

liftSubst :: Subst' t ('Suc v) v b -> Subst t ('Suc v) b
liftSubst = fmap $ fmap liftSubstRng

liftSubstRng :: SubstRng t v b -> SubstRng t ('Suc v) b
liftSubstRng (DoneEx e  ) = DoneEx (liftExpr f0 e)
liftSubstRng (SuspEx e s) = SuspEx (liftExpr f0 e) (extSubst s)

extInScopeSet :: InScopeSet t v b -> InScopeSet t ('Suc v) b
extInScopeSet s = Cons Nothing (fmap (fmap liftVarDef) s)

liftInScopeSet :: InScopeSet' t ('Suc v) v b -> InScopeSet t ('Suc v) b
liftInScopeSet = fmap $ fmap liftVarDef

liftVarDef :: VarDef t v b -> VarDef t ('Suc v) b
liftVarDef (Unknown) = Unknown
liftVarDef (BoundTo e occ) = BoundTo (liftExpr f0 e) occ
-- liftVarDef (NotAmong tags) = NotAmong tags

liftContext :: Context t v b -> Context t ('Suc v) b
liftContext Stop = Stop
liftContext _ = __todo "liftContext: not implemented yet"

-- substFin var (|var_body|-1==idx) |var_arg| arg
-- It performs substitution [var |-> arg], the substituted variable must be the one of largest index.
-- Returned env is constituted by `init (var_body) ++ var_arg'
substFin :: Fin ('Suc v') -> SNat v' -> SNat v -> PosTypedExpr t v VarName b -> Either (Fin (v :+: v')) (PosTypedExpr t (v :+: v') VarName b)
substFin FZero SZero _ arg = Right arg
substFin FZero (SSuc _) _ _ = Left FZero
substFin (FSuc _) SZero _ _ = __impossible "substFin"  -- idx must be the largest var
substFin (FSuc v) (SSuc n') n arg = case substFin v n' n arg of
  Left v' -> Left  $ FSuc v'
  Right e -> Right $ liftExpr f0 e

-- betaR body (|var_body|-1==idx) |var_arg| arg ts
betaR :: (v ~ 'Suc v0) => PosTypedExpr t' ('Suc v') VarName b -> SNat v' -> SNat v -> PosTypedExpr t v VarName b -> Vec t' (Type t b) -> Simp t b (PosTypedExpr t (v :+: v') VarName b)
betaR (TE tau (Variable (v,a) loc))  idx n arg ts
  = case substFin v idx n arg of
      Left v' -> pure $ TE (substitute ts tau) $ Variable (v',a) loc
      Right e -> pure e
betaR (TE tau (Fun fn tvs lvs nt loc)) idx n arg ts = pure . TE (substitute ts tau) $ Fun fn (L.map (substitute ts) tvs) lvs nt loc
betaR (TE tau (Op opr es))       idx n arg ts = TE (substitute ts tau) <$> (Op opr <$> mapM (\x -> betaR x idx n arg ts) es)

betaR (TE tau (App e1 e2))       idx n arg ts = TE (substitute ts tau) <$> (App <$> betaR e1 idx n arg ts <*> betaR e2 idx n arg ts)
betaR (TE tau (Con cn e t))      idx n arg ts = TE (substitute ts tau) <$> (Con cn <$> betaR e idx n arg ts <*> pure (substitute ts t))
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
        Refl -> do varg  <- pure $ TE (exprType arg) (Variable (f0,vn) __dummyPos)
                   arg'  <- pure $ upshiftExpr idx n f0 arg
                   body' <- betaR e idx (SSuc n) varg ts
                   return $ TE (substitute ts tau) $ (Let vn arg' body')
  | Refl <- sym (addSucLeft' n idx) = TE (substitute ts tau) <$> (LetBang (L.map (first $ flip widenN n0) vs) a <$> betaR e1 idx n arg ts <*> betaR e2 (SSuc idx) n arg ts)
betaR (TE tau (Tuple e1 e2)) idx n arg ts = TE (substitute ts tau) <$> (Tuple <$> betaR e1 idx n arg ts <*> betaR e2 idx n arg ts)
betaR (TE tau (Struct fs))   idx n arg ts = TE (substitute ts tau) <$> (Struct <$> mapM (secondM (\x -> betaR x idx n arg ts)) fs)
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
betaR (TE tau (Cast ty e))        idx n arg ts = TE (substitute ts tau) <$> (Cast (substitute ts ty) <$> betaR e idx n arg ts)
#if __GLASGOW_HASKELL__ < 711
betaR _ _ _ _ _ = __ghc_t4139 "betaR"
#endif

lookupKind :: Fin t -> Simp t b Kind
lookupKind f = (`V.at` f) <$> use kindEnv

kindcheck = kindcheck_ lookupKind

typeNotLinear :: Type t b -> Simp t b Bool
typeNotLinear t = kindcheck t >>= \k -> return (canDiscard k && canShare k)  -- NOTE: depending on definition of linear types, judgement may change / zilinc
