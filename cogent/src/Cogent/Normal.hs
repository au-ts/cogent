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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}

module Cogent.Normal where

import Cogent.Common.Syntax (VarName)
import Cogent.Compiler
import Cogent.Core
import Cogent.Vec

import Control.Applicative
import Control.Arrow (second, (***))
import Control.Monad.State
import Prelude as P

-- import Debug.Trace

isVar :: UntypedExpr t v a -> Bool
isVar (E (Variable _)) = True
isVar _ = False

isAtom :: UntypedExpr t v a -> Bool
isAtom (E (Variable x)) = True
isAtom (E (Fun fn ts _)) = True
isAtom (E (Op opr es)) | and (map isVar es) = True
isAtom (E (App (E (Fun fn ts _)) arg)) | isVar arg = True
isAtom (E (App f arg)) | isVar f && isVar arg = True
isAtom (E (Con cn x)) | isVar x = True
isAtom (E (Promote t e)) | isVar e = True
isAtom (E (Struct fs)) | and (map (isVar . snd) fs) = True
isAtom (E (Member rec f)) | isVar rec = True
isAtom (E Unit) = True
isAtom (E (ILit {})) = True
isAtom (E (SLit _)) = True
isAtom (E (Tuple e1 e2)) | isVar e1 && isVar e2 = True
isAtom (E (Put rec f v)) | isVar rec && isVar v = True
isAtom (E (Esac e)) | isVar e = True
isAtom _ = False

isNormal :: Show a => UntypedExpr t v a -> Bool
isNormal te | isAtom te = True
isNormal (E (Let _ e1 e2)) | __cogent_fnormalisation == ANF && isAtom e1 && isNormal e2 = True
                            -- XXX | ANF <- __cogent_fnormalisation, __cogent_fcondition_knf && isNormal e1 && isNormal e2 = True
                           | __cogent_fnormalisation `elem` [KNF, LNF] && isNormal e1 && isNormal e2 = True
isNormal (E (LetBang vs _ e1 e2)) | isNormal e1 && isNormal e2 = True
isNormal (E (Case e tn (l1,_,e1) (l2,_,e2))) | isVar e && isNormal e1 && isNormal e2 = True
  -- | ANF <- __cogent_fnormalisation, isVar  e && isNormal e1 && isNormal e2 = True
  -- | KNF <- __cogent_fnormalisation, isAtom e && isNormal e1 && isNormal e2 = True
isNormal (E (If c th el)) | isVar c && isNormal th && isNormal el = True
isNormal (E (Split _ p e)) | isVar  p && isNormal e = True
  -- | ANF <- __cogent_fnormalisation, isVar  p && isNormal e = True
  -- | KNF <- __cogent_fnormalisation, isAtom p && isNormal e = True
isNormal (E (Take _ rec fld e)) | isVar rec && isNormal e = True
isNormal _ = False

newtype AN a = AN { runAN :: State Int a }
             deriving (Functor, Applicative, Monad, MonadState Int)

freshVarPrefix = "__an_var_"

freshVar :: AN VarName
freshVar = do x <- get
              put (x + 1)
              return $ freshVarPrefix ++ show x

normal :: [Definition UntypedExpr VarName] -> [Definition UntypedExpr VarName]
normal = flip evalState 0 . runAN . mapM normaliseDefinition

verifyNormal :: Show a => [Definition UntypedExpr a] -> Bool
verifyNormal [] = True
verifyNormal (d:ds) =
  let b = case d of
            FunDef _ _ _ _ _ e -> isNormal e
            otherwise -> True
  in if b then verifyNormal ds else False

normaliseDefinition :: Definition UntypedExpr VarName -> AN (Definition UntypedExpr VarName)
normaliseDefinition (FunDef attr fn ts ti to e) = FunDef attr fn ts ti to <$> (wrapPut =<< normaliseExpr s1 e)
normaliseDefinition d = pure d

normaliseExpr :: SNat v -> UntypedExpr t v VarName -> AN (UntypedExpr t v VarName)
normaliseExpr v e = normalise v e (\_ x -> return x)

upshiftExpr :: SNat n -> SNat v -> Fin ('Suc v) -> UntypedExpr t v a -> UntypedExpr t (v :+: n) a
upshiftExpr SZero _ _ e = e
upshiftExpr (SSuc n) sv v e | Refl <- addSucLeft sv n
  = let a = upshiftExpr n sv v e in insertIdxAt (widenN v n) a

normalise :: SNat v -> UntypedExpr t v VarName
          -> (forall n. SNat n -> UntypedExpr t (v :+: n) VarName -> AN (UntypedExpr t (v :+: n) VarName))
          -> AN (UntypedExpr t v VarName)
normalise v e@(E (Variable var)) k = k s0 (E (Variable var))
normalise v e@(E (Fun fn ts _)) k = k s0 e
normalise v e@(E (App (E (Fun fn ts nt)) arg)) k
  = normaliseName v arg$ \n' arg' ->
          k n' ((E $ App (E (Fun fn ts nt)) arg'))
normalise v e@(E (App f arg)) k
  = normaliseName v f $ \n f' ->
      normaliseName (sadd v n) (upshiftExpr n v f0 arg) $ \n' arg' ->
        withAssoc v n n' $ \Refl ->
          k (sadd n n') ((E $ App (upshiftExpr n' (sadd v n) f0 f') arg'))
normalise v (E (Con cn e)) k = normaliseName v e $ \n e' -> k n (E $ Con cn e')
normalise v e@(E (Unit)) k = k s0 e
normalise v e@(E (ILit {})) k = k s0 e
normalise v e@(E (SLit {})) k = k s0 e
normalise v (E (Let a e1 e2)) k
  | __cogent_fnormalisation `elem` [KNF, LNF]  -- || (__cogent_fnormalisation == ANF && __cogent_fcondition_knf && isCondition e1)
  = do e1' <- normaliseExpr v e1
       E <$> (Let a e1' <$> (normalise (SSuc v) e2 $ \n -> case addSucLeft v n of Refl -> k (SSuc n)))
  | __cogent_fnormalisation == ANF
  = normaliseAtom v e1 $ \n e1' -> case addSucLeft v n of
     Refl -> E <$> (Let a e1' <$> (normalise (sadd (SSuc v) n) (upshiftExpr n (SSuc v) f1 e2) $ \n' ->
         withAssocS v n n' $ \Refl -> k (SSuc (sadd n n'))))
  | otherwise = __exhaustivity "normalise"
normalise v (E (LetBang vs a e1 e2)) k
  = do e1' <- normaliseExpr v e1
       E <$> (LetBang vs a e1' <$> (normalise (SSuc v) e2 $ \n -> case addSucLeft v n of Refl -> k (SSuc n)))
normalise v (E (Tuple e1 e2)) k
  = normaliseName v e1 $ \n e1' ->
    normaliseName (sadd v n) (upshiftExpr n v f0 e2) $ \n' e2' ->
    withAssoc v n n' $ \Refl ->
    k (sadd n n') (E $ Tuple (upshiftExpr n' (sadd v n) f0 e1') e2')
normalise v (E (If c th el)) k | LNF <- __cogent_fnormalisation =
  freshVar >>= \a ->
  normaliseExpr v th >>= \th' ->
  normaliseExpr v el >>= \el' ->
  normaliseName v c $ \n c' ->
  E <$> (Let a (E $ If c' (upshiftExpr n v f0 th') (upshiftExpr n v f0 el')) <$> k (SSuc n) (E $ Variable (f0, a)))
normalise v (E (If c th el)) k = normaliseName v c $ \n c' ->
  E <$> (If c' <$> (normalise (sadd v n) (upshiftExpr n v f0 th) (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n')))
               <*> (normalise (sadd v n) (upshiftExpr n v f0 el) (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n'))))
normalise v (E (Case e tn (l1,a1,e1) (l2,a2,e2))) k | LNF <- __cogent_fnormalisation =
  freshVar >>= \a ->
  normaliseExpr (SSuc v) e1 >>= \e1' ->
  normaliseExpr (SSuc v) e2 >>= \e2' ->
  normaliseName v e $ \n e' ->
  case sym $ addSucLeft v n of
    Refl -> E <$> (Let a (E $ Case e' tn (l1,a1,upshiftExpr n (SSuc v) f0 e1') (l2,a2,upshiftExpr n (SSuc v) f0 e2')) <$> k (SSuc n) (E $ Variable (f0, a)))
normalise v (E (Case e tn (l1,a1,e1) (l2,a2,e2))) k =
  normaliseName v e $ \n e' -> case addSucLeft v n of
    Refl -> let [e1u,e2u] = map (upshiftExpr n (SSuc v) f1) [e1,e2]
             in E <$> (Case e' tn <$> ((l1, a1,) <$> (normalise (sadd (SSuc v) n) e1u $ \n' -> withAssocS v n n' $ \Refl -> k (SSuc (sadd n n'))))
                                  <*> ((l2, a2,) <$> (normalise (sadd (SSuc v) n) e2u $ \n' -> withAssocS v n n' $ \Refl -> k (SSuc (sadd n n')))))
normalise v (E (Esac e)) k = normaliseName v e $ \n e' -> k n (E $ Esac e')
normalise v (E (Split a p e)) k
  = normaliseName v p $ \n p' -> case addSucLeft v n of
      Refl -> case addSucLeft (SSuc v) n of
        Refl -> E <$> (Split a p' <$> (normalise (sadd (SSuc (SSuc v)) n) (upshiftExpr n (SSuc $ SSuc v) f2 e) $ \n' ->
          withAssocSS v n n' $ \Refl -> k (SSuc (SSuc (sadd n n')))))
normalise v (E (Take a rec fld e)) k
  = normaliseName v rec $ \n rec' -> case addSucLeft v n of
      Refl -> case addSucLeft (SSuc v) n of
        Refl -> E <$> (Take a rec' fld <$> (normalise (sadd (SSuc (SSuc v)) n) (upshiftExpr n (SSuc $ SSuc v) f2 e) $ \n' ->
         withAssocSS v n n' $ \Refl -> k (SSuc (SSuc (sadd n n')))))
normalise v (E (Put rec fld e)) k
  = normaliseName v rec $ \n rec' ->
    normaliseName (sadd v n) (upshiftExpr n v f0 e) $ \n' e' ->
    withAssoc v n n' $ \Refl ->
    k (sadd n n') (E $ Put (upshiftExpr n' (sadd v n) f0 rec') fld e')
normalise v (E (Member rec fld)) k = normaliseName v rec $ \n rec' -> k n (E $ Member rec' fld)
normalise v (E (Promote ty e)) k = normaliseName v e $ \n e' -> k n (E $ Promote ty e')
normalise v (E (Op opr es)) k = normaliseNames v es $ \n es' -> k n (E $ Op opr es')
normalise v (E (Struct fs)) k = let (ns,es) = P.unzip fs in normaliseNames v es $ \n es' -> k n (E $ Struct $ P.zip ns es')

normaliseAtom :: SNat v -> UntypedExpr t v VarName
              -> (forall n. SNat n -> UntypedExpr t (v :+: n) VarName -> AN (UntypedExpr t (v :+: n) VarName))
              -> AN (UntypedExpr t v VarName)
normaliseAtom v e k = normalise v e $ \n e' -> if isAtom e' then k n e' else case e' of
  (E (Let a e1 e2)) -> freshVar >>= \a' -> E <$> (Let a e1 <$> (normaliseAtom (SSuc (sadd v n)) e2 $
     \n' e2' -> withAssocS v n n' $ \Refl -> E <$> (Let a' e2' <$> (k (SSuc (sadd n (SSuc n'))) $ E $ Variable (f0, a')))))
  (E (LetBang vs a e1 e2)) -> freshVar >>= \a' -> E <$> (LetBang vs a e1 <$> (normaliseAtom (SSuc (sadd v n)) e2 $
     \n' e2'  -> withAssocS v n n' $ \Refl -> E <$> (Let a' e2' <$> (k (SSuc (sadd n (SSuc n'))) $ E $ Variable (f0, a')))))
  (E (Case e tn (l1,a1,e1) (l2,a2,e2))) ->
     E <$> (Case e tn <$> ((l1,a1,) <$> (normaliseAtom (SSuc (sadd v n)) e1 (\n' -> withAssocS v n n' $ \Refl -> k (sadd n (SSuc n')))))
                                    <*> ((l2,a2,) <$> (normaliseAtom (SSuc (sadd v n)) e2 (\n' -> withAssocS v n n' $ \Refl -> k (sadd n (SSuc n'))))))
  -- FIXME: does this one also need to be changed for LNF? / zilinc
  (E (If c th el)) -> E <$> (If c <$> (normaliseAtom (sadd v n) th (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n')))
                                  <*> (normaliseAtom (sadd v n) el (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n'))))
  (E (Split a p e)) -> E <$> (Split a p <$> (normaliseAtom (SSuc (SSuc (sadd v n))) e $ \n' ->
     withAssocSS v n n' $ \Refl -> k (sadd n (SSuc (SSuc n')))))
  (E (Take a rec fld e)) -> E <$> (Take a rec fld <$> (normaliseAtom (SSuc (SSuc (sadd v n))) e $ \n' ->
     withAssocSS v n n' $ \Refl -> k (sadd n (SSuc (SSuc n')))))
  _ -> __impossible "normaliseAtom"

wrapPut :: UntypedExpr t v VarName -> AN (UntypedExpr t v VarName)
wrapPut e | not __cogent_fwrap_put_in_let = return e
wrapPut put@(E (Put rec f e)) = freshVar >>= \a -> return $ E (Let a put (E $ Variable (f0,a)))
wrapPut (E (Let a e1 e2)) = E <$> (Let a e1 <$> wrapPut e2)
wrapPut (E (LetBang vs a e1 e2)) = E <$> (LetBang vs a <$> wrapPut e1 <*> wrapPut e2)
wrapPut (E (Case e tn (l1,a1,e1) (l2,a2,e2))) = E <$> (Case e tn <$> ((l1,a1,) <$> wrapPut e1) <*> ((l2,a2,) <$> wrapPut e2))
wrapPut (E (If c th el)) = E <$> (If c <$> wrapPut th <*> wrapPut el)
wrapPut (E (Split a p e)) = E <$> (Split a p <$> wrapPut e)
wrapPut (E (Take a rec fld e)) = E <$> (Take a rec fld <$> wrapPut e)
wrapPut e = return e  -- non-normal, thus put cannot occur

normaliseName :: SNat v -> UntypedExpr t v VarName
              -> (forall n. SNat n -> UntypedExpr t (v :+: n) VarName -> AN (UntypedExpr t (v :+: n) VarName))
              -> AN (UntypedExpr t v VarName)
normaliseName v e k = freshVar >>= \a -> normaliseAtom v e $ \n e' -> if isVar e' then k n e' else E <$> (Let a e' <$> k (SSuc n) (E (Variable (f0,a))))

normaliseNames :: SNat v -> [UntypedExpr t v VarName]
               -> (forall n. SNat n -> [UntypedExpr t (v :+: n) VarName] -> AN (UntypedExpr t (v :+: n) VarName))
               -> AN (UntypedExpr t v VarName)
normaliseNames v [] k = k s0 []
normaliseNames v (e:es) k
  = normaliseName v e $ \n e' ->
      normaliseNames (sadd v n) (map (upshiftExpr n v f0) es) $ \n' es' ->
        withAssoc v n n' $ \Refl -> k (sadd n n') (upshiftExpr n' (sadd v n) f0 e':es')

insertIdxAt :: Fin ('Suc v) -> UntypedExpr t v a -> UntypedExpr t ('Suc v) a
insertIdxAt cut (E e) = E $ insertIdxAt' cut e
  where
    insertIdxAt' :: Fin ('Suc v) -> Expr t v a UntypedExpr -> Expr t ('Suc v) a UntypedExpr
    insertIdxAt' cut (Variable v) = Variable $ (liftIdx cut *** id) v
    insertIdxAt' cut (Fun fn ty nt) = Fun fn ty nt
    insertIdxAt' cut (Op opr es) = Op opr $ map (insertIdxAt cut) es
    insertIdxAt' cut (App e1 e2) = App (insertIdxAt cut e1) (insertIdxAt cut e2)
    insertIdxAt' cut (Con tag e) = Con tag (insertIdxAt cut e)
    insertIdxAt' cut (Unit) = Unit
    insertIdxAt' cut (ILit n pt) = ILit n pt
    insertIdxAt' cut (SLit s) = SLit s
    insertIdxAt' cut (Let a e1 e2) = Let a (insertIdxAt cut e1) (insertIdxAt (FSuc cut) e2)
    insertIdxAt' cut (LetBang vs a e1 e2) = LetBang (map (liftIdx cut *** id) vs) a (insertIdxAt cut e1) (insertIdxAt (FSuc cut) e2)
    insertIdxAt' cut (Tuple e1 e2) = Tuple (insertIdxAt cut e1) (insertIdxAt cut e2)
    insertIdxAt' cut (Struct fs) = Struct $ map (second $ insertIdxAt cut) fs
    insertIdxAt' cut (If c e1 e2) = If (insertIdxAt cut c) (insertIdxAt cut e1) (insertIdxAt cut e2)
    insertIdxAt' cut (Case c tag (l1,a1,alt) (l2,a2,alts)) =
      Case (insertIdxAt cut c) tag (l1, a1, insertIdxAt (FSuc cut) alt) (l2, a2, insertIdxAt (FSuc cut) alts)
    insertIdxAt' cut (Esac e) = Esac (insertIdxAt cut e)
    insertIdxAt' cut (Split a e1 e2) = Split a (insertIdxAt cut e1) (insertIdxAt (FSuc (FSuc cut)) e2)
    insertIdxAt' cut (Member e fld) = Member (insertIdxAt cut e) fld
    insertIdxAt' cut (Take a rec fld e) = Take a (insertIdxAt cut rec) fld (insertIdxAt (FSuc (FSuc cut)) e)
    insertIdxAt' cut (Put rec fld e) = Put (insertIdxAt cut rec) fld (insertIdxAt cut e)
    insertIdxAt' cut (Promote ty e) = Promote ty (insertIdxAt cut e)

isCondition :: UntypedExpr t v a -> Bool
isCondition (E (If {})) = True
isCondition (E (Case {})) = True
isCondition _ = False
