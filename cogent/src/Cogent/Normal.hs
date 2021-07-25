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
import Cogent.Util (getLoc)
import Data.Fin
import Data.Nat
import Data.Vec
import Data.PropEq

import Control.Applicative
import Control.Arrow (first, second)
import Control.Monad.State
import Prelude as P

-- import Debug.Trace


isVar :: PosUntypedExpr t v a b -> Bool
isVar (E (Variable _ _)) = True
isVar _ = False


-- FIXME: I used to think that an atom corresponds to a Cogent construct which can be
-- generated to a single C expression, whereas a NF corresponds to that which has to be
-- generated as statements. But this is not accurately reflected in the code below, which
-- made me to rethink what the criteria were. Another possibility is that if the Cogent
-- construct takes a continuation as argument, then it's going to be a NF. This view more closely
-- matches what the code is doing, however it's less justifiable as far as I can see.
-- This matter might be important if we want to carefully study the performance of the
-- generated code, as it should affact if the C code can be generated in SSA form or
-- something that gcc has a better chance to see optimisation candidates. / zilinc (24-Oct-19)

isAtom :: PosUntypedExpr t v a b -> Bool
isAtom (E (Variable x _)) = True
isAtom (E (Fun _ _ _ _ _)) = True
isAtom (E (Op opr es _)) | all isVar es = True
isAtom (E (App (E (Fun _ _ _ _ _)) arg _)) | isVar arg = True
isAtom (E (App f arg _)) | isVar f && isVar arg = True
isAtom (E (Con cn x _ _)) | isVar x = True
isAtom (E (Unit _)) = True
isAtom (E (ILit {})) = True
isAtom (E (SLit _ _)) = True
#ifdef BUILTIN_ARRAYS
isAtom (E (ALit es)) | all isVar es = True
isAtom (E (ArrayIndex e i)) | isVar e && isVar i = True
isAtom (E (ArrayMap2 (_,f) (e1,e2)))
  | isNormal f && isVar e1 && isVar e2 = True
  -- \ ^^^ FIXME: does it make sense? @ArrayMap@ cannot be made an expression.
  -- Does the atom-expression / normal-statement correspondence still hold?
isAtom (E (Singleton e)) | isVar e = True
isAtom (E (ArrayPut arr i e)) | isVar arr && isVar i && isVar e = True
#endif
isAtom (E (Tuple e1 e2 _)) | isVar e1 && isVar e2 = True
isAtom (E (Struct fs _)) | all (isVar . snd) fs = True
isAtom (E (Esac e _)) | isVar e = True
isAtom (E (Member rec f _)) | isVar rec = True
isAtom (E (Put rec f v _)) | isVar rec && isVar v = True
isAtom (E (Promote t e _)) | isVar e = True
isAtom (E (Cast t e _)) | isVar e = True
isAtom _ = False

isNormal :: PosUntypedExpr t v a b -> Bool
isNormal te | isAtom te = True
isNormal (E (Let _ e1 e2 _)) | __cogent_fnormalisation == ANF && isAtom e1 && isNormal e2 = True
                            -- XXX | ANF <- __cogent_fnormalisation, __cogent_fcondition_knf && isNormal e1 && isNormal e2 = True
                           | __cogent_fnormalisation `elem` [KNF, LNF] && isNormal e1 && isNormal e2 = True
isNormal (E (LetBang vs _ e1 e2 _)) | isNormal e1 && isNormal e2 = True
isNormal (E (Case e tn (l1,_,e1) (l2,_,e2) _)) | isVar e && isNormal e1 && isNormal e2 = True
  -- \| ANF <- __cogent_fnormalisation, isVar  e && isNormal e1 && isNormal e2 = True
  -- \| KNF <- __cogent_fnormalisation, isAtom e && isNormal e1 && isNormal e2 = True
isNormal (E (If  c th el _)) | isVar c  && isNormal th && isNormal el = True
#ifdef BUILTIN_ARRAYS
isNormal (E (Pop _ e1 e2)) | isVar e1 && isNormal e2 = True
isNormal (E (ArrayTake _ arr i e)) | isVar arr && isVar i && isNormal e = True
#endif
isNormal (E (Split _ p e _)) | isVar p  && isNormal e  = True
  -- \| ANF <- __cogent_fnormalisation, isVar  p && isNormal e = True
  -- \| KNF <- __cogent_fnormalisation, isAtom p && isNormal e = True
isNormal (E (Take _ rec fld e _)) | isVar rec && isNormal e = True
isNormal _ = False

newtype AN a = AN { runAN :: State Int a }
             deriving (Functor, Applicative, Monad, MonadState Int)

freshVarPrefix = "x__an_var_"

freshVar :: AN VarName
freshVar = do x <- get
              put (x + 1)
              return $ freshVarPrefix ++ show x

normal :: [Definition PosUntypedExpr (VarName, Maybe VarName) b] -> [Definition PosUntypedExpr (VarName, Maybe VarName) b]
normal = flip evalState 0 . runAN . mapM normaliseDefinition

verifyNormal :: Show a => [Definition PosUntypedExpr a b] -> Bool
verifyNormal [] = True
verifyNormal (d:ds) =
  let b = case d of
            FunDef _ _ _ _ _ _ e -> isNormal e
            _ -> True
   in b && verifyNormal ds

normaliseDefinition :: Definition PosUntypedExpr (VarName, Maybe VarName) b -> AN (Definition PosUntypedExpr (VarName, Maybe VarName) b)
normaliseDefinition (FunDef attr fn ts ls ti to e) = FunDef attr fn ts ls ti to <$> (wrapPut =<< normaliseExpr s1 e)
normaliseDefinition d = pure d

normaliseExpr :: SNat v -> PosUntypedExpr t v (VarName, Maybe VarName) b -> AN (PosUntypedExpr t v (VarName, Maybe VarName) b)
normaliseExpr v e = normalise v e (\_ x -> return x)

upshiftExpr :: SNat n -> SNat v -> Fin ('Suc v) -> PosUntypedExpr t v a b -> PosUntypedExpr t (v :+: n) a b
upshiftExpr SZero _ _ e = e
upshiftExpr (SSuc n) sv v e | Refl <- addSucLeft sv n
  = let a = upshiftExpr n sv v e in insertIdxAtUntypedExpr (widenN v n) a

-- | @upshiftType n cut t@: upshift by @n@, for all the indices starting from @cut@
upshiftType :: SNat n -> Nat -> Type t a -> Type t a
upshiftType SZero cut t = t
upshiftType (SSuc n) cut t = let t' = upshiftType n cut t in insertIdxAtType cut t'

normalise :: SNat v
          -> PosUntypedExpr t v (VarName, Maybe VarName) b
          -> (forall n. SNat n -> PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b -> AN (PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b))
          -> AN (PosUntypedExpr t v (VarName, Maybe VarName) b)
normalise v e@(E (Variable var loc)) k = k s0 (E (Variable var loc))
normalise v e@(E (Fun{})) k = k s0 e
normalise v   (E (Op opr es loc)) k = normaliseNames v es $ \n es' -> k n (E $ Op opr es' loc)
normalise v e@(E (App (E (Fun fn ts ls nt locFun)) arg locApp)) k
  = normaliseName v arg $ \n arg' ->
      k n (E $ App (E (Fun fn (fmap (upshiftType n $ finNat f0) ts) ls nt locFun)) arg' locApp)
normalise v e@(E (App f arg loc)) k
  = normaliseName v f $ \n f' ->
      normaliseName (sadd v n) (upshiftExpr n v f0 arg) $ \n' arg' ->
        withAssoc v n n' $ \Refl ->
          k (sadd n n') (E $ App (upshiftExpr n' (sadd v n) f0 f') arg' loc)
normalise v   (E (Con cn e t loc)) k = normaliseName v e $ \n e' -> k n (E $ Con cn e' (upshiftType n (finNat f0) t) loc)
normalise v e@(E (Unit _)) k = k s0 e
normalise v e@(E (ILit {})) k = k s0 e
normalise v e@(E (SLit {})) k = k s0 e
#ifdef BUILTIN_ARRAYS
normalise v   (E (ALit es)) k = normaliseNames v es $ \n es' -> k n (E $ ALit es')
normalise v   (E (ArrayIndex e i)) k
  = normaliseName v e $ \n e' ->
      normaliseName (sadd v n) (upshiftExpr n v f0 i) $ \n' i' ->
        withAssoc v n n' $ \Refl ->
          k (sadd n n') (E $ ArrayIndex (upshiftExpr n' (sadd v n) f0 e') i')
normalise v   (E (ArrayMap2 ((a1,a2),f) (e1,e2))) k
  = normaliseExpr (SSuc $ SSuc v) f >>= \f' ->
      normaliseName v e1 $ \n e1' ->
      normaliseName (sadd v n) (upshiftExpr n v f0 e2) $ \n' e2' ->
        withAssoc v n n' $ \Refl ->
        withSSAssoc v n n' $ \Refl ->
        k (sadd n n') $ E $ ArrayMap2 ((a1,a2), upshiftExpr (sadd n n') (SSuc (SSuc v)) f2 f')
                                      (upshiftExpr n' (sadd v n) f0 e1', e2')
normalise v   (E (Pop a e1 e2)) k
  = normaliseName v e1 $ \n e1' -> case addSucLeft v n of
      Refl -> case addSucLeft (SSuc v) n of
        Refl -> E <$> (Pop a e1' <$> (normalise (sadd (SSuc (SSuc v)) n) (upshiftExpr n (SSuc $ SSuc v) f2 e2) $ \n' ->
          withAssocSS v n n' $ \Refl -> k (SSuc (SSuc (sadd n n')))))
normalise v   (E (Singleton e)) k = normaliseName v e $ \n e' -> k n (E $ Singleton e')
normalise v   (E (ArrayPut arr i e)) k
  = normaliseName v arr $ \n arr' ->
    normaliseName (sadd v n) (upshiftExpr n v f0 i) $ \n' i' ->
      withAssoc v n n' $ \Refl ->
      normaliseName (sadd (sadd v n) n') (upshiftExpr (sadd n n') v f0 e) $ \n'' e' ->
        case sym $ assoc v (sadd n n') n'' of
          Refl -> case assoc (sadd v n) n' n'' of
            Refl -> k (sadd (sadd n n') n'') $ E $
                      ArrayPut (upshiftExpr (sadd n' n'') (sadd v n) f0 arr')
                               (upshiftExpr n'' (sadd v n `sadd` n') f0 i')
                               e'
normalise v   (E (ArrayTake (o, ca) pa i e)) k
  = normaliseName v pa $ \n pa' ->
    normaliseName (sadd v n) (upshiftExpr n v f0 i) $ \n' i' ->
      withSSAssoc v n n' $ \Refl ->
        withAssoc v n n' $ \Refl ->
          E <$> (ArrayTake (o, ca)
                (upshiftExpr n' (sadd v n) f0 pa')
                i')
            <$> (normalise (SSuc $ SSuc (sadd (sadd v n) n')) (upshiftExpr (sadd n n') (SSuc $ SSuc v) f2 e) $
                \n'' -> case sym $ assoc v (sadd n n') n'' of
                    Refl -> case sym $ addSucLeft (SSuc $ sadd (sadd v n) n') n'' of
                        Refl -> case sym $ addSucLeft (sadd (sadd v n) n') n'' of
                            Refl -> k (SSuc $ SSuc (sadd (sadd n n') n'')))
#endif
normalise v   (E (Let a e1 e2 loc)) k
  | __cogent_fnormalisation `elem` [KNF, LNF]  -- \ || (__cogent_fnormalisation == ANF && __cogent_fcondition_knf && isCondition e1)
  = do e1' <- normaliseExpr v e1
       E <$> (Let a e1' <$> (normalise (SSuc v) e2 $ \n -> case addSucLeft v n of Refl -> k (SSuc n)) <*> pure loc)
  | __cogent_fnormalisation == ANF
  = normaliseAtom v e1 $ \n e1' -> case addSucLeft v n of
     Refl -> E <$> (Let a e1' <$> (normalise (sadd (SSuc v) n) (upshiftExpr n (SSuc v) f1 e2) $ \n' ->
         withAssocS v n n' $ \Refl -> k (SSuc (sadd n n'))) <*> pure loc)
  | otherwise = __exhaustivity "normalise"
normalise v (E (LetBang vs a e1 e2 loc)) k
  = do e1' <- normaliseExpr v e1
       E <$> (LetBang vs a e1' <$> (normalise (SSuc v) e2 $ \n -> case addSucLeft v n of Refl -> k (SSuc n)) <*> pure loc)
normalise v (E (Tuple e1 e2 loc)) k
  = normaliseName v e1 $ \n e1' ->
    normaliseName (sadd v n) (upshiftExpr n v f0 e2) $ \n' e2' ->
    withAssoc v n n' $ \Refl ->
    k (sadd n n') (E $ Tuple (upshiftExpr n' (sadd v n) f0 e1') e2' loc)
normalise v (E (Struct fs loc)) k = let (ns,es) = P.unzip fs in normaliseNames v es $ \n es' -> k n (E $ Struct (P.zip ns es') loc)
normalise v (E (If c th el loc)) k | LNF <- __cogent_fnormalisation =
  freshVar >>= \a ->
  normaliseExpr v th >>= \th' ->
  normaliseExpr v el >>= \el' ->
  normaliseName v c $ \n c' ->
  E <$> (Let (a, Nothing) (E $ If c' (upshiftExpr n v f0 th') (upshiftExpr n v f0 el') loc) <$> k (SSuc n) (E $ Variable (f0, (a, Nothing)) loc ) <*> pure loc)
normalise v (E (If c th el loc)) k = normaliseName v c $ \n c' ->
  E <$> (If c' <$> normalise (sadd v n) (upshiftExpr n v f0 th) (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n'))
               <*> normalise (sadd v n) (upshiftExpr n v f0 el) (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n'))
               <*> pure loc)
normalise v (E (Case e tn (l1,a1,e1) (l2,a2,e2) loc)) k | LNF <- __cogent_fnormalisation =
  freshVar >>= \a ->
  normaliseExpr (SSuc v) e1 >>= \e1' ->
  normaliseExpr (SSuc v) e2 >>= \e2' ->
  normaliseName v e $ \n e' ->
  case sym $ addSucLeft v n of
    Refl -> E <$> (Let (a, Nothing) (E $ Case e' tn (l1,a1,upshiftExpr n (SSuc v) f0 e1') (l2,a2,upshiftExpr n (SSuc v) f0 e2') loc) <$> k (SSuc n) (E $ Variable (f0, (a, Nothing)) loc) <*> pure loc)
normalise v (E (Case e tn (l1,a1,e1) (l2,a2,e2) loc)) k =
  normaliseName v e $ \n e' -> case addSucLeft v n of
    Refl -> let [e1u,e2u] = map (upshiftExpr n (SSuc v) f1) [e1,e2]
             in E <$> (Case e' tn <$> ((l1, a1,) <$> (normalise (sadd (SSuc v) n) e1u $ \n' -> withAssocS v n n' $ \Refl -> k (SSuc (sadd n n'))))
                                  <*> ((l2, a2,) <$> (normalise (sadd (SSuc v) n) e2u $ \n' -> withAssocS v n n' $ \Refl -> k (SSuc (sadd n n'))))
                                  <*> pure loc)
normalise v (E (Esac e loc)) k = normaliseName v e $ \n e' -> k n (E $ Esac e' loc)
normalise v (E (Split a p e loc)) k
  = normaliseName v p $ \n p' -> case addSucLeft v n of
      Refl -> case addSucLeft (SSuc v) n of
        Refl -> E <$> (Split a p' <$> (normalise (sadd (SSuc (SSuc v)) n) (upshiftExpr n (SSuc $ SSuc v) f2 e) $ \n' ->
          withAssocSS v n n' $ \Refl -> k (SSuc (SSuc (sadd n n')))) <*> pure loc)
normalise v (E (Member rec fld loc)) k = normaliseName v rec $ \n rec' -> k n (E $ Member rec' fld loc)
normalise v (E (Take a rec fld e loc)) k
  = normaliseName v rec $ \n rec' -> case addSucLeft v n of
      Refl -> case addSucLeft (SSuc v) n of
        Refl -> E <$> (Take a rec' fld <$> (normalise (sadd (SSuc (SSuc v)) n) (upshiftExpr n (SSuc $ SSuc v) f2 e) $ \n' ->
         withAssocSS v n n' $ \Refl -> k (SSuc (SSuc (sadd n n')))) <*> pure loc)
normalise v (E (Put rec fld e loc)) k
  = normaliseName v rec $ \n rec' ->
    normaliseName (sadd v n) (upshiftExpr n v f0 e) $ \n' e' ->
    withAssoc v n n' $ \Refl ->
    k (sadd n n') (E $ Put (upshiftExpr n' (sadd v n) f0 rec') fld e' loc)
normalise v (E (Promote ty e loc)) k = normaliseName v e $ \n e' -> k n (E $ Promote (upshiftType n (finNat f0) ty) e' loc)
normalise v (E (Cast ty e loc)) k = normaliseName v e $ \n e' -> k n (E $ Cast (upshiftType n (finNat f0) ty) e' loc)

normaliseAtom :: SNat v -> PosUntypedExpr t v (VarName, Maybe VarName) b
              -> (forall n. SNat n -> PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b -> AN (PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b))
              -> AN (PosUntypedExpr t v (VarName, Maybe VarName) b)
normaliseAtom v e k = normalise v e $ \n e' -> if isAtom e' then k n e' else case e' of
  (E (Let a e1 e2 loc)) -> freshVar >>= \a' -> E <$> (Let a e1 <$> (normaliseAtom (SSuc (sadd v n)) e2 $
     \n' e2' -> withAssocS v n n' $ \Refl -> E <$> (Let (a', Nothing) e2' <$> (k (SSuc (sadd n (SSuc n'))) $ E $ Variable (f0, (a', Nothing)) loc) <*> pure loc)) <*> pure loc)  
  (E (LetBang vs a e1 e2 loc)) -> freshVar >>= \a' -> E <$> (LetBang vs a e1 <$> (normaliseAtom (SSuc (sadd v n)) e2 $
     \n' e2'  -> withAssocS v n n' $ \Refl -> E <$> (Let (a', Nothing) e2' <$> (k (SSuc (sadd n (SSuc n'))) $ E $ Variable (f0, (a', Nothing)) loc) <*> pure loc)) <*> pure loc)
  (E (Case e tn (l1,a1,e1) (l2,a2,e2) loc)) ->
     E <$> (Case e tn <$> ((l1,a1,) <$> normaliseAtom (SSuc (sadd v n)) e1 (\n' -> withAssocS v n n' $ \Refl -> k (sadd n (SSuc n'))))
                                    <*> ((l2,a2,) <$> normaliseAtom (SSuc (sadd v n)) e2 (\n' -> withAssocS v n n' $ \Refl -> k (sadd n (SSuc n'))))
                                    <*> pure loc)
  -- FIXME: does this one also need to be changed for LNF? / zilinc
  (E (If c th el loc)) -> E <$> (If c <$> normaliseAtom (sadd v n) th (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n'))
                                      <*> normaliseAtom (sadd v n) el (\n' -> withAssoc v n n' $ \Refl -> k (sadd n n'))
                                      <*> pure loc)
  (E (Split a p e loc)) -> E <$> (Split a p <$> (normaliseAtom (SSuc (SSuc (sadd v n))) e $ \n' ->
     withAssocSS v n n' $ \Refl -> k (sadd n (SSuc (SSuc n')))) <*> pure loc)
  (E (Take a rec fld e loc)) -> E <$> (Take a rec fld <$> (normaliseAtom (SSuc (SSuc (sadd v n))) e $ \n' ->
     withAssocSS v n n' $ \Refl -> k (sadd n (SSuc (SSuc n')))) <*> pure loc)
  _ -> __impossible "normaliseAtom"

wrapPut :: PosUntypedExpr t v (VarName, Maybe VarName) b -> AN (PosUntypedExpr t v (VarName, Maybe VarName) b)
wrapPut e | not __cogent_fwrap_put_in_let = return e
wrapPut put@(E (Put rec f e loc)) = freshVar >>= \a -> return $ E (Let (a, Nothing) put (E $ Variable (f0,(a, Nothing)) loc) loc)
wrapPut (E (Let a e1 e2 loc)) = E <$> (Let a e1 <$> wrapPut e2 <*> pure loc)
wrapPut (E (LetBang vs a e1 e2 loc)) = E <$> (LetBang vs a <$> wrapPut e1 <*> wrapPut e2 <*> pure loc)
wrapPut (E (Case e tn (l1,a1,e1) (l2,a2,e2) loc)) = E <$> (Case e tn <$> ((l1,a1,) <$> wrapPut e1) <*> ((l2,a2,) <$> wrapPut e2) <*> pure loc)
wrapPut (E (If c th el loc)) = E <$> (If c <$> wrapPut th <*> wrapPut el <*> pure loc)
wrapPut (E (Split a p e loc)) = E <$> (Split a p <$> wrapPut e <*> pure loc)
wrapPut (E (Take a rec fld e loc)) = E <$> (Take a rec fld <$> wrapPut e <*> pure loc)
wrapPut e = return e  -- non-normal, thus put cannot occur

normaliseName :: SNat v -> PosUntypedExpr t v (VarName, Maybe VarName) b
              -> (forall n. SNat n -> PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b -> AN (PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b))
              -> AN (PosUntypedExpr t v (VarName, Maybe VarName) b)
normaliseName v e k =
  freshVar >>=
    \a ->
      normaliseAtom v e $ \n e' ->
        if isVar e'
          then k n e'
          else E <$> (Let (a, Nothing) e' <$> k (SSuc n) (E (Variable (f0,(a, Nothing)) (getLoc e))) <*> pure (getLoc e))

normaliseNames :: SNat v -> [PosUntypedExpr t v (VarName, Maybe VarName) b]
               -> (forall n. SNat n -> [PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b] -> AN (PosUntypedExpr t (v :+: n) (VarName, Maybe VarName) b))
               -> AN (PosUntypedExpr t v (VarName, Maybe VarName) b)
normaliseNames v [] k = k s0 []
normaliseNames v (e:es) k
  = normaliseName v e $ \n e' ->
      normaliseNames (sadd v n) (map (upshiftExpr n v f0) es) $ \n' es' ->
        withAssoc v n n' $ \Refl -> k (sadd n n') (upshiftExpr n' (sadd v n) f0 e':es')

isCondition :: PosUntypedExpr t v a b -> Bool
isCondition (E (If {})) = True
isCondition (E (Case {})) = True
isCondition _ = False

