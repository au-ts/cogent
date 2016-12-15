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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.Desugar where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core
import Cogent.PrettyPrint ()
import qualified Cogent.Surface as S
import qualified Cogent.TypeCheck.Base as B
import Cogent.Util
import Cogent.Vec as Vec

import Control.Applicative
import Control.Arrow ((&&&))
import Control.Lens
import Control.Monad.Reader hiding (forM)
import Control.Monad.RWS.Strict hiding (forM)
import Data.Char (ord)
-- import Data.Foldable
import Data.Function.Flippers (flip3)
import Data.List as L (elemIndex)
import Data.Map as M hiding (filter, map, (\\))
import Data.Maybe
import Data.Tuple.Select
import Prelude as P
import Data.Traversable (forM)
import Text.PrettyPrint.ANSI.Leijen (pretty)
-- import qualified Traversable as Trav (mapM)

-- import Debug.Trace

-- Desugar

noPos = __fixme S.noPos  -- FIXME! / zilinc

type TypeVars t = Vec t TyVarName
type TermVars v = Vec v VarName
type Typedefs   = M.Map TypeName ([VarName], S.RawType)  -- typenames |-> typeargs * strltype
type Constants  = M.Map VarName  B.TypedExpr  -- This shares namespace with `TermVars'
type Enumerator = Int

newtype DS (t :: Nat) (v :: Nat) a = DS { runDS :: RWS (Typedefs, Constants, [Pragma])
                                                       (Last (Typedefs, Constants, [CoreConst UntypedExpr]))  -- NOTE: it's a hack to export the reader! / zilinc
                                                       (TypeVars t, TermVars v, Enumerator)
                                                       a }
                                   deriving (Functor, Applicative, Monad,
                                             MonadReader (Typedefs, Constants, [Pragma]),
                                             MonadWriter (Last (Typedefs, Constants, [CoreConst UntypedExpr])),
                                             MonadState  (TypeVars t, TermVars v, Enumerator))

freshVarPrefix :: String
freshVarPrefix = "__ds_var_"

freshVar :: DS t v VarName
freshVar = P.head <$> freshVars 1

freshVars :: Int -> DS t v [VarName]
freshVars n = do x <- sel3 <$> get
                 modify (\(a,b,c) -> (a,b,c+n))
                 return $ P.map ((++) freshVarPrefix . show) $ take n (iterate (+1) x)

desugar :: [S.TopLevel S.RawType B.TypedPatn B.TypedExpr] -> [Pragma]
        -> ([Definition UntypedExpr VarName], Last (Typedefs, Constants, [CoreConst UntypedExpr]))
desugar tls pragmas =
  let fundefs    = filter isFunDef     tls where isFunDef     (S.FunDef   {})   = True; isFunDef     _ = False
      absdecs    = filter isAbsDec     tls where isAbsDec     (S.AbsDec   {})   = True; isAbsDec     _ = False
      typedecs   = filter isTypeDec    tls where isTypeDec    (S.TypeDec  {})   = True; isTypeDec    _ = False
      abstydecs  = filter isAbsTypeDec tls where isAbsTypeDec (S.AbsTypeDec {}) = True; isAbsTypeDec _ = False
      constdefs  = filter isConstDef   tls where isConstDef   (S.ConstDef {})   = True; isConstDef   _ = False
      initialReader = (M.fromList $ P.map fromTypeDec typedecs, M.fromList $ P.map fromConstDef constdefs, pragmas)
      initialState  = (Nil, Nil, 0)
  in flip3 evalRWS initialState initialReader $
       runDS (do defs' <- catMaybes <$> (mapM (\x -> put initialState >> desugarTopLevel x pragmas) $ abstydecs ++ typedecs ++ absdecs ++ fundefs)
                 write <- ask
                 consts' <- desugarConsts constdefs
                 tell $ Last (Just (write^._1, write^._2, consts'))
                 return defs'
             )
  where fromTypeDec  (S.TypeDec tn vs t) = (tn,(vs,t)); fromTypeDec  _ = __impossible "fromTypeDec (in desugarProgram)"
        fromConstDef (S.ConstDef vn t e) = (vn,e)     ; fromConstDef _ = __impossible "fromConstDef (in desguarProgram)"

withTypeBinding :: TyVarName -> DS ('Suc t) v a -> DS t v a
withTypeBinding t ds = do readers <- ask
                          (tenv,venv,enum) <- get
                          let (a, (_,_,enum'), _) = flip3 runRWS (Cons t tenv, venv, enum) readers $ runDS ds
                          put (tenv,venv,enum')
                          return a

withTypeBindings :: Vec k TyVarName -> DS (t :+: k) v a -> DS t v a
withTypeBindings Nil ds = ds
withTypeBindings (Cons x xs) ds = withTypeBindings xs (withTypeBinding x ds)

withBinding :: VarName -> DS t ('Suc v) a -> DS t v a
withBinding v ds = do readers <- ask
                      (tenv,venv,enum) <- get
                      let (a, (_,_,enum'), _) = flip3 runRWS (tenv, Cons v venv, enum) readers $ runDS ds
                      put (tenv,venv,enum')
                      return a

withBindings :: Vec k VarName -> DS t (v :+: k) x -> DS t v x
withBindings Nil ds = ds
withBindings (Cons x xs) ds = withBindings xs (withBinding x ds)

pragmaToAttr :: [Pragma] -> FunName -> Attr -> Attr
pragmaToAttr [] fn attr = attr
pragmaToAttr (CInlinePragma fn':pragmas) fn attr | fn == fn' = pragmaToAttr pragmas fn (attr <> Attr True False)
pragmaToAttr (_:pragmas) fn attr = pragmaToAttr pragmas fn attr

pragmaToNote :: [Pragma] -> FunName -> FunNote -> FunNote
pragmaToNote [] f note = note
pragmaToNote (InlinePragma  fn':pragmas) fn note | fn == fn' = max note InlineMe
pragmaToNote (FnMacroPragma fn':pragmas) fn note | fn == fn' = max note MacroCall
pragmaToNote (_:pragmas) fn note = pragmaToNote pragmas fn note

desugarTopLevel :: S.TopLevel S.RawType B.TypedPatn B.TypedExpr
                -> [Pragma]
                -> DS 'Zero 'Zero (Maybe (Definition UntypedExpr VarName))
desugarTopLevel (S.Include s) _ = __impossible "desugarTopLevel"
desugarTopLevel (S.IncludeStd s) _ = __impossible "desugarTopLevel"
desugarTopLevel (S.TypeDec tn vs t) _ | ExI (Flip vs') <- Vec.fromList vs
                                      , Vec.Refl <- zeroPlusNEqualsN (Vec.length vs') = do
  tenv <- use _1
  t' <- withTypeBindings vs' $ desugarType t
  return . Just $ TypeDef tn vs' (Just t')
desugarTopLevel (S.AbsTypeDec tn vs) _ | ExI (Flip vs') <- Vec.fromList vs = return . Just $ TypeDef tn vs' Nothing
desugarTopLevel (S.AbsDec ('_':_) _) _ | not __cogent_debug = return Nothing
desugarTopLevel (S.AbsDec fn sigma) pragmas | S.PT vs t <- sigma
                                            , ExI (Flip vs') <- Vec.fromList vs
                                            , Refl <- zeroPlusNEqualsN $ Vec.length vs'
  = do TFun ti' to' <- withTypeBindings (fmap fst vs') $ desugarType t
       return . Just $ AbsDecl (pragmaToAttr pragmas fn mempty) fn vs' ti' to'
desugarTopLevel (S.FunDef ('_':_) _ _) _ | not __cogent_debug = return Nothing
desugarTopLevel (S.FunDef fn sigma alts) pragmas | S.PT vs t <- sigma
                                                 , ExI (Flip vs') <- Vec.fromList vs
                                                 , Refl <- zeroPlusNEqualsN $ Vec.length vs'
  = withTypeBindings (fmap fst vs') $ do
      let (S.RT (S.TFun ti _)) = t
      TFun ti' to' <- desugarType t
      v <- freshVar
      let e0 = B.TE ti (S.Var v) noPos
      e <- if not __cogent_debug && P.head fn == '_'
              then return $ E Unit
              else withBinding v $ desugarAlts e0 alts
      return . Just $ FunDef (pragmaToAttr pragmas fn mempty) fn vs' ti' to' e
desugarTopLevel (S.ConstDef vn t e) _ = __impossible "desugarTopLevel"

desugarAlts :: B.TypedExpr -> [S.Alt B.TypedPatn B.TypedExpr] -> DS t v (UntypedExpr t v VarName)
desugarAlts e0 [] = __impossible "desugarAlts"
desugarAlts e0 [S.Alt p l e] = desugarAlt e0 p e  -- Note: Likelihood is ignored here / zilinc
                                                  --       This also serves as the base case for PCon
  -- Idea:
  --   Base case: e0 | (PCon tagname [p]) in e ~~> desugarAlt e0 (PCon tagname [p]) e
  --   Ind. step: A) e0 | (PCon tagname [PVar v1]) in e1; alts ==>
  --                 case e0 of tagname -> e1; e0' -> e0' | alts
  --              B) e0 | (PCon tagname [p]) in e; alts ==> e0 | (PCon tagname (PVar v)) in (let p = v in e); alts
  --              C) e0 | (PCon tagname ps) in e; alts ==> e0 | (PCon tagname [TTuple ps]) in e; alts
desugarAlts e0@(B.TE t v@(S.Var _) _) ((S.Alt (B.TP p1 pos1) l1 e1):alts) =  -- More than one Alt, which means the pattern cannot be IrrefPattern
  case p1 of
    S.PCon cn1 [B.TIP (S.PVar v1) _] -> do  -- this is A) for PCon
      e0' <- freshVar
      let S.RT (S.TVariant talts) = t
          t0' = S.RT $ S.TVariant (M.delete cn1 talts)  -- type of e0 without alternative cn
      e1' <- withBinding (fst v1) $ desugarExpr e1
      e2' <- withBinding e0' $ desugarAlts (B.TE t0' (S.Var e0') noPos) alts
      E <$> (Case <$> desugarExpr e0 <*> pure cn1 <*> pure (l1,fst v1,e1') <*> pure (mempty,e0',e2'))
    S.PCon cn1 [p1'] -> do  -- This is B) for PCon
      v1 <- freshVar
      let S.RT (S.TVariant talts) = t
          p1'' = B.TIP (S.PVar (v1,t1)) noPos
          Just ([t1], False)  = M.lookup cn1 talts  -- type of v1
          b   = S.Binding p1' Nothing (B.TE t1 (S.Var v1) noPos) []
          e1' = B.TE (B.getTypeTE e1) (S.Let [b] e1) noPos
      desugarAlts e0 ((S.Alt (B.TP (S.PCon cn1 [p1'']) pos1) l1 e1'):alts)
    S.PCon cn1 ps -> do  -- This is C) for PCon
      desugarAlts (B.TE t v noPos) ((S.Alt (B.TP (S.PCon cn1 [B.TIP (S.PTuple ps) (B.getLocTIP $ P.head ps)]) pos1) l1 e1):alts)
    S.PIntLit  i -> let pt = desugarPrimInt (B.getTypeTE e0)
                    in E <$> (If <$> (E <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [E $ ILit i pt])))
                                 <*> desugarExpr e1 <*> desugarAlts e0 alts)
    -- FIXME: could do better for PBoolLit because this one is easy to exhaust
    S.PBoolLit b -> E <$> (If <$> (E <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [E $ ILit (if b then 1 else 0) Boolean])))
                              <*> desugarExpr e1 <*> desugarAlts e0 alts)
    S.PCharLit c -> E <$> (If <$> (E <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [E $ ILit (fromIntegral $ ord c) U8])))
                              <*> desugarExpr e1 <*> desugarAlts e0 alts)
    S.PIrrefutable _ -> __impossible "desugarAlts"
desugarAlts e0 alts@((S.Alt _ _ e1):_) = do  -- e0 is not a var, so lift it
  v <- freshVar
  let t0 = B.getTypeTE e0
      t1 = B.getTypeTE e1
      b = S.Binding (B.TIP (S.PVar (v,t0)) noPos) Nothing e0 []
      m = B.TE t1 (S.Match (B.TE t0 (S.Var v) noPos) [] alts) noPos
  desugarExpr $ B.TE t1 (S.Let [b] m) noPos

desugarAlt :: B.TypedExpr -> B.TypedPatn -> B.TypedExpr -> DS t v (UntypedExpr t v VarName)
desugarAlt e0 (B.TP p pos) e = desugarAlt' e0 p e

-- FIXME: this function should take a position
desugarAlt' :: B.TypedExpr -> S.Pattern B.TypedIrrefPatn -> B.TypedExpr -> DS t v (UntypedExpr t v VarName)
desugarAlt' e0 (S.PCon tag [B.TIP (S.PVar tn) _]) e =
  E <$> (Let (fst tn) <$> (E <$> Esac <$> desugarExpr e0) <*> withBinding (fst tn) (desugarExpr e))
  -- Idea:
  --   Base case: e0 | PCon cn [PVar v] in e ~~> let v = esac e0 in e
  --   Ind. step: A) e0 | PCon vn [p] in e ==> e0 | PCon cn [PVar v] in (let p = v in e)
  --              B) e0 | PCon vn ps  in e ==> e0 | PCon vn [PTuple ps] in e
desugarAlt' e0 (S.PCon tag [p]) e = do  -- Ind. step A)
  v <- freshVar
  let S.RT (S.TVariant alts) = B.getTypeTE e0
      Just ([t], False) = M.lookup tag alts
      -- b0 = S.Binding (S.PVar (v,t)) Nothing (B.TE t $ Esac e0) []
      b1 = S.Binding p Nothing (B.TE t (S.Var v) noPos) []
  -- desugarExpr $ B.TE (B.getTypeTE e) $ S.Let [b0,b1] e
      e' = B.TE (B.getTypeTE e) (S.Let [b1] e) noPos
  desugarAlt' e0 (S.PCon tag [B.TIP (S.PVar (v,t)) noPos]) e'
desugarAlt' (B.TE t e0 l) (S.PCon tag []) e =  -- Ind. B1)
  desugarAlt' (B.TE t e0 l) (S.PCon tag [B.TIP S.PUnitel noPos]) e
desugarAlt' (B.TE t e0 l) (S.PCon tag ps) e =  -- B2)
  -- FIXME: zilinc
  desugarAlt' (B.TE t e0 l) (S.PCon tag [B.TIP (S.PTuple ps) (B.getLocTIP $ P.head ps)]) e
                                                          -- At this point, t and e0 do not match!
                                                          -- but hopefully they will after e0 gets desugared

desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PVar v) _)) e =
  E <$> (Let (fst v) <$> desugarExpr e0 <*> (withBinding (fst v) $ desugarExpr e))
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTuple []) _)) e = __impossible "desugarAlt' (Tuple-1)"
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTuple [irf]) _)) e = __impossible "desugarAlt' (Tuple-2)"
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTuple [B.TIP (S.PVar tn1) _, B.TIP (S.PVar tn2) _]) _)) e
  | not __cogent_ftuples_as_sugar =
  -- NOTE: This does not work! / zilinc
  --   XXX | Idea: (p0,p1) = e0 in e ==> split (v0,v1) = e0 in let p1 = v0 and p0' = v0 and p1' = v1 in e
  --   XXX | vns <- freshVars $ P.length ps
  --   XXX | let S.RT (S.TTuple ts) = B.getTypeTE e0
  --   XXX |     pvs = P.zipWith (curry $ S.PVar) vns ts
  --   XXX |     vs  = P.zipWith (\t v -> B.TE t $ S.Var v) ts vns
  --   XXX |     b0 = S.Binding (S.PTuple pvs) Nothing e0 []
  --   XXX |     bs = P.zipWith (\p v -> S.Binding p Nothing v []) ps vs
  --   XXX | desugarExpr (B.TE (B.getTypeTE e) $ S.Let (b0:bs) e)
  -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  -- Idea: PTuple ps = e0 in e
  --   Base case: PTuple [PVar v1, PVar v2] = e0 in e ~~>
  --              Split (x,y) = e0 in e
  --   Ind. step: A) PTuple [p1,p2] = e0 in e ==>
  --                 let PTuple [PVar v1, PVar v2] = e0
  --                 and p1 = v1 and p2 = v2 in e
  --              B) PTuple (p1:p2:ps) = e0 in e ==>
  --                 PTuple [p1, PTuple (p2:ps)] = e0 in e
  E <$> (Split (fst tn1, fst tn2) <$> desugarExpr e0 <*> (withBindings (Cons (fst tn1) (Cons (fst tn2) Nil)) $ desugarExpr e))
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTuple [p1,p2]) _)) e | not __cogent_ftuples_as_sugar = do
  v1 <- freshVar
  v2 <- freshVar
  let S.RT (S.TTuple [t1,t2]) = B.getTypeTE e0
      b0 = S.Binding (B.TIP (S.PTuple [B.TIP (S.PVar (v1,t1)) noPos, B.TIP (S.PVar (v2,t2)) noPos]) noPos) Nothing e0 []
      b1 = S.Binding p1 Nothing (B.TE t1 (S.Var v1) (B.getLocTIP p1)) []
      b2 = S.Binding p2 Nothing (B.TE t2 (S.Var v2) (B.getLocTIP p2)) []
  desugarExpr $ B.TE (B.getTypeTE e) (S.Let [b0,b1,b2] e) noPos  -- Mutual recursion here
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTuple (p1:p2:ps)) _)) e  | not __cogent_ftuples_as_sugar = __impossible "desugarAlt'"
  -- let p' = S.PIrrefutable $ S.PTuple [p1, p2']
  --     p2' = S.PTuple $ p2:ps
  -- in desugarAlt' e0 p' e
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTuple ps) _)) e | __cogent_ftuples_as_sugar, and (P.map isPVar ps) = do
  -- Idea: PTuple ps = e0 in e
  --   Base case: PTuple [PVar v1, PVar v2, ..., PVar vn] = e0 in e ~~>
  --              let e0'' = e0' {p1=v1, ..., pn=vn} in e'  -- nested take's in sugarfree
  --   Ind. step: PTuple ps = e0 in e ==>
  --              let (v1, ..., vn) = e0
  --              and p1 = v1
  --              ...
  --              and pn = vn
  --              in e  -- The implemention is optimised so that PVars in ps don't need to assign to new vars again
  e0' <- desugarExpr e0
  let vs = P.map (fst . getPVar) ps
  mkTake e0' vs e 0
  where isPVar (B.TIP (S.PVar _) _) = True; isPVar _ = False
        getPVar (B.TIP (S.PVar v) _) = v; getPVar _ = __impossible "getPVar (in desugarAlt')"
        mkTake :: UntypedExpr t v VarName -> [VarName] -> B.TypedExpr -> Int -> DS t v (UntypedExpr t v VarName)
        mkTake _ [] _ _ = __impossible "mkTake (in desugarAlt')"
        mkTake e0 [v] e idx = do
          e0' <- freshVar
          E . Take (v,e0') e0 idx <$> withBindings (Cons v (Cons e0' Nil)) (desugarExpr e)
        mkTake e0 (v:vs) e idx = do
          e0' <- freshVar
          E . Take (v,e0') e0 idx <$> withBindings (Cons v (Cons e0' Nil)) (mkTake (E $ Variable (f1, e0')) vs e (idx + 1))
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTuple ps) _)) e | __cogent_ftuples_as_sugar = do
  let S.RT (S.TTuple ts) = B.getTypeTE e0
  __assert (P.length ps == P.length ts) $ "desugarAlt': |ps| /= |ts|\nps = " ++ show ps ++ "\nts = " ++ show ts
  let pts = P.zip ps ts
  vpts <- forM pts $ \(p,t) -> case p of B.TIP (S.PVar (v,_)) _ -> return (v,p,t); _ -> (,p,t) <$> freshVar
  let vpts' = P.filter (not . isPVar . sel2) vpts
      b0 = S.Binding (B.TIP (S.PTuple $ flip P.map vpts (\(v,p,t) -> B.TIP (S.PVar (v,t)) (B.getLocTIP p))) noPos) Nothing e0 []
      bs = flip P.map vpts' $ \(v,p,t) -> S.Binding p Nothing (B.TE t (S.Var v) noPos) []
  desugarExpr $ B.TE (B.getTypeTE e) (S.Let (b0:bs) e) noPos
  where isPVar (B.TIP (S.PVar _) _) = True; isPVar _ = False
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PUnboxedRecord fs) pos)) e = do
  -- #{a, b, c} ~~> x {a,b,c}  -- since we take all the fields out, the unboxed x is useless and can be discarded
  rec <- (, B.getTypeTE e0) <$> freshVar
  desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTake rec fs) pos)) e
desugarAlt' e0 (S.PIrrefutable (B.TIP S.PUnderscore _)) e = do
  v <- freshVar
  E <$> (Let v <$> desugarExpr e0 <*> withBinding v (desugarExpr e))
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PUnitel) pos)) e = desugarAlt' e0 (S.PIrrefutable $ B.TIP S.PUnderscore pos) e
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTake rec []) pos)) e = desugarAlt' e0 (S.PIrrefutable $ B.TIP (S.PVar rec) pos) e
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTake rec [Nothing]) _)) e = __impossible "desugarAlt'"
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTake rec [Just (f, B.TIP (S.PVar v) _)]) _)) e =
  -- Idea:
  --   Base case: e0 | rec {f = PVar v} in e ~~> Take f' (rec,v) = e0 in e
  --   Ind. step: A) e0 | rec {f = p} in e ==> let rec {f = PVar v} = e0 and p = v in e
  --              B) e0 | rec (fp:fps) in e ==> let e1 {f = p} = e0 and rec = e1 {fps} in e
  desugarType (B.getTypeTE e0) >>= \(TRecord fs _) -> let Just fldIdx = elemIndex f (P.map fst fs) in
  E <$> (Take (fst v, fst rec) <$> desugarExpr e0 <*> pure fldIdx <*> (withBindings (Cons (fst v) (Cons (fst rec) Nil)) $ desugarExpr e))
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTake rec [Just (f,p)]) pos)) e = do
  v <- freshVar
  let S.RT (S.TRecord fts s) = snd rec
      Just (ft,_) = P.lookup f fts  -- the type of the taken field
      b1 = S.Binding (B.TIP (S.PTake rec [Just (f, B.TIP (S.PVar (v,ft)) noPos)]) pos) Nothing e0 []
      b2 = S.Binding p Nothing (B.TE ft (S.Var v) noPos) []  -- FIXME: someone wrote "wrong!" here. Why? check!
  desugarExpr $ B.TE (B.getTypeTE e) (S.Let [b1,b2] e) noPos
desugarAlt' e0 (S.PIrrefutable (B.TIP (S.PTake rec (fp:fps)) pos)) e = do
  e1 <- freshVar
  let S.RT (S.TRecord fts s) = snd rec
      t1 = S.RT $ S.TRecord (P.map (\ft@(f,(t,x)) -> if f == fst (fromJust fp) then (f,(t,True)) else ft) fts) s  -- type of e1
      b0 = S.Binding (B.TIP (S.PTake (e1, t1) [fp]) noPos) Nothing e0 []
      bs = S.Binding (B.TIP (S.PTake rec fps) pos) Nothing (B.TE t1 (S.Var e1) noPos) []
  desugarExpr $ B.TE (B.getTypeTE e) (S.Let [b0,bs] e) noPos
desugarAlt' _ _ _ = __impossible "desugarAlt' (_)"  -- literals

desugarPrimInt :: S.RawType -> PrimInt
desugarPrimInt (S.RT (S.TCon "U8"   [] Unboxed)) = U8
desugarPrimInt (S.RT (S.TCon "U16"  [] Unboxed)) = U16
desugarPrimInt (S.RT (S.TCon "U32"  [] Unboxed)) = U32
desugarPrimInt (S.RT (S.TCon "U64"  [] Unboxed)) = U64
desugarPrimInt (S.RT (S.TCon "Bool" [] Unboxed)) = Boolean
desugarPrimInt _ = __impossible "desugarPrimInt"

desugarType :: S.RawType -> DS t v (Type t)
desugarType = \case
  S.RT (S.TCon "U8"     [] Unboxed) -> return $ TPrim U8
  S.RT (S.TCon "U16"    [] Unboxed) -> return $ TPrim U16
  S.RT (S.TCon "U32"    [] Unboxed) -> return $ TPrim U32
  S.RT (S.TCon "U64"    [] Unboxed) -> return $ TPrim U64
  S.RT (S.TCon "Bool"   [] Unboxed) -> return $ TPrim Boolean
  S.RT (S.TCon "Char"   [] Unboxed) -> return $ TPrim U8
  S.RT (S.TCon "String" [] Unboxed) -> return $ TString
  S.RT (S.TCon tn tvs s) -> TCon tn <$> mapM desugarType tvs <*> pure s
  S.RT (S.TVar vn b)     -> (findIx vn <$> sel1 <$> get) >>= \(Just v) -> return $ if b then TVarBang v else TVar v
  S.RT (S.TFun ti to)    -> TFun <$> desugarType ti <*> desugarType to
  S.RT (S.TRecord fs s)  -> TRecord <$> mapM (\(f,(t,x)) -> (f,) . (,x) <$> desugarType t) fs <*> pure s
  S.RT (S.TVariant alts) -> TSum <$> mapM (\(c,(ts,x)) -> (c,) . (,x) <$> desugarType (group ts)) (M.toList alts)
    where group [] = S.RT S.TUnit
          group (t:[]) = t
          group ts = S.RT $ S.TTuple ts
  S.RT (S.TTuple [])     -> __impossible "desugarType (TTuple 0)"
  S.RT (S.TTuple (t:[])) -> __impossible "desugarType (TTuple 1)"
  S.RT (S.TTuple (t1:t2:[])) | not __cogent_ftuples_as_sugar -> TProduct <$> desugarType t1 <*> desugarType t2
  S.RT (S.TTuple (t1:t2:ts)) | not __cogent_ftuples_as_sugar -> __impossible "desugarType"  -- desugarType $ S.RT $ S.TTuple [t1, S.RT $ S.TTuple (t2:ts)]
  S.RT (S.TTuple ts) | __cogent_ftuples_as_sugar -> TRecord <$> (P.zipWith (\t n -> (n,(t, False))) <$> forM ts desugarType <*> pure (P.map (('p':) . show) [1 :: Integer ..])) <*> pure Unboxed
  S.RT (S.TUnit)   -> return TUnit
  notInWHNF -> __impossible' "desugarType" ("type" : lines (show (pretty notInWHNF)) ++ ["is not in WHNF"])

desugarNote :: S.Inline -> FunNote
desugarNote S.NoInline = NoInline
desugarNote S.Inline   = InlinePlease

desugarExpr :: B.TypedExpr -> DS t v (UntypedExpr t v VarName)
desugarExpr (B.TE _ (S.PrimOp opr es) _) = E . Op (symbolOp opr) <$> mapM desugarExpr es
desugarExpr (B.TE _ (S.Var vn) _) = (findIx vn . sel2 <$> get) >>= \case
  Just v  -> return $ E $ Variable (v, vn)
  Nothing -> do constdefs <- view _2
                let Just e = M.lookup vn constdefs
                desugarExpr e
desugarExpr (B.TE _ (S.Match e _ []) _) = __impossible "desugarExpr (Match)"
desugarExpr (B.TE _ (S.Match e [] alts) _) = desugarAlts e alts
desugarExpr (B.TE _ (S.Match e vs alts) l) = do
  -- Idea: e !vs | alts ~~> let v = e !vs in desugarAlt (v, alts)
  -- FIXME: Not sure if this is going to work / zilinc
  venv <- use _2
  v <- freshVar
  let vs' = P.map (fromJust . flip findIx venv &&& id) vs
  e' <- withBinding v $ desugarAlts (B.TE (B.getTypeTE e) (S.Var v) l) alts
  E <$> (LetBang vs' v <$> desugarExpr e <*> pure e')
desugarExpr (B.TE _ (S.TypeApp v ts note) _) = do
  pragmas <- view _3
  E <$> (Fun v <$> mapM desugarType (map fromJust ts) <*> pure (pragmaToNote pragmas v $ desugarNote note))  -- FIXME: fromJust
desugarExpr (B.TE _ (S.Con c []) _) = return . E $ Con c (E Unit)
desugarExpr (B.TE _ (S.Con c [e]) _) = E . Con c <$> desugarExpr e
desugarExpr (B.TE (S.RT (S.TVariant ts)) (S.Con c es) l) = do
    let Just (tes, k) = M.lookup c ts  -- TODO liamoc just added ,k to make this compile
    E . Con c <$> desugarExpr (B.TE (group tes) (S.Tuple es) l)
  where group [] = S.RT S.TUnit
        group (t:[]) = t
        group ts = S.RT $ S.TTuple ts
desugarExpr (B.TE _ (S.Seq e1 e2) _) = do
  v <- freshVar
  E <$> (Let v <$> desugarExpr e1 <*> withBinding v (desugarExpr e2))
desugarExpr (B.TE _ (S.App (B.TE _ (S.TypeApp ('_':_) _ _) _) _) _) | not __cogent_debug = return (E Unit)
desugarExpr (B.TE _ (S.App e1 e2) _) = E <$> (App <$> desugarExpr e1 <*> desugarExpr e2)
desugarExpr (B.TE _ (S.If c [] th el) _) = E <$> (If <$> desugarExpr c <*> desugarExpr th <*> desugarExpr el)
desugarExpr (B.TE _ (S.If c vs th el) _) = do
  venv <- use _2
  v <- freshVar
  let vs' = P.map (fromJust . flip findIx venv &&& id) vs
  th' <- withBinding v $ desugarExpr th
  el' <- withBinding v $ desugarExpr el
  let e' = E $ If (E $ Variable (f0, v)) th' el'
  E <$> (LetBang vs' v <$> desugarExpr c <*> pure e')
desugarExpr (B.TE _ (S.Member e fld) _) = do
  TRecord fs _ <- desugarType $ B.getTypeTE e
  let Just f' = elemIndex fld (P.map fst fs)
  E <$> (Member <$> desugarExpr e <*> pure f')
desugarExpr (B.TE _ (S.Unitel) _) = return $ E Unit
desugarExpr (B.TE t (S.IntLit n) _) = return $ E . ILit n $ desugarPrimInt t
desugarExpr (B.TE _ (S.BoolLit b) _) = return $ E $ ILit (if b then 1 else 0) Boolean
desugarExpr (B.TE _ (S.CharLit c) _) = return $ E $ ILit (fromIntegral $ ord c) U8
desugarExpr (B.TE _ (S.StringLit s) _) = return $ E $ SLit s
desugarExpr (B.TE _ (S.Tuple []) _) = __impossible "desugarExpr (Tuple)"
desugarExpr (B.TE _ (S.Tuple [e]) _) = __impossible "desugarExpr (Tuple)"
desugarExpr (B.TE _ (S.Tuple (e1:e2:[])) _) | not __cogent_ftuples_as_sugar = E <$> (Tuple <$> desugarExpr e1 <*> desugarExpr e2)
desugarExpr (B.TE t (S.Tuple (e1:e2:es)) _) | not __cogent_ftuples_as_sugar = __impossible "desugarExpr"  -- do
  -- S.RT (S.TTuple (t1:t2:ts)) <- typeWHNF t
  -- let t2' = S.RT $ S.TTuple (t2:ts)
  --     e2' = B.TE t2' $ S.Tuple (e2:es)
  -- desugarExpr $ B.TE (S.RT $ S.TTuple [t1,t2']) $ S.Tuple [e1,e2']
-- desugarExpr (B.TE _ (S.Tuple (reverse -> (e:es)))) | B.TE _ (S.Tuple _) <- e = __impossible "desugarExpr"
desugarExpr (B.TE _ (S.Tuple es) _) = E . Struct <$> (P.zip (P.map (('p':) . show) [1 :: Integer ..]) <$> mapM desugarExpr es)  -- | __cogent_ftuples_as_sugar
desugarExpr (B.TE _ (S.UnboxedRecord fs) _) = E . Struct <$> mapM (\(f,e) -> (f,) <$> desugarExpr e) fs
desugarExpr (B.TE _ (S.Let [] e) _) = __impossible "desugarExpr (Let)"
desugarExpr (B.TE _ (S.Let [S.Binding p mt e0 []] e) _) = desugarAlt' e0 (S.PIrrefutable p) e
desugarExpr (B.TE _ (S.Let [S.Binding (B.TIP (S.PVar v) _) mt e0 bs] e) _) = do
  -- Idea:
  --   Base case: let v = e0 !bs in e ~~> let! bs e0 e
  --   Ind. step: A) let p = e0 !bs in e ==> let v = e0 !bs and p = v in e
  --              B) let p1=e1 !bs1; ps=es !bss in e ==> let p1 = e1 !bs1 in let ps=es !bss in e
  venv <- use _2
  let bs' = P.map (fromJust . flip findIx venv &&& id) bs
  E <$> (LetBang bs' (fst v) <$> desugarExpr e0 <*> withBinding (fst v) (desugarExpr e))
desugarExpr (B.TE t (S.Let [S.Binding p mt e0 bs] e) l) = do
  v <- freshVar
  let t0 = B.getTypeTE e0
      b0 = S.Binding (B.TIP (S.PVar (v,t0)) noPos) Nothing e0 bs
      b1 = S.Binding p mt (B.TE t0 (S.Var v) l) []
  desugarExpr $ B.TE t (S.Let [b0,b1] e) l
desugarExpr (B.TE t (S.Let (b:bs) e) l) = desugarExpr $ B.TE t (S.Let [b] e') l
  where e' = B.TE t (S.Let bs e) l
desugarExpr (B.TE _ (S.Put e []) _) = desugarExpr e
desugarExpr (B.TE t (S.Put e [Nothing]) _) = __impossible "desugarExpr (Put)"
desugarExpr (B.TE t (S.Put e [Just (f,a)]) _) = do
  TRecord fs _ <- desugarType t
  let Just f' = elemIndex f (P.map fst fs)
  E <$> (Put <$> desugarExpr e <*> pure f' <*> desugarExpr a)
desugarExpr (B.TE t (S.Put e (fa@(Just (f0,_)):fas)) l) = do
  let S.RT (S.TRecord fs s) = t
      fs' = map (\ft@(f,(t,b)) -> if f == f0 then (f,(t,False)) else ft) fs
      t' = S.RT (S.TRecord fs' s)
  desugarExpr $ B.TE t (S.Put (B.TE t' (S.Put e [fa]) l) fas) l
desugarExpr (B.TE t (S.Upcast e) _) = E <$> (Promote <$> desugarType t <*> desugarExpr e)
-- desugarExpr (B.TE t (S.Widen  e) _) = E <$> (Promote <$> desugarType t <*> desugarExpr e)


desugarConst :: (VarName, B.TypedExpr) -> DS 'Zero 'Zero (CoreConst UntypedExpr)
desugarConst (n,e) = (n,) <$> desugarExpr e

-- NOTE: aseume the first arguments consists of constants only
desugarConsts :: [S.TopLevel S.RawType B.TypedPatn B.TypedExpr] -> DS 'Zero 'Zero [CoreConst UntypedExpr]
desugarConsts = mapM desugarConst . P.map (\(S.ConstDef v _ e) -> (v,e))

