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
import Cogent.Sugarfree hiding (withBinding, withBindings)
import qualified Cogent.Surface as S
import qualified Cogent.TypeCheck.Base as B
import Cogent.Util
import Cogent.Vec as Vec
import Control.Applicative
import Control.Arrow (first, second, (&&&))
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
-- import qualified Traversable as Trav (mapM)

-- import Debug.Trace

-- Desugar

type TypeVars t = Vec t TyVarName
type TermVars v = Vec v VarName
type Typedefs   = M.Map TypeName ([VarName], S.RawType)  -- typenames |-> typeargs * strltype
type Constants  = M.Map VarName  B.TypedExpr  -- This shares namespace with `TermVars'
type Enumerator = Int

newtype DS (t :: Nat) (v :: Nat) a = DS { runDS :: RWS (Typedefs, Constants, [Pragma])
                                                       (Last (Typedefs, Constants, [SFConst UntypedExpr]))  -- NOTE: it's a hack to export the reader! / zilinc
                                                       (TypeVars t, TermVars v, Enumerator)
                                                       a }
                                   deriving (Functor, Applicative, Monad,
                                             MonadReader (Typedefs, Constants, [Pragma]),
                                             MonadWriter (Last (Typedefs, Constants, [SFConst UntypedExpr])),
                                             MonadState  (TypeVars t, TermVars v, Enumerator))

freshVarPrefix :: String
freshVarPrefix = "__ds_var_"

freshVar :: DS t v VarName
freshVar = P.head <$> freshVars 1

freshVars :: Int -> DS t v [VarName]
freshVars n = do x <- sel3 <$> get
                 modify (\(a,b,c) -> (a,b,c+n))
                 return $ P.map ((++) freshVarPrefix . show) $ take n (iterate (+1) x)

desugar :: [S.TopLevel S.RawType B.TypedName B.TypedExpr] -> [Pragma]
        -> ([Definition UntypedExpr VarName], Last (Typedefs, Constants, [SFConst UntypedExpr]))
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

desugarTopLevel :: S.TopLevel S.RawType B.TypedName B.TypedExpr
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
      TFun ti' to' <- desugarType t
      S.RT (S.TFun ti _) <- typeWHNF t
      v <- freshVar
      let e0 = B.TE ti $ S.Var v
      e <- if not __cogent_debug && P.head fn == '_'
              then return $ E Unit
              else withBinding v $ desugarAlts e0 alts
      return . Just $ FunDef (pragmaToAttr pragmas fn mempty) fn vs' ti' to' e
desugarTopLevel (S.ConstDef vn t e) _ = __impossible "desugarTopLevel"

desugarAlts :: B.TypedExpr -> [S.Alt B.TypedName B.TypedExpr] -> DS t v (UntypedExpr t v VarName)
desugarAlts e0 [] = __impossible "desugarAlts"
desugarAlts e0 [S.Alt p l e] = desugarAlt e0 p e  -- Note: Likelihood is ignored here / zilinc
                                                  --       This also serves as the base case for PCon
  -- Idea:
  --   Base case: e0 | (PCon tagname [p]) in e ~~> desugarAlt e0 (PCon tagname [p]) e
  --   Ind. step: A) e0 | (PCon tagname [PVar v1]) in e1; alts ==>
  --                 case e0 of tagname -> e1; e0' -> e0' | alts
  --              B) e0 | (PCon tagname [p]) in e; alts ==> e0 | (PCon tagname (PVar v)) in (let p = v in e); alts
  --              C) e0 | (PCon tagname ps) in e; alts ==> e0 | (PCon tagname [TTuple ps]) in e; alts
desugarAlts e0@(B.TE t v@(S.Var _)) ((S.Alt p1 l1 e1):alts) =  -- More than one Alt, which means the pattern cannot be IrrefPattern
  case p1 of
    S.PCon cn1 [S.PVar v1] -> do  -- this is A) for PCon
      e0' <- freshVar
      S.RT (S.TVariant talts) <- typeWHNF t
      let t0' = S.RT $ S.TVariant (M.delete cn1 talts)  -- type of e0 without alternative cn
      e1' <- withBinding (fst v1) $ desugarExpr e1
      e2' <- withBinding e0' $ desugarAlts (B.TE t0' $ S.Var e0') alts
      E <$> (Case <$> desugarExpr e0 <*> pure cn1 <*> pure (l1,fst v1,e1') <*> pure (mempty,e0',e2'))
    S.PCon cn1 [p1'] -> do  -- This is B) for PCon
      v1 <- freshVar
      S.RT (S.TVariant talts) <- typeWHNF t
      let p1'' = S.PVar (v1,t1)
          Just [t1]  = M.lookup cn1 talts  -- type of v1
          b   = S.Binding p1' Nothing (B.TE t1 $ S.Var v1) []
          e1' = B.TE (B.getType e1) $ S.Let [b] e1
      desugarAlts e0 ((S.Alt (S.PCon cn1 [p1'']) l1 e1'):alts)
    S.PCon cn1 ps -> do  -- This is C) for PCon
      t' <- typeWHNF t
      desugarAlts (B.TE t' v) ((S.Alt (S.PCon cn1 [S.PTuple ps]) l1 e1):alts)
    S.PIntLit  i -> desugarPrimInt <$> typeWHNF (B.getType e0) >>= \pt ->
                    E <$> (If <$> (E <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [E $ ILit i pt])))
                              <*> desugarExpr e1 <*> desugarAlts e0 alts)
    -- FIXME: could do better for PBoolLit because this one is easy to exhaust
    S.PBoolLit b -> E <$> (If <$> (E <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [E $ ILit (if b then 1 else 0) Boolean])))
                              <*> desugarExpr e1 <*> desugarAlts e0 alts)
    S.PCharLit c -> E <$> (If <$> (E <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [E $ ILit (fromIntegral $ ord c) U8])))
                              <*> desugarExpr e1 <*> desugarAlts e0 alts)
    S.PIrrefutable _ -> __impossible "desugarAlts"
desugarAlts e0 alts@((S.Alt _ _ e1):_) = do  -- e0 is not a var, so lift it
  v <- freshVar
  let t0 = B.getType e0
      t1 = B.getType e1
      b = S.Binding (S.PVar (v,t0)) Nothing e0 []
      m = B.TE t1 $ S.Match (B.TE t0 $ S.Var v) [] alts
  desugarExpr $ B.TE t1 (S.Let [b] m)

desugarAlt :: B.TypedExpr -> S.Pattern B.TypedName -> B.TypedExpr -> DS t v (UntypedExpr t v VarName)
desugarAlt e0 (S.PCon tag [S.PVar tn]) e =
  E <$> (Let (fst tn) <$> (E <$> Esac <$> desugarExpr e0) <*> withBinding (fst tn) (desugarExpr e))
  -- Idea:
  --   Base case: e0 | PCon cn [PVar v] in e ~~> let v = esac e0 in e
  --   Ind. step: A) e0 | PCon vn [p] in e ==> e0 | PCon cn [PVar v] in (let p = v in e)
  --              B) e0 | PCon vn ps  in e ==> e0 | PCon vn [PTuple ps] in e
desugarAlt e0 (S.PCon tag [p]) e = do  -- Ind. step A)
  v <- freshVar
  S.RT (S.TVariant alts) <- typeWHNF $ B.getType e0
  let Just [t] = M.lookup tag alts
      -- b0 = S.Binding (S.PVar (v,t)) Nothing (B.TE t $ Esac e0) []
      b1 = S.Binding p Nothing (B.TE t (S.Var v)) []
  -- desugarExpr $ B.TE (B.getType e) $ S.Let [b0,b1] e
  let e' = B.TE (B.getType e) $ S.Let [b1] e
  desugarAlt e0 (S.PCon tag [S.PVar (v,t)]) e'
desugarAlt (B.TE t e0) (S.PCon tag []) e = do  -- Ind. B1)
  t' <- typeWHNF t
  desugarAlt (B.TE t' e0) (S.PCon tag [S.PUnitel]) e
desugarAlt (B.TE t e0) (S.PCon tag ps) e = do  -- B2)
  t' <- typeWHNF t
  -- FIXME: zilinc
  desugarAlt (B.TE t' e0) (S.PCon tag [S.PTuple ps]) e  -- At this point, t' and e0 do not match!
                                                        -- but hopefully they will after e0 gets desugared

desugarAlt e0 (S.PIrrefutable (S.PVar v)) e = E <$> (Let (fst v) <$> desugarExpr e0 <*> (withBinding (fst v) $ desugarExpr e))
desugarAlt e0 (S.PIrrefutable (S.PTuple [])) e = __impossible "desugarAlt (Tuple-1)"
desugarAlt e0 (S.PIrrefutable (S.PTuple [irf])) e = __impossible "desugarAlt (Tuple-2)"
desugarAlt e0 (S.PIrrefutable (S.PTuple [S.PVar tn1, S.PVar tn2])) e | not __cogent_ftuples_as_sugar =
  -- NOTE: This does not work! / zilinc
  --   XXX | Idea: (p0,p1) = e0 in e ==> split (v0,v1) = e0 in let p1 = v0 and p0' = v0 and p1' = v1 in e
  --   XXX | vns <- freshVars $ P.length ps
  --   XXX | let S.RT (S.TTuple ts) = B.getType e0
  --   XXX |     pvs = P.zipWith (curry $ S.PVar) vns ts
  --   XXX |     vs  = P.zipWith (\t v -> B.TE t $ S.Var v) ts vns
  --   XXX |     b0 = S.Binding (S.PTuple pvs) Nothing e0 []
  --   XXX |     bs = P.zipWith (\p v -> S.Binding p Nothing v []) ps vs
  --   XXX | desugarExpr (B.TE (B.getType e) $ S.Let (b0:bs) e)
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
desugarAlt e0 (S.PIrrefutable (S.PTuple [p1,p2])) e | not __cogent_ftuples_as_sugar = do
  v1 <- freshVar
  v2 <- freshVar
  S.RT (S.TTuple [t1,t2]) <- typeWHNF $ B.getType e0
  let b0 = S.Binding (S.PTuple [S.PVar (v1,t1), S.PVar (v2,t2)]) Nothing e0 []
      b1 = S.Binding p1 Nothing (B.TE t1 $ S.Var v1) []
      b2 = S.Binding p2 Nothing (B.TE t2 $ S.Var v2) []
  desugarExpr $ B.TE (B.getType e) $ S.Let [b0,b1,b2] e  -- Mutual recursion here
desugarAlt e0 (S.PIrrefutable (S.PTuple (p1:p2:ps))) e  | not __cogent_ftuples_as_sugar = __impossible "desugarAlt"
  -- let p' = S.PIrrefutable $ S.PTuple [p1, p2']
  --     p2' = S.PTuple $ p2:ps
  -- in desugarAlt e0 p' e
desugarAlt e0 (S.PIrrefutable (S.PTuple ps)) e | __cogent_ftuples_as_sugar, and (P.map isPVar ps) = do
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
  where isPVar (S.PVar _) = True; isPVar _ = False
        getPVar (S.PVar v) = v; getPVar _ = __impossible "getPVar (in desugarAlt)"
        mkTake :: UntypedExpr t v VarName -> [VarName] -> B.TypedExpr -> Int -> DS t v (UntypedExpr t v VarName)
        mkTake _ [] _ _ = __impossible "mkTake (in desugarAlt)"
        mkTake e0 [v] e idx = do
          e0' <- freshVar
          E . Take (v,e0') e0 idx <$> withBindings (Cons v (Cons e0' Nil)) (desugarExpr e)
        mkTake e0 (v:vs) e idx = do
          e0' <- freshVar
          E . Take (v,e0') e0 idx <$> withBindings (Cons v (Cons e0' Nil)) (mkTake (E $ Variable (f1, e0')) vs e (idx + 1))
desugarAlt e0 (S.PIrrefutable (S.PTuple ps)) e | __cogent_ftuples_as_sugar = do
  S.RT (S.TTuple ts) <- typeWHNF $ B.getType e0
  __assert (P.length ps == P.length ts) $ "desugarAlt: |ps| /= |ts|\nps = " ++ show ps ++ "\nts = " ++ show ts
  let pts = P.zip ps ts
  vpts <- forM pts $ \(p,t) -> case p of S.PVar (v,_) -> return (v,p,t); _ -> (,p,t) <$> freshVar
  let vpts' = P.filter (not . isPVar . sel2) vpts
      b0 = S.Binding (S.PTuple $ flip P.map vpts (\(v,p,t) -> S.PVar (v,t))) Nothing e0 []
      bs = flip P.map vpts' $ \(v,p,t) -> S.Binding p Nothing (B.TE t $ S.Var v) []
  desugarExpr $ B.TE (B.getType e) $ S.Let (b0:bs) e
  where isPVar (S.PVar _) = True; isPVar _ = False
desugarAlt e0 (S.PIrrefutable (S.PUnboxedRecord fs)) e = do
  -- #{a, b, c} ~~> x {a,b,c}  -- since we take all the fields out, the unboxed x is useless and can be discarded
  rec <- (, B.getType e0) <$> freshVar
  desugarAlt e0 (S.PIrrefutable (S.PTake rec fs)) e
desugarAlt e0 (S.PIrrefutable (S.PUnderscore)) e = do
  v <- freshVar
  E <$> (Let v <$> desugarExpr e0 <*> withBinding v (desugarExpr e))
desugarAlt e0 (S.PIrrefutable (S.PUnitel)) e = desugarAlt e0 (S.PIrrefutable S.PUnderscore) e
desugarAlt e0 (S.PIrrefutable (S.PTake rec [])) e = desugarAlt e0 (S.PIrrefutable (S.PVar rec)) e
desugarAlt e0 (S.PIrrefutable (S.PTake rec [Nothing])) e = __impossible "desugarAlt"
desugarAlt e0 (S.PIrrefutable (S.PTake rec [Just (f, S.PVar v)])) e =
  -- Idea:
  --   Base case: e0 | rec {f = PVar v} in e ~~> Take f' (rec,v) = e0 in e
  --   Ind. step: A) e0 | rec {f = p} in e ==> let rec {f = PVar v} = e0 and p = v in e
  --              B) e0 | rec (fp:fps) in e ==> let e1 {f = p} = e0 and rec = e1 {fps} in e
  desugarType (B.getType e0) >>= \(TRecord fs _) -> let Just fldIdx = elemIndex f (P.map fst fs) in
  E <$> (Take (fst v, fst rec) <$> desugarExpr e0 <*> pure fldIdx <*> (withBindings (Cons (fst v) (Cons (fst rec) Nil)) $ desugarExpr e))
desugarAlt e0 (S.PIrrefutable (S.PTake rec [Just (f,p)])) e = do
  v <- freshVar
  S.RT (S.TRecord fts s) <- typeWHNF $ snd rec
  let Just (ft,_) = P.lookup f fts  -- the type of the taken field
      b1 = S.Binding (S.PTake rec [Just (f,S.PVar (v,ft))]) Nothing e0 []
      b2 = S.Binding p Nothing (B.TE ft $ S.Var v) [] -- wrong!
  desugarExpr $ B.TE (B.getType e) $ S.Let [b1,b2] e
desugarAlt e0 (S.PIrrefutable (S.PTake rec (fp:fps))) e = do
  e1 <- freshVar
  S.RT (S.TRecord fts s) <- typeWHNF $ snd rec
  let t1 = S.RT $ S.TRecord (P.map (\ft@(f,(t,x)) -> if f == fst (fromJust fp) then (f,(t,True)) else ft) fts) s  -- type of e1
      b0 = S.Binding (S.PTake (e1, t1) [fp]) Nothing e0 []
      bs = S.Binding (S.PTake rec fps) Nothing (B.TE t1 $ S.Var e1) []
  desugarExpr $ B.TE (B.getType e) $ S.Let [b0,bs] e
desugarAlt _ _ _ = __impossible "desugarAlt (_)"  -- literals

desugarPrimInt :: S.RawType -> PrimInt
desugarPrimInt (S.RT (S.TCon "U8"   [] Unboxed)) = U8
desugarPrimInt (S.RT (S.TCon "U16"  [] Unboxed)) = U16
desugarPrimInt (S.RT (S.TCon "U32"  [] Unboxed)) = U32
desugarPrimInt (S.RT (S.TCon "U64"  [] Unboxed)) = U64
desugarPrimInt (S.RT (S.TCon "Bool" [] Unboxed)) = Boolean
desugarPrimInt _ = __impossible "desugarPrimInt"

desugarType :: S.RawType -> DS t v (Type t)
desugarType t = typeWHNF t >>= \case
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
  S.RT (S.TVariant alts) -> TSum <$> mapM (\(c,ts) -> (c,) . (,False) <$> desugarType (S.RT $ S.TTuple ts)) (M.toList alts)
  S.RT (S.TTuple [])     -> __impossible "desugarType (TTuple)"
  S.RT (S.TTuple (t:[])) -> __impossible "desugarType (TTuple)"
  S.RT (S.TTuple (t1:t2:[])) | not __cogent_ftuples_as_sugar -> TProduct <$> desugarType t1 <*> desugarType t2
  S.RT (S.TTuple (t1:t2:ts)) | not __cogent_ftuples_as_sugar -> __impossible "desugarType"  -- desugarType $ S.RT $ S.TTuple [t1, S.RT $ S.TTuple (t2:ts)]
  S.RT (S.TTuple ts) | __cogent_ftuples_as_sugar -> TRecord <$> (P.zipWith (\t n -> (n,(t, False))) <$> forM ts desugarType <*> pure (P.map (('p':) . show) [1 :: Integer ..])) <*> pure Unboxed
  S.RT (S.TUnit)   -> return TUnit
  notInWHNF -> __impossible $ "desugarType" ++ show notInWHNF

substType :: [(VarName, S.RawType)] -> S.RawType -> S.RawType
substType sigma (S.RT (S.TVar v b)) | Just t <- P.lookup v sigma = t
                                    | otherwise = S.RT (S.TVar v b)
substType sigma (S.RT (S.TFun a b)) = S.RT (S.TFun (substType sigma a) (substType sigma b))
substType sigma (S.RT (S.TRecord fs s)) = S.RT (S.TRecord (map (second . first $ substType sigma) fs) s)
substType sigma (S.RT (S.TVariant fs)) = S.RT (S.TVariant (fmap (fmap $ substType sigma) fs))
substType sigma (S.RT (S.TUnit)) = S.RT S.TUnit
substType sigma (S.RT (S.TTuple fs)) = S.RT (S.TTuple (map (substType sigma) fs))
substType sigma (S.RT (S.TUnbox t)) = S.RT (S.TUnbox $ substType sigma t)
substType sigma (S.RT (S.TBang t)) = S.RT (S.TBang $ substType sigma t)
substType sigma (S.RT (S.TTake fs t)) = S.RT (S.TTake fs (substType sigma t))
substType sigma (S.RT (S.TPut  fs t)) = S.RT (S.TPut  fs (substType sigma t))
substType sigma (S.RT (S.TCon c ts s)) = S.RT (S.TCon c (map (substType sigma) ts) s)

bangType :: S.RawType -> S.RawType
bangType (S.RT (S.TVar v _)) = S.RT (S.TVar v True)
bangType (S.RT (S.TRecord fs s)) = S.RT (S.TRecord (map (second . first $ S.RT . S.TBang) fs) $ bangSigil s)
bangType (S.RT (S.TCon x ts s))= S.RT (S.TCon x (map (S.RT . S.TBang) ts) $ bangSigil s)
bangType (S.RT (S.TUnit)) = S.RT S.TUnit
bangType (S.RT (S.TFun a b)) = S.RT (S.TFun a b)
bangType (S.RT (S.TTuple ts)) = S.RT (S.TTuple (map (S.RT . S.TBang) ts))  -- using `RT . TBang' instead of `bangType' for better errmsgs
bangType (S.RT (S.TVariant ts)) = S.RT (S.TVariant (fmap (fmap $ S.RT . S.TBang) ts))
bangType notInWHNF = __impossible "bangType"

typeWHNF :: S.RawType -> DS t v S.RawType
typeWHNF x@(S.RT (S.TCon c as s)) = M.lookup c . sel1 <$> ask >>= \case
  Just (vs,t)  -> typeWHNF (substType (P.zip vs as) t)
  Nothing -> return x
typeWHNF x@(S.RT (S.TVar {})) = return x
typeWHNF x@(S.RT (S.TFun {})) = return x
typeWHNF x@(S.RT (S.TRecord {})) = return x
typeWHNF x@(S.RT (S.TVariant alts)) = S.RT . S.TVariant <$> (forM alts $ \ts -> (:[]) <$> typeWHNF (S.RT $ S.TTuple ts))
typeWHNF   (S.RT (S.TTuple [])) = return $ S.RT S.TUnit
typeWHNF   (S.RT (S.TTuple [t])) = typeWHNF t
typeWHNF x@(S.RT (S.TTuple [t1,t2])) | not __cogent_ftuples_as_sugar = return x  -- make n-tuples into nested 2-tuples
typeWHNF   (S.RT (S.TTuple (t:ts@(_:_:_)))) | not __cogent_ftuples_as_sugar = typeWHNF (S.RT $ S.TTuple ts) >>= \ts' -> return $ S.RT $ S.TTuple [t,ts']
typeWHNF x@(S.RT (S.TTuple _)) = return x  -- | __cogent_ftuples_as_sugar
-- typeWHNF x@(S.RT (S.TTuple (reverse -> (t:ts)))) = case t of
--   (S.RT (S.TTuple ts')) -> typeWHNF (S.RT . S.TTuple $ reverse ts ++ ts')
--   _ -> return x
typeWHNF x@(S.RT (S.TUnit)) = return x
typeWHNF x@(S.RT (S.TUnbox t)) = typeWHNF t >>= \case
  S.RT (S.TCon cn ts s) -> return $ S.RT (S.TCon cn ts Unboxed)
  S.RT (S.TRecord fs s) -> return $ S.RT (S.TRecord fs Unboxed)
  x -> __impossible "typeWHNF"
typeWHNF (S.RT (S.TBang t)) = bangType <$> typeWHNF t
typeWHNF (S.RT (S.TTake Nothing t)) = typeWHNF t >>= \case  -- take all untaken fields
  S.RT (S.TRecord fs s) -> return $ S.RT $ S.TRecord (P.map (second . second $ const True) fs) s
  x -> __impossible "typeWHNF"
typeWHNF (S.RT (S.TTake (Just []) t)) = typeWHNF t
typeWHNF (S.RT (S.TTake (Just fs) t)) = typeWHNF t >>= \case  -- take untaken fields
  S.RT (S.TRecord rs s) -> return $ S.RT $ S.TRecord (P.map (\r@(n,(t,x)) -> if n `elem` fs then (n,(t,True)) else r) rs) s
  x -> __impossible "typeWHNF"
typeWHNF (S.RT (S.TPut Nothing t)) = typeWHNF t >>= \case  -- put (a) taken linear fields (b) untaken discardable fields
  S.RT (S.TRecord fs s) -> return $ S.RT $ S.TRecord (P.map (second . second $ const False) fs) s
  x -> __impossible "typeWHNF"
typeWHNF (S.RT (S.TPut (Just []) t)) = typeWHNF t
typeWHNF (S.RT (S.TPut (Just fs) t)) = typeWHNF t >>= \case
  S.RT (S.TRecord rs s) -> return $ S.RT $ S.TRecord (P.map (\r@(n,(t,x)) -> if n `elem` fs then (n,(t,False)) else r) rs) s
  x -> __impossible "typeWHNF"

desugarNote :: S.Inline -> FunNote
desugarNote S.NoInline = NoInline
desugarNote S.Inline   = InlinePlease

desugarExpr :: B.TypedExpr -> DS t v (UntypedExpr t v VarName)
desugarExpr (B.TE _ (S.PrimOp opr es)) = E . Op (desugarOp opr) <$> mapM desugarExpr es
desugarExpr (B.TE _ (S.Var vn)) = (findIx vn . sel2 <$> get) >>= \case
  Just v  -> return $ E $ Variable (v, vn)
  Nothing -> do constdefs <- view _2
                let Just e = M.lookup vn constdefs
                desugarExpr e
desugarExpr (B.TE _ (S.Match e _ [])) = __impossible "desugarExpr (Match)"
desugarExpr (B.TE _ (S.Match e [] alts)) = desugarAlts e alts
desugarExpr (B.TE _ (S.Match e vs alts)) = do
  -- Idea: e !vs | alts ~~> let v = e !vs in desugarAlt (v, alts)
  -- FIXME: Not sure if this is going to work / zilinc
  venv <- use _2
  v <- freshVar
  let vs' = P.map (fromJust . flip findIx venv &&& id) vs
  e' <- withBinding v $ desugarAlts (B.TE (B.getType e) $ S.Var v) alts
  E <$> (LetBang vs' v <$> desugarExpr e <*> pure e')
desugarExpr (B.TE _ (S.TypeApp v ts note)) = do
  pragmas <- view _3
  E <$> (Fun v <$> mapM desugarType ts <*> pure (pragmaToNote pragmas v $ desugarNote note))
desugarExpr (B.TE _ (S.Con c [] )) = return . E $ Con c (E Unit)
desugarExpr (B.TE _ (S.Con c [e])) = E . Con c <$> desugarExpr e
desugarExpr (B.TE t (S.Con c es )) = do
  S.RT (S.TVariant ts) <- typeWHNF t
  let Just [tes] = M.lookup c ts 
  E . Con c <$> desugarExpr (B.TE tes $ S.Tuple es)
desugarExpr (B.TE _ (S.Seq e1 e2)) = do
  v <- freshVar
  E <$> (Let v <$> desugarExpr e1 <*> withBinding v (desugarExpr e2))
desugarExpr (B.TE _ (S.App (B.TE _ (S.TypeApp ('_':_) _ _)) _)) | not __cogent_debug = return (E Unit)
desugarExpr (B.TE _ (S.App e1 e2)) = E <$> (App <$> desugarExpr e1 <*> desugarExpr e2)
desugarExpr (B.TE _ (S.If c [] th el)) = E <$> (If <$> desugarExpr c <*> desugarExpr th <*> desugarExpr el)
desugarExpr (B.TE _ (S.If c vs th el)) = do
  venv <- use _2
  v <- freshVar
  let vs' = P.map (fromJust . flip findIx venv &&& id) vs
  th' <- withBinding v $ desugarExpr th
  el' <- withBinding v $ desugarExpr el
  let e' = E $ If (E $ Variable (f0, v)) th' el'
  E <$> (LetBang vs' v <$> desugarExpr c <*> pure e')
desugarExpr (B.TE _ (S.Member e fld)) = do
  TRecord fs _ <- desugarType $ B.getType e
  let Just f' = elemIndex fld (P.map fst fs)
  E <$> (Member <$> desugarExpr e <*> pure f')
desugarExpr (B.TE _ (S.Unitel)) = return $ E Unit
desugarExpr (B.TE t (S.IntLit n)) = return $ E . ILit n $ desugarPrimInt t
desugarExpr (B.TE _ (S.BoolLit b)) = return $ E $ ILit (if b then 1 else 0) Boolean
desugarExpr (B.TE _ (S.CharLit c)) = return $ E $ ILit (fromIntegral $ ord c) U8
desugarExpr (B.TE _ (S.StringLit s)) = return $ E $ SLit s
desugarExpr (B.TE _ (S.Tuple [])) = __impossible "desugarExpr (Tuple)"
desugarExpr (B.TE _ (S.Tuple [e])) = __impossible "desugarExpr (Tuple)"
desugarExpr (B.TE _ (S.Tuple (e1:e2:[]))) | not __cogent_ftuples_as_sugar = E <$> (Tuple <$> desugarExpr e1 <*> desugarExpr e2)
desugarExpr (B.TE t (S.Tuple (e1:e2:es))) | not __cogent_ftuples_as_sugar = __impossible "desugarExpr"  -- do
  -- S.RT (S.TTuple (t1:t2:ts)) <- typeWHNF t
  -- let t2' = S.RT $ S.TTuple (t2:ts)
  --     e2' = B.TE t2' $ S.Tuple (e2:es)
  -- desugarExpr $ B.TE (S.RT $ S.TTuple [t1,t2']) $ S.Tuple [e1,e2']
-- desugarExpr (B.TE _ (S.Tuple (reverse -> (e:es)))) | B.TE _ (S.Tuple _) <- e = __impossible "desugarExpr"
desugarExpr (B.TE _ (S.Tuple es)) = E . Struct <$> (P.zip (P.map (('p':) . show) [1 :: Integer ..]) <$> mapM desugarExpr es)  -- | __cogent_ftuples_as_sugar
desugarExpr (B.TE _ (S.UnboxedRecord fs)) = E . Struct <$> mapM (\(f,e) -> (f,) <$> desugarExpr e) fs
desugarExpr (B.TE _ (S.Let [] e)) = __impossible "desugarExpr (Let)"
desugarExpr (B.TE _ (S.Let [S.Binding p mt e0 []] e)) = desugarAlt e0 (S.PIrrefutable p) e
desugarExpr (B.TE _ (S.Let [S.Binding (S.PVar v) mt e0 bs] e)) = do
  -- Idea:
  --   Base case: let v = e0 !bs in e ~~> let! bs e0 e
  --   Ind. step: A) let p = e0 !bs in e ==> let v = e0 !bs and p = v in e
  --              B) let p1=e1 !bs1; ps=es !bss in e ==> let p1 = e1 !bs1 in let ps=es !bss in e
  venv <- use _2
  let bs' = P.map (fromJust . flip findIx venv &&& id) bs
  E <$> (LetBang bs' (fst v) <$> desugarExpr e0 <*> withBinding (fst v) (desugarExpr e))
desugarExpr (B.TE t (S.Let [S.Binding p mt e0 bs] e)) = do
  v <- freshVar
  let t0 = B.getType e0
      b0 = S.Binding (S.PVar (v,t0)) Nothing e0 bs
      b1 = S.Binding p mt (B.TE t0 $ S.Var v) []
  desugarExpr (B.TE t $ S.Let [b0,b1] e)
desugarExpr (B.TE t (S.Let (b:bs) e)) = desugarExpr $ B.TE t (S.Let [b] e')
  where e' = B.TE t $ S.Let bs e
desugarExpr (B.TE _ (S.Put e [])) = desugarExpr e
desugarExpr (B.TE t (S.Put e [Nothing])) = __impossible "desugarExpr (Put)"
desugarExpr (B.TE t (S.Put e [Just (f,a)])) = do
  TRecord fs _ <- desugarType t
  let Just f' = elemIndex f (P.map fst fs)
  E <$> (Put <$> desugarExpr e <*> pure f' <*> desugarExpr a)
desugarExpr (B.TE t (S.Put e (fa:fas))) = do
  t' <- typeWHNF t >>= \x -> return $ S.RT (S.TTake (Just $ P.map (fst . fromJust) fas) x)
  desugarExpr $ B.TE t $ S.Put (B.TE t' $ S.Put e [fa]) fas
desugarExpr _ = undefined
--desugarExpr (B.Promote t e) = E <$> (Promote <$> desugarType t <*> desugarExpr e)
--desugarExpr (B.TypeErrorHappened {}) = __impossible "desugarExpr (Error)"

desugarOp :: S.OpName -> Op
desugarOp "+"   = Plus
desugarOp "-"   = Minus
desugarOp "*"   = Times
desugarOp "/"   = Divide
desugarOp "%"   = Mod
desugarOp "not" = Not
desugarOp "&&"  = And
desugarOp "||"  = Or
desugarOp ">="  = Ge
desugarOp "<="  = Le
desugarOp "<"   = Lt
desugarOp ">"   = Gt
desugarOp "=="  = Eq
desugarOp "/="  = NEq
desugarOp ".&." = BitAnd
desugarOp ".|." = BitOr
desugarOp ".^." = BitXor
desugarOp ">>"  = RShift
desugarOp "<<"  = LShift
desugarOp "complement" = Complement
desugarOp x     = __impossible "desugarOp"

desugarConst :: (VarName, T.TypedExpr) -> DS 'Zero 'Zero (SFConst UntypedExpr)
desugarConst (n,e) = (n,) <$> desugarExpr e

-- NOTE: aseume the first arguments consists of constants only
desugarConsts :: [S.TopLevel S.RawType T.TypedName T.TypedExpr] -> DS 'Zero 'Zero [SFConst UntypedExpr]
desugarConsts = mapM desugarConst . P.map (\(S.ConstDef v _ e) -> (v,e))

