--
-- Copyright 2021, Data61
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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.DesugarV2 (desugar) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core
import qualified Cogent.Dargent.Allocation as DA
import Cogent.Dargent.Core
import Cogent.Dargent.Surface
import qualified Cogent.Dargent.Desugar as DD
import Cogent.Dargent.TypeCheck
import Cogent.Dargent.Util
import Cogent.PrettyPrint ()
import qualified Cogent.Surface as S
import qualified Cogent.TypeCheck.Base as B
import Cogent.Util
import Data.Ex
import Data.Fin
import Data.Nat
import Data.PropEq ((:=:)(Refl))
import Data.Vec as Vec

import Control.Applicative
import Control.Arrow ((&&&), first)
import Lens.Micro as Lens
import Lens.Micro.TH as Lens
import Lens.Micro.Mtl as Lens
import Lens.Micro.GHC as Lens
import Control.Monad.Reader hiding (forM)
import Control.Monad.RWS.Strict hiding (forM)
import Data.Bits
import Data.Char (ord)
-- import Data.Foldable
import Data.IntMap as IM (fromList, filterWithKey)
import Data.List as L (elemIndex)
import qualified Data.Map as M hiding (filter, (\\))
import Data.Maybe
import Data.Word (Word32)
import Prelude as P
import Data.Traversable (forM)
import Text.Parsec.Pos (SourcePos)
import Text.PrettyPrint.ANSI.Leijen (pretty)
-- import qualified Traversable as Trav (mapM)

import Debug.Trace


-- -----------------------------------------------------------------------------
-- Top-level definitions and function
-- -----------------------------------------------------------------------------

type TypeVars t = Vec t TyVarName
type LayoutVars l = Vec l DLVarName
type TermVars v = Vec v VarName
type Typedefs   = M.Map TypeName ([VarName], B.DepType)  -- typenames |-> typeargs * strltype
type Constants  = M.Map VarName  B.TypedExpr  -- This shares namespace with `TermVars'
type Enumerator = Int

data DsState t l v = DsState { _typCtx :: TypeVars t
                             , _layCtx :: LayoutVars l
                             , _varCtx :: TermVars v
                             , _oracleLcl :: Enumerator
                             , _oracleGbl :: Enumerator
                             , _lftFun :: [S.TopLevel B.DepType B.TypedPatn B.TypedExpr]  -- reversed
                             }

makeLenses ''DsState

newtype DS (t :: Nat) (l :: Nat) (v :: Nat) a =
  DS { runDS :: RWS (Typedefs, Constants, [Pragma])
                    (Last (Typedefs, Constants, [CoreConst TypedExpr]))
                    -- \^ NOTE: it's a hack to export the reader! / zilinc
                    (DsState t l v)
                    a }
  deriving (Functor, Applicative, Monad,
            MonadReader (Typedefs, Constants, [Pragma]),
            MonadWriter (Last (Typedefs, Constants, [CoreConst TypedExpr])),
            MonadState  (DsState t l v))

#if MIN_VERSION_base(4,13,0)
instance MonadFail (DS t l v) where
  fail = __impossible
#endif


desugar :: [S.TopLevel B.DepType B.TypedPatn B.TypedExpr]
        -> [(B.DepType, String)]
        -> [Pragma]
        -> ( ([Definition TypedExpr VarName VarName], [(SupposedlyMonoType VarName, String)])
           , Last (Typedefs, Constants, [CoreConst TypedExpr]) )
desugar tls ctygen pragmas =
  let fundefs    = filter isFunDef     tls where isFunDef     S.FunDef     {} = True; isFunDef     _ = False
      absdecs    = filter isAbsDec     tls where isAbsDec     S.AbsDec     {} = True; isAbsDec     _ = False
      typedecs   = filter isTypeDec    tls where isTypeDec    S.TypeDec    {} = True; isTypeDec    _ = False
      abstydecs  = filter isAbsTypeDec tls where isAbsTypeDec S.AbsTypeDec {} = True; isAbsTypeDec _ = False
      constdefs  = filter isConstDef   tls where isConstDef   S.ConstDef   {} = True; isConstDef   _ = False

      initialReader = ( M.fromList $ P.map fromTypeDec  typedecs
                      , M.fromList $ P.map fromConstDef constdefs
                      , pragmas )
      initialState = DsState Nil Nil Nil 0 0 []
   in flip3 evalRWS initialState initialReader . runDS $
        desugar' (abstydecs ++ typedecs ++ absdecs ++ fundefs) constdefs ctygen pragmas
  where
    fromTypeDec  (S.TypeDec tn vs t) = (tn,(vs,t))
    fromTypeDec  _ = __impossible "fromTypeDec (in desugarProgram)"

    fromConstDef (S.ConstDef vn t e) = (vn,e)
    fromConstDef _ = __impossible "fromConstDef (in desugarProgram)"


desugar' :: [S.TopLevel B.DepType B.TypedPatn B.TypedExpr]
         -> [S.TopLevel B.DepType B.TypedPatn B.TypedExpr]  -- constants
         -> [(B.DepType, String)]
         -> [Pragma]
         -> DS 'Zero 'Zero 'Zero ([Definition TypedExpr VarName VarName], [(SupposedlyMonoType VarName, String)])
desugar' tls constdefs ctygen pragmas = do
  defs' <- concat <$> mapM go tls
  write <- ask
  consts' <- desugarConsts constdefs
  ctygen' <- desugarCustTyGen ctygen
  tell $ Last (Just (write^._1, write^._2, consts'))
  return (defs',ctygen')

  where
    initialState  = DsState Nil Nil Nil 0 0 []

    go :: S.TopLevel B.DepType B.TypedPatn B.TypedExpr
       -> DS 'Zero 'Zero 'Zero [Definition TypedExpr VarName VarName]
    go x = do gbl <- use oracleGbl
              put initialState
              oracleGbl .= gbl
              -- \ ^^^ NOTE: We need to set the local oracle to 0 for every top-level definition, as in the
              -- ShallowHaskell module we assume each top-level function have bound variable 0 (de Bruijn)
              -- of name `freshVarPrefix ++ "0"'. The global oracle must __not__ be reset, as it's global.
              -- / zilinc
              x' <- lamLftTlv x
              typCtx .= Nil; varCtx .= Nil;
              def' <- desugarTlv x' pragmas  -- it generates a few more lifted functions
              lfdefs <- reverse <$> use lftFun
              lfdefs' <- concat <$> mapM go lfdefs
              return $ lfdefs' ++ [def']


-- -----------------------------------------------------------------------------
-- Helper functions
-- -----------------------------------------------------------------------------

noPos = __fixme S.noPos  -- FIXME! / zilinc

freshVarPrefix = "x__ds_var_"
freshFunPrefix = "x__lft_f_"


freshVar :: DS t l v VarName
freshVar = P.head <$> freshVars 1

freshVars :: Int -> DS t l v [VarName]
freshVars n = do x <- oracleLcl <<%= (+n)
                 return $ P.map ((++) freshVarPrefix . show) $ P.take n (iterate (+1) x)

freshFun :: FunName -> DS t l v FunName
freshFun f = do x <- oracleGbl <<%= (+1)
                return $ freshFunPrefix ++ f ++ "_" ++ show x

withTypeBinding :: TyVarName -> DS ('Suc t) l v a -> DS t l v a
withTypeBinding t ds = do readers <- ask
                          st <- get
                          let (a, st', _) = flip3 runRWS (st & typCtx %~ Cons t) readers $ runDS ds
                          put $ st' & typCtx .~ st^.typCtx & oracleLcl .~ st^.oracleLcl
                          return a

withTypeBindings :: Vec k TyVarName -> DS (t :+: k) l v a -> DS t l v a
withTypeBindings Nil ds = ds
withTypeBindings (Cons x xs) ds = withTypeBindings xs (withTypeBinding x ds)

withLayoutBinding :: DLVarName -> DS t ('Suc l) v a -> DS t l v a
withLayoutBinding l ds = do readers <- ask
                            st <- get
                            let (a, st', _) = flip3 runRWS (st & layCtx %~ Cons l) readers $ runDS ds
                            put $ st' & layCtx .~ st^.layCtx & oracleLcl .~ st^.oracleLcl
                            return a

withLayoutBindings :: Vec k DLVarName -> DS t (l :+: k) v a -> DS t l v a
withLayoutBindings Nil ds = ds
withLayoutBindings (Cons x xs) ds = withLayoutBindings xs (withLayoutBinding x ds)

withBinding :: VarName -> DS t l ('Suc v) a -> DS t l v a
withBinding v ds = do readers <- ask
                      st <- get
                      let (a, st', _) = flip3 runRWS (st & varCtx %~ Cons v) readers $ runDS ds
                      put $ st' & varCtx .~ st^.varCtx & oracleLcl .~ st^.oracleLcl
                      return a

withBindings :: Vec k VarName -> DS t l (v :+: k) x -> DS t l v x
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


-- -----------------------------------------------------------------------------
-- Lambda lifting
-- -----------------------------------------------------------------------------

lamLftTlv :: S.TopLevel B.DepType B.TypedPatn B.TypedExpr
          -> DS t l v (S.TopLevel B.DepType B.TypedPatn B.TypedExpr)
lamLftTlv (S.FunDef fn sigma@(S.PT tvs _ _) alts) = S.FunDef fn sigma <$> mapM (lamLftAlt tvs fn) alts
lamLftTlv d = return d

lamLftAlt :: [(TyVarName, Kind)] -> FunName -> S.Alt B.TypedPatn B.TypedExpr -> DS t l v (S.Alt B.TypedPatn B.TypedExpr)
lamLftAlt tvs f (S.Alt p l e) = S.Alt p l <$> lamLftExpr tvs f e

lamLftExpr :: [(TyVarName, Kind)] -> FunName -> B.TypedExpr -> DS t l v B.TypedExpr
lamLftExpr tvs f (B.TE t (S.Lam p mt e) l) = do
  f' <- freshFun f
  -- v <- freshVar
  -- let S.RT (S.TFun ti to) = t
      -- e0 = B.TE ti (S.Var v) noPos
      -- [] = freeVars e $ Cons v Nil  -- only implement those without captures
      -- ps = B.TIP ti (S.PVar (v, ti)) : map (\(v,t) -> B.TIP t (S.PVar (v,t) noPos)) fvs
      -- p' = B.TP (S.PIrrefutable $ B.TIP (PTuple ps) noPos) noPos
  -- sigma <- sel1 <$> get
  e' <- lamLftExpr tvs f e
  let fn = S.FunDef f' (S.PT tvs [] t) [S.Alt (B.TP (S.PIrrefutable p) noPos) Regular e']  -- no let-generalisation
  lftFun %= (fn:)
  let tvs' = map (Just . B.DT . flip3 S.TVar False False . fst) tvs
  return $ B.TE t (S.TLApp f' tvs' [] S.NoInline) l
lamLftExpr sigma f (B.TE t e l) = B.TE t <$> traverse (lamLftExpr sigma f) e <*> pure l

-- freeVars :: B.TypedExpr -> Vec v VarName -> [(VarName, S.RawType)]
-- freeVars (B.TE t (S.Var v) _) vs = maybeToList $ case findIx v vs of Just i -> Nothing; Nothing -> Just (v,t)
-- freeVars (B.TE _ e _) vs = foldMap (flip freeVars vs) e

-- -----------------------------------------------------------------------------
-- Desugar functions
-- -----------------------------------------------------------------------------



desugarTlv :: S.TopLevel B.DepType B.TypedPatn B.TypedExpr
           -> [Pragma]
           -> DS 'Zero 'Zero 'Zero (Definition TypedExpr VarName VarName)
desugarTlv (S.Include    _) _ = __impossible "desugarTlv"
desugarTlv (S.IncludeStd _) _ = __impossible "desugarTlv"
desugarTlv (S.TypeDec tn vs t) _ | ExI (Flip vs') <- Vec.fromList vs
                                 , Refl <- zeroPlusNEqualsN (Vec.length vs') = do
  tenv <- use typCtx
  t' <- withTypeBindings vs' $ desugarType t
  return $ TypeDef tn vs' (Just t')
desugarTlv (S.AbsTypeDec tn vs _) _ | ExI (Flip vs') <- Vec.fromList vs = return $ TypeDef tn vs' Nothing
desugarTlv (S.AbsDec fn sigma) pragmas | S.PT vs ls t <- sigma
                                       , ExI (Flip vs') <- Vec.fromList vs
                                       , Refl <- zeroPlusNEqualsN $ Vec.length vs'
  = do
      ls' <- mapM (secondM (withTypeBindings (fmap fst vs') . desugarType)) ls
      case Vec.fromList ls' of
        ExI (Flip ls'') -> do
          t' <- withTypeBindings (fmap fst vs') $ withLayoutBindings (fmap fst ls'') $ desugarType t
          case t' of
            TFun ti' to' -> return $ AbsDecl (pragmaToAttr pragmas fn mempty) fn vs' ls'' ti' to'  -- TODO: dep functions
            _ -> error "Cogent does not allow FFI constants"
desugarTlv (S.FunDef fn sigma alts) pragmas | S.PT vs ls t <- sigma
                                            , ExI (Flip vs') <- Vec.fromList vs
                                            , Refl <- zeroPlusNEqualsN $ Vec.length vs'
  = do
      ls' <- mapM (secondM (withTypeBindings (fmap fst vs') . desugarType)) ls
      case Vec.fromList ls' of
        ExI (Flip ls'') -> do
          withTypeBindings (fmap fst vs') $ withLayoutBindings (fmap fst ls'') $ do
            let (B.DT (S.TFun _ ti to)) = t  -- TODO: dep functions
            TFun ti' to' <- desugarType t
            v <- freshVar
            let e0 = B.TE ti (S.Var v) noPos
            e <- withBinding v $ desugarAlts to e0 alts
            return $ FunDef (pragmaToAttr pragmas fn mempty) fn vs' ls'' ti' to' e
desugarTlv (S.ConstDef {}) _ = __impossible "desugarTlv"
desugarTlv (S.DocBlock _ ) _ = __impossible "desugarTlv"

desugarAlts :: B.DepType -> B.TypedExpr -> [S.Alt B.TypedPatn B.TypedExpr] -> DS t l v (TypedExpr t v VarName VarName)
desugarAlts _ e0 [] = __impossible "desugarAlts"
desugarAlts τ e0 [S.Alt p l e] = desugarAlt τ e0 p e  -- Note: Likelihood is ignored here / zilinc
                                                      --       This also serves as the base case for PCon
  -- Idea:
  --   Base case: e0 | (PCon tagname [p]) in e ~~> desugarAlt e0 (PCon tagname [p]) e
  --   Ind. step: A) e0 | (PCon tagname [PVar v1]) in e1; alts ==>
  --                 case e0 of tagname -> e1; e0' -> e0' | alts
  --              B) e0 | (PCon tagname [p]) in e; alts ==> e0 | (PCon tagname (PVar v)) in (let p = v in e); alts
  --              C) e0 | (PCon tagname ps) in e; alts ==> e0 | (PCon tagname [TTuple ps]) in e; alts
desugarAlts τ e0@(B.TE t v@(S.Var _) vpos) (S.Alt (B.TP p1 pos1) l1 e1 : alts) =  -- More than one Alt, which means the pattern cannot be IrrefPattern
  case p1 of
    S.PCon cn1 [B.TIP (S.PVar v1) _] -> do  -- this is A) for PCon
      e0' <- freshVar
      let B.DT (S.TVariant talts) = t
          t0' = B.DT $ S.TVariant (M.delete cn1 talts)  -- type of e0 without alternative cn
      e1' <- withBinding (fst v1) $ desugarExpr e1
      e2' <- withBinding e0' $ desugarAlts τ (B.TE t0' (S.Var e0') noPos) alts
      let t1' = B.getTypeTE e1  -- should be the same as that of e2
      t1'' <- desugarType t1'
      TE <$> desugarType τ <*> (Case <$> desugarExpr e0 <*> pure cn1 <*> pure (l1,fst v1,e1') <*> pure (mempty,e0',e2'))
    S.PCon cn1 [p1'] -> do  -- This is B) for PCon
      v1 <- freshVar
      let B.DT (S.TVariant talts) = t  -- NOTE: assuming we can't refine a variant type for now / zilinc
          p1'' = B.TIP (S.PVar (v1,t1)) noPos
          Just ([t1], False)  = M.lookup cn1 talts  -- type of v1
          b   = S.Binding p1' Nothing (B.TE t1 (S.Var v1) noPos) []
          e1' = B.TE τ (S.Let [b] e1) noPos
      desugarAlts τ e0 (S.Alt (B.TP (S.PCon cn1 [p1'']) pos1) l1 e1':alts)
    S.PCon cn1 ps ->  -- This is C) for PCon
      desugarAlts τ (B.TE t v vpos) (S.Alt (B.TP (S.PCon cn1 [B.TIP (S.PTuple ps) (B.getLocTIP $ P.head ps)]) pos1) l1 e1 : alts)
    S.PIntLit  i -> do let pt = desugarPrimInt (B.getTypeTE e0)
                       c <- TE (TPrim Boolean) <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [TE (TPrim pt) $ ILit i pt]))
                       -- NOTE: according to the typing rule of If, the refinement on the condition doesn't matter. Thus
                       -- we can safely put Bool here all the time.
                       --  Γ ⊢ c ⇐ Bool  Γ, c ⊢ e1 ⇐ τ  Γ,¬c ⊢ e2 ⇐ τ
                       -- -------------------------------------------- (If)
                       --         Γ ⊢ if c then e1 else e2 ⇐ τ
                       e' <- If <$> pure c
                                <*> desugarExpr e1 <*> desugarAlts τ e0 alts
                       TE <$> desugarType τ <*> pure e'
    -- FIXME: could do better for PBoolLit because this one is easy to exhaust
    S.PBoolLit b -> do let b' = TE (TPrim Boolean) $ ILit (if b then 1 else 0) Boolean
                       c  <- TE (TPrim Boolean) <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [b']))
                       e' <- If <$> pure c
                                <*> desugarExpr e1 <*> desugarAlts τ e0 alts
                       TE <$> desugarType τ <*> pure e'
    S.PCharLit c -> do let c' = TE (TPrim U8) $ ILit (fromIntegral $ ord c) U8
                       e' <- If <$> (TE (TPrim Boolean) <$> (Op Eq <$> ((:) <$> desugarExpr e0 <*> pure [c'])))
                                <*> desugarExpr e1 <*> desugarAlts τ e0 alts
                       TE <$> desugarType τ <*> pure e'
    S.PIrrefutable _ -> __impossible "desugarAlts"
desugarAlts τ e0 alts@(S.Alt _ _ e1:_) = do  -- e0 is not a var, so lift it
  v <- freshVar
  let t0 = B.getTypeTE e0
      b = S.Binding (B.TIP (S.PVar (v,t0)) noPos) Nothing e0 []
      m = B.TE τ (S.Match (B.TE t0 (S.Var v) noPos) [] alts) noPos
  desugarExpr $ B.TE τ (S.Let [b] m) noPos

desugarAlt :: B.DepType -> B.TypedExpr -> B.TypedPatn -> B.TypedExpr -> DS t l v (TypedExpr t v VarName VarName)
desugarAlt τ e0 (B.TP p pos) = let ?pos = pos in desugarAlt' τ e0 p

-- FIXME: use the appropriate source pos information
desugarAlt' :: (?pos :: SourcePos)
            => B.DepType -> B.TypedExpr -> S.Pattern B.TypedIrrefPatn -> B.TypedExpr -> DS t l v (TypedExpr t v VarName VarName)
desugarAlt' τ e0 (S.PCon tag [B.TIP (S.PVar (v,t)) _]) e = do
  e0' <- TE <$> desugarType t <*> (Esac <$> desugarExpr e0)
  e'  <- withBinding v (desugarExpr e)
  TE <$> desugarType τ <*> pure (Let v e0' e')
  -- Idea:
  --   Base case: e0 | PCon cn [PVar v] in e ~~> let v = esac e0 in e
  --   Ind. step: A) e0 | PCon vn [p] in e ==> e0 | PCon cn [PVar v] in (let p = v in e)
  --              B) e0 | PCon vn ps  in e ==> e0 | PCon vn [PTuple ps] in e
desugarAlt' τ e0 (S.PCon tag [p]) e = do  -- Ind. step A)
  v <- freshVar
  let B.DT (S.TVariant alts) = B.getTypeTE e0
      Just ([t], False) = M.lookup tag alts
      b  = S.Binding p Nothing (B.TE t (S.Var v) ?pos) []
      e' = B.TE (B.getTypeTE e) (S.Let [b] e) ?pos
  desugarAlt' τ e0 (S.PCon tag [B.TIP (S.PVar (v,t)) ?pos]) e'
desugarAlt' τ (B.TE t e0 l) (S.PCon tag []) e =  -- Ind. B1)
  desugarAlt' τ (B.TE t e0 l) (S.PCon tag [B.TIP S.PUnitel ?pos]) e
desugarAlt' τ (B.TE t e0 l) (S.PCon tag ps) e =  -- B2)
  -- FIXME: zilinc
  desugarAlt' τ (B.TE t e0 l) (S.PCon tag [B.TIP (S.PTuple ps) (B.getLocTIP $ P.head ps)]) e
                                                          -- At this point, t and e0 do not match!
                                                          -- but hopefully they will after e0 gets desugared
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PVar v) _)) e =
  TE <$> desugarType τ <*> (Let (fst v) <$> desugarExpr e0 <*> (withBinding (fst v) $ desugarExpr e))
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTuple []) p)) e = desugarAlt' τ e0 (S.PIrrefutable (B.TIP S.PUnitel p)) e
desugarAlt' _ e0 (S.PIrrefutable (B.TIP (S.PTuple [irf]) _)) e = __impossible "desugarAlt' (singleton tuple)"
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTuple [B.TIP (S.PVar tn1) _, B.TIP (S.PVar tn2) _]) _)) e
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
  TE <$> desugarType τ <*> (Split (fst tn1, fst tn2) <$> desugarExpr e0 <*> (withBindings (Cons (fst tn1) (Cons (fst tn2) Nil)) $ desugarExpr e))
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTuple [p1,p2]) _)) e | not __cogent_ftuples_as_sugar = do
  v1 <- freshVar
  v2 <- freshVar
  let B.DT (S.TTuple [t1,t2]) = B.getTypeTE e0
      b0 = S.Binding (B.TIP (S.PTuple [B.TIP (S.PVar (v1,t1)) ?pos, B.TIP (S.PVar (v2,t2)) ?pos]) ?pos) Nothing e0 []
      b1 = S.Binding p1 Nothing (B.TE t1 (S.Var v1) (B.getLocTIP p1)) []
      b2 = S.Binding p2 Nothing (B.TE t2 (S.Var v2) (B.getLocTIP p2)) []
  desugarExpr $ B.TE τ (S.Let [b0,b1,b2] e) ?pos  -- Mutual recursion here
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTuple (p1:p2:ps)) pos)) e | not __cogent_ftuples_as_sugar =
  let p2' = B.TIP (S.PTuple (p2:ps)) pos
      p'  = S.PIrrefutable $ B.TIP (S.PTuple [p1, p2']) pos
  in desugarAlt' τ e0 p' e
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTuple ps) _)) e
  | __cogent_ftuples_as_sugar, all isPVar ps
  = do
  -- Idea: PTuple ps = e0 in e
  --   Base case: PTuple [PVar v1, PVar v2, ..., PVar vn] = e0 in e ~~>
  --              let e0'' {p1=v1, ..., pn=vn} = e0' in e'  -- nested take's in sugarfree
  --   Ind. step: PTuple ps = e0 in e ==>
  --              let (v1, ..., vn) = e0
  --              and p1 = v1
  --              ...
  --              and pn = vn
  --              in e  -- The implemention is optimised so that PVars in ps don't need to assign to new vars again
       e0' <- desugarExpr e0
       let vs = P.map (fst . getPVar) ps
       mkTake τ e0' vs e 0
  -- We must construct desugared expression manually, as we have to call
  -- @desugarExpr e0@ to get the e0 desugared to unboxed records.

 where isPVar (B.TIP (S.PVar _) _) = True; isPVar _ = False
       getPVar (B.TIP (S.PVar v) _) = v; getPVar _ = __impossible "getPVar (in desugarAlt')"
       
       mkTake :: B.DepType -> TypedExpr t v VarName VarName -> [VarName] -> B.TypedExpr -> Int
              -> DS t l v (TypedExpr t v VarName VarName)
       mkTake _ _ [] _ _ = __impossible "mkTake (in desugarAlt')"
       mkTake τ e0 [v] e idx = do
         e1 <- freshVar
         e' <- Take (v,e1) e0 idx <$> withBindings (Cons v (Cons e1 Nil)) (desugarExpr e)
         TE <$> desugarType τ <*> pure e'
       mkTake τ e0 (v:vs) e idx = do
         e1 <- freshVar
         let TRecord rp fts s = exprType e0
             t1' = TRecord rp (P.map (\(f,(t,b)) -> (f,(t,f == ('p':show idx) || b))) fts) s
             es  = mkTake τ (TE t1' $ Variable (f1, e1)) vs e (idx + 1)
         e' <- Take (v,e1) e0 idx <$> withBindings (Cons v (Cons e1 Nil)) es
         TE <$> desugarType τ <*> pure e'
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTuple ps) _)) e | __cogent_ftuples_as_sugar = do
  let B.DT (S.TTuple ts) = B.getTypeTE e0  -- NOTE: assuming e0 is not of a refinement type / zilinc
  __assert (P.length ps == P.length ts) $ "desugarAlt': |ps| /= |ts|\nps = " ++ show ps ++ "\nts = " ++ show ts
  let pts = P.zip ps ts
  vpts <- forM pts $ \(p,t) -> case p of B.TIP (S.PVar (v,_)) _ -> return (v,p,t); _ -> (,p,t) <$> freshVar
  let vpts' = P.filter (\(v,p,t) -> not (isPVar p)) vpts
      b0 = S.Binding (B.TIP (S.PTuple $ flip P.map vpts (\(v,p,t) -> B.TIP (S.PVar (v,t)) (B.getLocTIP p))) ?pos) Nothing e0 []
      bs = flip P.map vpts' $ \(v,p,t) -> S.Binding p Nothing (B.TE t (S.Var v) ?pos) []
  desugarExpr $ B.TE τ (S.Let (b0:bs) e) ?pos
  where isPVar (B.TIP (S.PVar _) _) = True; isPVar _ = False
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PUnboxedRecord fs) pos)) e = do
  -- #{a, b, c} ~~> x {a,b,c}  -- since we take all the fields out, the unboxed x is useless and can be discarded
  rec <- (, B.getTypeTE e0) <$> freshVar
  desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTake rec fs) pos)) e
desugarAlt' τ e0 (S.PIrrefutable (B.TIP S.PUnderscore _)) e = do
  v <- freshVar
  TE <$> desugarType τ <*> (Let v <$> desugarExpr e0 <*> withBinding v (desugarExpr e))
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PUnitel) pos)) e = desugarAlt' τ e0 (S.PIrrefutable $ B.TIP S.PUnderscore pos) e
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTake rec []) pos)) e = desugarAlt' τ e0 (S.PIrrefutable $ B.TIP (S.PVar rec) pos) e
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTake rec [Nothing]) _)) e = __impossible "desugarAlt'"
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTake rec [Just (f, B.TIP (S.PVar v) _)]) _)) e = do
  -- Idea:
  --   Base case: e0 | rec {f = PVar v} in e ~~> Take f' (rec,v) = e0 in e
  --   Ind. step: A) e0 | rec {f = p} in e ==> let rec {f = PVar v} = e0 and p = v in e
  --              B) e0 | rec (fp:fps) in e ==> let e1 {f = p} = e0 and rec = e1 {fps} in e
  t <- desugarType (B.getTypeTE e0)
  let TRecord _ fs _ = t  -- NOTE: assuming not a ref.type
      Just fldIdx = elemIndex f (P.map fst fs)
  e' <- withBindings (Cons (fst v) (Cons (fst rec) Nil)) $ desugarExpr e
  TE <$> desugarType τ <*> (Take (fst v, fst rec) <$> desugarExpr e0 <*> pure fldIdx <*> pure e')
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTake rec [Just (f,p)]) pos)) e = do
  v <- freshVar
  let B.DT (S.TRecord _ fts _) = snd rec  -- NOTE: no ref.type
      Just (ft,_) = P.lookup f fts  -- the type of the taken field
      b1 = S.Binding (B.TIP (S.PTake rec [Just (f, B.TIP (S.PVar (v,ft)) ?pos)]) pos) Nothing e0 []
      b2 = S.Binding p Nothing (B.TE ft (S.Var v) ?pos) []  -- FIXME: someone wrote "wrong!" here. Why? check!
  desugarExpr $ B.TE τ (S.Let [b1,b2] e) ?pos
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PTake rec (fp:fps)) pos)) e = do
  e1 <- freshVar
  let B.DT (S.TRecord rp fts s) = snd rec  -- NOTE: no ref.type
      t1 = B.DT $ S.TRecord rp (P.map (\ft@(f,(t,x)) -> if f == fst (fromJust fp) then (f,(t,True)) else ft) fts) s  -- type of e1
      b0 = S.Binding (B.TIP (S.PTake (e1, t1) [fp]) ?pos) Nothing e0 []
      bs = S.Binding (B.TIP (S.PTake rec fps) pos) Nothing (B.TE t1 (S.Var e1) ?pos) []
  desugarExpr $ B.TE τ (S.Let [b0,bs] e) ?pos
#ifdef REFINEMENT_TYPES
desugarAlt' _ e0 (S.PIrrefutable (B.TIP (S.PArray []) pos)) e = __impossible "desugarAlts' (PSequence [] p)"
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PArray [B.TIP (S.PVar (v,t)) _]) _)) e = do
  e0' <- desugarExpr e0
  e'  <- withBinding v $ desugarExpr e
  TE <$> desugarType τ <*> (Let v <$> (TE <$> desugarType t <*> pure (Singleton e0')) <*> pure e')
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PArray [p]) pos)) e = do
  -- Idea:
  --    e0 | [p] in e ~~> let [v] = e0; p = v in e
  v <- freshVar
  let B.TE te0 _ _ = e0
      B.DT (S.TArray telt l _ _) = te0  -- NOTE: no ref.type
      b1 = S.Binding (B.TIP (S.PVar (v,telt)) pos) Nothing e0 []
      b2 = S.Binding p Nothing (B.TE telt (S.Var v) pos) []
  desugarExpr $ B.TE τ (S.Let [b1,b2] e) pos
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PArray (B.TIP (S.PVar (v,_)) _ : ps)) pos)) e = do
  -- Idea:
  --   Base case: e0 | v:@ps in e ~~> pop (v,vs) = e0' in desugarAlt' (vs | ps in e')
  --   Ind. case: e0 | p:@ps in e ==> let v:@ps = e0; p = v in e
  vs <- freshVar
  e0' <- desugarExpr e0
  let B.DT (S.TArray te le s tkns) = B.getTypeTE e0
      tvs = B.DT (S.TArray te (minus1 le) s (map (first minus1) tkns))
      e10 = B.TE tvs (S.Var vs) pos
      p1 = S.PIrrefutable $ B.TIP (S.PArray ps) pos
  e1' <- withBindings (Cons v (Cons vs Nil)) $ desugarAlt' τ e10 p1 e
  TE <$> desugarType τ <*> pure (Pop (v,vs) e0' e1')
 where minus1 :: B.RawTypedExpr -> B.RawTypedExpr
       minus1 e = B.TE u32 (S.PrimOp "-" [e, B.TE u32 (S.IntLit 1) noPos]) S.noPos
       u32 = S.RT (S.TCon "U32" [] Unboxed)
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PArray (p:ps)) pos)) e = do
  v <- freshVar
  let B.DT (S.TArray te l _ _) = B.getTypeTE e0  -- NOTE: no ref.type
      b1 = S.Binding (B.TIP (S.PArray ((B.TIP (S.PVar (v,te)) pos):ps)) pos) Nothing e0 []
      b2 = S.Binding p Nothing (B.TE te (S.Var v) pos) []
  desugarExpr $ B.TE τ (S.Let [b1,b2] e) pos
desugarAlt' _ e0 (S.PIrrefutable (B.TIP (S.PArrayTake arr []) pos)) e = __impossible "desugarAlt': PArrayTake"
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PArrayTake (arr,_) [(i, B.TIP (S.PVar (v,_)) _)]) pos)) e = do
  e0' <- desugarExpr e0
  i'  <- desugarExpr i
  e'  <- withBindings (Cons v $ Cons arr Nil) $ desugarExpr e
  TE <$> desugarType τ <*> pure (ArrayTake (v,arr) e0' i' e')
desugarAlt' τ e0 (S.PIrrefutable (B.TIP (S.PArrayTake arr [(i,ip)]) pos)) e = do
  v <- freshVar
  let B.DT (S.TArray telt _ _ _) = snd arr  -- NOTE: no ref.type
      b1 = S.Binding (B.TIP (S.PArrayTake arr [(i, B.TIP (S.PVar (v,telt)) (B.getLocTIP ip))]) pos) Nothing e []
      b2 = S.Binding ip Nothing (B.TE telt (S.Var v) pos) []
  desugarExpr $ B.TE τ (S.Let [b1,b2] e) pos
desugarAlt' _ e0 (S.PIrrefutable (B.TIP (S.PArrayTake arr ips) pos)) e =
  __todo "desugarAlts': taking multiple elements out of an array is currently not supported"
#endif
desugarAlt' _ _ _ _ = __impossible "desugarAlt' (_)"  -- literals

desugarPrimInt :: B.DepType -> PrimInt
desugarPrimInt (B.DT (S.TCon "U8"   [] Unboxed)) = U8
desugarPrimInt (B.DT (S.TCon "U16"  [] Unboxed)) = U16
desugarPrimInt (B.DT (S.TCon "U32"  [] Unboxed)) = U32
desugarPrimInt (B.DT (S.TCon "U64"  [] Unboxed)) = U64
desugarPrimInt (B.DT (S.TCon "Bool" [] Unboxed)) = Boolean
#ifdef REFINEMENT_TYPES
desugarPrimInt (B.DT (S.TRefine _ b _)) = desugarPrimInt b
#endif
desugarPrimInt t = __impossible $ "desugarPrimInt: " ++ show t

desugarType :: B.DepType -> DS t l v (Type t VarName)
desugarType = \case
  B.DT (S.TCon "U8"     [] Unboxed) -> return $ TPrim U8
  B.DT (S.TCon "U16"    [] Unboxed) -> return $ TPrim U16
  B.DT (S.TCon "U32"    [] Unboxed) -> return $ TPrim U32
  B.DT (S.TCon "U64"    [] Unboxed) -> return $ TPrim U64
  B.DT (S.TCon "Bool"   [] Unboxed) -> return $ TPrim Boolean
  B.DT (S.TCon "String" [] Unboxed) -> return $ TString
  B.DT (S.TCon tn tvs s) -> TCon tn <$> mapM desugarType tvs <*> pure (DD.desugarAbstractTypeSigil s)
  B.DT (S.TVar vn b u)   ->
    (findIx vn <$> use typCtx) >>= \(Just v) -> return $
      case (b,u) of
        (_    , True ) -> TVarUnboxed v
        (True , False) -> TVarBang v
        (False, False) -> TVar v
  B.DT (S.TFun _ ti to) -> TFun <$> desugarType ti <*> desugarType to  -- TODO: dep functions
  B.DT (S.TRecord rp fs Unboxed) -> TRecord rp <$> mapM (\(f,(t,x)) -> (f,) . (,x) <$> desugarType t) fs <*> pure Unboxed
  B.DT (S.TRecord rp fs sigil) -> do
    -- Making an unboxed record is necessary here because of how `desugarSigil`
    -- is defined.
    TRecord rp' fs' Unboxed <- desugarType $ B.DT (S.TRecord rp fs Unboxed)
    TRecord rp' <$> pure fs' <*> desugarSigil sigil
  B.DT (S.TVariant alts) -> TSum <$> mapM (\(c,(ts,x)) -> (c,) . (,x) <$> desugarType (group ts)) (M.toList alts)
    where group [] = B.DT S.TUnit
          group (t:[]) = t
          group ts = B.DT $ S.TTuple ts
  B.DT (S.TTuple [])     -> __impossible "desugarType (TTuple 0)"
  B.DT (S.TTuple (t:[])) -> __impossible "desugarType (TTuple 1)"
  B.DT (S.TTuple (t1:t2:[])) | not __cogent_ftuples_as_sugar -> TProduct <$> desugarType t1 <*> desugarType t2
  B.DT (S.TTuple ts@(_:_:_)) | not __cogent_ftuples_as_sugar ->
    foldr1 (liftA2 TProduct) $ map desugarType ts  -- right associative product repr of a list
  B.DT (S.TTuple ts) | __cogent_ftuples_as_sugar -> do
    let ns = P.map (('p':) . show) [1 :: Integer ..]
    fs <- P.zipWith (\n t -> (n,(t, False))) ns <$> forM ts desugarType
    return $ TRecord NonRec fs Unboxed
  B.DT (S.TUnit)     -> return TUnit
  B.DT (S.TRPar v b m) -> do
    m' <- mapM id (fmap (\x -> mapM id (M.map desugarType x)) m)
    return $ 
      if b then
        TRParBang v m'
      else
        TRPar v m'
#ifdef REFINEMENT_TYPES
  B.DT (S.TArray t l Unboxed tkns) -> do
    t' <- desugarType t
    l' <- texprToLExpr id <$> desugarExpr (fmap B.rawToDepType l)
    mhole <- case tkns of
               [] -> return Nothing
               [(idx,True)] -> Just . texprToLExpr id <$> desugarExpr (fmap B.rawToDepType idx)
               _ -> __impossible "desugarType: TArray should not have more than 1 element taken"
    return $ TArray t' l' Unboxed mhole
  B.DT (S.TArray t l sigil tkns) -> do
    TArray t' l' Unboxed tkns' <- desugarType $ B.DT (S.TArray t l Unboxed tkns)
    -- NOTE: if the user specify boxed array containing boxed types with layout defined as pointer,
    --       we simply turn that into CLayout to avoid generating extra getters & setters
    ds <- case sigil of
            Boxed ro (Just (S.DLArray S.DLPtr _)) -> pure $ Boxed ro CLayout
            _ -> desugarSigil sigil
    TArray <$> pure t'
           <*> pure l'
           <*> pure ds
           <*> pure tkns'
  B.DT (S.TRefine vn b p) -> do
    b' <- desugarType b
    p' <- texprToLExpr id <$> withBinding vn (desugarExpr (fmap B.rawToDepType p))
    return $ TRefine b' p'
#endif
  notInWHNF -> __impossible $ "desugarType (type " ++ show (pretty notInWHNF) ++ " is not in WHNF)"

desugarLayout :: TCDataLayout -> DS t l v (DataLayout DA.BitRange)
desugarLayout l = Layout <$> desugarLayout' l
  where
    desugarLayout' :: TCDataLayout -> DS t l v (DataLayout' DA.BitRange)
    desugarLayout' = \case
      TLRepRef _ _ -> __impossible "desugarLayout: TLRepRef should be normalised before"
      TLPrim n
        | sz <- DD.desugarSize n
        , sz > 0 -> pure $ PrimLayout (fromJust $ DA.newBitRangeBaseSize 0 sz)
        | DD.desugarSize n < 0 -> __impossible "desugarLayout: TLPrim has a negative size"
        | otherwise            -> pure UnitLayout
      TLOffset e n -> do
        e' <- desugarLayout' e
        pure $ offset (DD.desugarSize n) e'
      TLRecord fs -> do
        let f (n,_,l) = desugarLayout' l >>= pure . (n,)
        fs' <- mapM f fs
        pure $ RecordLayout (M.fromList fs')
      TLVariant te alts -> do
        te' <- desugarLayout' te
        let tr = case te' of
                   PrimLayout range -> range
                   UnitLayout       -> __impossible $ "desugarLayout: zero sized bit range for variant tag"
                   _                -> __impossible $ "desugarLayout: tag layout known to be a single range"
        let f (n,_,s,l) = desugarLayout' l >>= pure . (n,) . (s,)
        alts' <- mapM f alts
        pure $ SumLayout tr (M.fromList alts')
      TLPtr -> pure $ PrimLayout DA.pointerBitRange
#ifdef REFINEMENT_TYPES
      TLArray e _ -> ArrayLayout <$> desugarLayout' e
#endif
      TLVar n -> (findIx n <$> use layCtx) >>= \case
        Just v -> pure $ VarLayout (finNat v)
        Nothing -> __impossible "desugarLayout: unexpected layout variable - check typecheck"

desugarSigil :: Sigil (Maybe DataLayoutExpr) -> DS t l v (Sigil (DataLayout DA.BitRange))
desugarSigil (Boxed b Nothing)  = pure $ Boxed b CLayout
desugarSigil (Boxed b (Just l)) = Boxed b <$> desugarLayout (toTCDL l)
desugarSigil Unboxed            = pure Unboxed

desugarNote :: S.Inline -> FunNote
desugarNote S.NoInline = NoInline
desugarNote S.Inline   = InlinePlease

desugarExpr :: B.TypedExpr -> DS t l v (TypedExpr t v VarName VarName)
desugarExpr (B.TE τ (S.PrimOp opr es) _) = TE <$> desugarType τ <*> (Op (symbolOp opr) <$> mapM desugarExpr es)
desugarExpr (B.TE τ (S.Var vn) _) = (findIx vn <$> use varCtx) >>= \case
  Just v  -> TE <$> desugarType τ <*> pure (Variable (v, vn))
  Nothing -> do constdefs <- view _2
                ctx <- use varCtx
                traceM ("ctx = " ++ show (pretty ctx))
                traceM ("constdefs = " ++ show (constdefs))
                traceM ("vn = " ++ show vn)
                let Just e = M.lookup vn constdefs
                desugarExpr e
desugarExpr (B.TE _ (S.Match e _ []) _) = __impossible "desugarExpr (Match)"
desugarExpr (B.TE τ (S.Match e [] alts) _) = desugarAlts τ e alts
desugarExpr (B.TE τ (S.Match e vs alts) l) = do
  -- Idea: e !vs | alts ~~> let v = e !vs in desugarAlt (v, alts)
  -- FIXME: Not sure if this is going to work / zilinc
  venv <- use varCtx
  v <- freshVar
  let vs' = P.map (fromJust . flip findIx venv &&& id) vs
  e' <- withBinding v $ desugarAlts τ (B.TE (B.getTypeTE e) (S.Var v) l) alts
  TE <$> desugarType τ <*> (LetBang vs' v <$> desugarExpr e <*> pure e')
desugarExpr (B.TE τ (S.TLApp v ts ls note) _) = do
  pragmas <- view _3
  ts' <- mapM (desugarType . fromJust) ts
  ls' <- mapM (desugarLayout . fromJust) ls
  TE <$> desugarType τ <*> pure (Fun (funNameToCoreFunName v) ts' ls' (pragmaToNote pragmas v $ desugarNote note))
desugarExpr (B.TE τ (S.Con c [e]) _) = do
  τ'@(TSum ts) <- desugarType τ
  e' <- desugarExpr e
  let ts' = map (\(c',(t,b)) -> if c' == c then (c',(t,b)) else (c',(t,True))) ts
  return $ TE τ' (Con c e' (TSum ts'))  -- the smallest type for `Con c [e]', which should be a subtype of `t'
desugarExpr (B.TE τ@(B.DT (S.TVariant ts)) (S.Con c es) l) = do
  let Just (tes, False) = M.lookup c ts
  desugarExpr (B.TE τ (S.Con c [B.TE (group tes) (S.Tuple es) l]) l)
 where group [] = B.DT S.TUnit
       group (t:[]) = t
       group ts = B.DT $ S.TTuple ts
desugarExpr (B.TE τ (S.Seq e1 e2) _) = do
  v <- freshVar
  TE <$> desugarType τ <*> (Let v <$> desugarExpr e1 <*> withBinding v (desugarExpr e2))
desugarExpr (B.TE _ (S.Lam p mt e) _) = __impossible "desugarExpr (Lam)"
desugarExpr (B.TE τ (S.App e1 e2 _) _) = TE <$> desugarType τ <*> (App <$> desugarExpr e1 <*> desugarExpr e2)
desugarExpr (B.TE τ (S.Comp f g) l) = do
  v <- freshVar
  compf <- freshVar
  let B.DT (S.TFun _ t1 t3) = τ  -- TODO: dep functions
      B.DT (S.TFun _ _  t2) = B.getTypeTE g
      tv = t1
      p = B.TIP (S.PVar (v,tv)) l
      v' = B.TE tv (S.Var v) (B.getLocTE g)
      g' = B.TE t2 (S.App g v' False) (B.getLocTE f)
      e = B.TE t3 (S.App f g' False) l
  e' <- lamLftExpr [] compf (B.TE τ (S.Lam p Nothing e) l)
  desugarExpr e'
desugarExpr (B.TE τ (S.If c [] th el) _) = TE <$> desugarType τ <*> (If <$> desugarExpr c <*> desugarExpr th <*> desugarExpr el)
desugarExpr (B.TE τ (S.If c vs th el) _) = do
  venv <- use varCtx
  v <- freshVar
  let vs' = P.map (fromJust . flip findIx venv &&& id) vs
  th' <- withBinding v $ desugarExpr th
  el' <- withBinding v $ desugarExpr el
  τ' <- withBinding v $ desugarType τ
  c' <- desugarExpr c
  let tc = exprType c'
      e' = TE τ' $ If (TE (insertIdxAtT (Suc Zero) tc) $ Variable (f0, v)) th' el'
  TE <$> desugarType τ <*> pure (LetBang vs' v c' e')
desugarExpr (B.TE _ (S.MultiWayIf [] el) _) = __impossible "desugarExpr: MultiWayIf with only one branch"
desugarExpr (B.TE τ (S.MultiWayIf es el) pos) =  -- FIXME: likelihood is ignored here
  desugarExpr $ B.TE τ (go es el) pos
 where go [(c,bs,_,e)] el = S.If c bs e el
       go ((c,bs,_,e):es) el = S.If c bs e (B.TE τ (go es el) pos)
desugarExpr (B.TE τ (S.Member e fld) _) = do
  t <- desugarType $ B.getTypeTE e
  let TRecord _ fs _ = t
      Just f' = elemIndex fld (P.map fst fs)
  TE <$> desugarType τ <*> (Member <$> desugarExpr e <*> pure f')
desugarExpr (B.TE τ (S.Unitel) _) = TE <$> desugarType τ <*> pure Unit
desugarExpr (B.TE τ (S.IntLit n) _) = TE <$> desugarType τ <*> pure (ILit n $ desugarPrimInt τ)
desugarExpr (B.TE τ (S.BoolLit b) _) = TE <$> desugarType τ <*> pure (ILit (if b then 1 else 0) Boolean)
desugarExpr (B.TE τ (S.CharLit c) _) = TE <$> desugarType τ <*> pure (ILit (fromIntegral $ ord c) U8)
desugarExpr (B.TE τ (S.StringLit s) _) = TE <$> desugarType τ <*> pure (SLit s)
#ifdef REFINEMENT_TYPES
desugarExpr (B.TE τ (S.ArrayLit es) _) = TE <$> desugarType τ <*> (ALit <$> mapM desugarExpr es)
desugarExpr (B.TE τ (S.ArrayIndex e i) _) = do
  e' <- desugarExpr e
  i' <- desugarExpr i
  τ' <- desugarType τ
  return $ TE τ' (ArrayIndex e' i')
desugarExpr (B.TE τ (S.ArrayMap2 ((p1,p2), fbody) (e1,e2)) _) = do
  e1' <- desugarExpr e1
  e2' <- desugarExpr e2
  let B.DT (S.TTuple [telt1, telt2]) = B.getTypeTE fbody
  -- Idea:
  --   \ p1 p2 -> fbody ~~> \ v1 v2 -> let p1 = v1; p2 = v2 in fbody
  v1 <- freshVar
  v2 <- freshVar
  let b1 = S.Binding p1 Nothing (B.TE telt1 (S.Var v1) (B.getLocTIP p1)) []
      b2 = S.Binding p2 Nothing (B.TE telt2 (S.Var v2) (B.getLocTIP p2)) []
  fbody' <- withBindings (Cons v2 $ Cons v1 Nil) $
              desugarExpr $ B.TE (B.DT $ S.TTuple [telt1, telt2]) (S.Let [b1,b2] fbody) (B.getLocTE fbody)
  TE <$> desugarType τ <*> pure (ArrayMap2 ((v1,v2), fbody') (e1',e2'))
desugarExpr (B.TE _ (S.ArrayPut arr []) _) = desugarExpr arr
desugarExpr (B.TE τ (S.ArrayPut arr [(i,e)]) _) = do
  arr' <- desugarExpr arr
  i'   <- desugarExpr i
  e'   <- desugarExpr e
  TE <$> desugarType τ <*> pure (ArrayPut arr' i' e')
desugarExpr (B.TE τ (S.ArrayPut arr (e:es)) l) =
  let t' = B.DT $ S.TAPut [B.toRawTypedExpr $ fst e] (B.getTypeTE arr)
      arr' = B.TE t' (S.ArrayPut arr [e]) l
   in desugarExpr $ B.TE τ (S.ArrayPut arr' es) l
#endif
desugarExpr (B.TE τ (S.Tuple []) _) = TE <$> desugarType τ <*> pure Unit
desugarExpr (B.TE _ (S.Tuple [e]) _) = __impossible "desugarExpr (Tuple)"
desugarExpr (B.TE τ (S.Tuple es@(_:_:_)) _) | not __cogent_ftuples_as_sugar = do
  -- right associative product repr of a list
  let B.DT (S.TTuple ts) = τ
  go ts es
 where go [t1,t2] [e1,e2] = TE <$> desugarType (B.DT $ S.TTuple [t1,t2])
                               <*> (Tuple <$> desugarExpr e1 <*> desugarExpr e2)
       go (t:ts) (e:es) = do es'@(TE ts' _) <- go ts es
                             e' <- desugarExpr e
                             t' <- desugarType t
                             return $ TE (TProduct t' ts') (Tuple e' es')
desugarExpr (B.TE τ (S.Tuple es) _) = do  -- \| __cogent_ftuples_as_sugar
  fs <- P.zip (P.map (('p':) . show) [1 :: Integer ..]) <$> mapM desugarExpr es
  let B.DT (S.TTuple ts) = τ  -- NOTE: no ref.type
      ts' = P.zipWith (\fn t -> (fn,(t,False))) (P.map (('p':) . show) [1 :: Integer ..]) ts
  τ' <- desugarType (B.DT $ S.TRecord NonRec ts' Unboxed)
  return $ TE τ' $ Struct fs
desugarExpr (B.TE τ (S.UnboxedRecord fs) _) = do
  rec <- Struct <$> mapM (\(f,e) -> (f,) <$> desugarExpr e) fs
  TE <$> desugarType τ <*> pure rec
desugarExpr (B.TE _ (S.Let [] e) _) = __impossible "desugarExpr (Let)"
desugarExpr (B.TE τ (S.Let [S.Binding p mt e0 []] e) pos) =
  let ?pos = pos in desugarAlt' τ e0 (S.PIrrefutable p) e
desugarExpr (B.TE τ (S.Let [S.Binding (B.TIP (S.PVar v) _) mt e0 bs] e) _) = do
  -- Idea:
  --   Base case: let v = e0 !bs in e ~~> let! bs e0 e
  --   Ind. step: A) let p = e0 !bs in e ==> let v = e0 !bs and p = v in e
  --              B) let p1=e1 !bs1; ps=es !bss in e ==> let p1 = e1 !bs1 in let ps=es !bss in e
  venv <- use varCtx
  let bs' = P.map (fromJust . flip findIx venv &&& id) bs
  e' <- LetBang bs' (fst v) <$> desugarExpr e0 <*> withBinding (fst v) (desugarExpr e)
  TE <$> desugarType τ <*> pure e'
desugarExpr (B.TE τ (S.Let [S.Binding p mt e0 bs] e) l) = do
  v <- freshVar
  let t0 = B.getTypeTE e0
      b0 = S.Binding (B.TIP (S.PVar (v,t0)) noPos) Nothing e0 bs
      b1 = S.Binding p mt (B.TE t0 (S.Var v) l) []
  desugarExpr $ B.TE τ (S.Let [b0,b1] e) l
desugarExpr (B.TE τ (S.Let (S.BindingAlts p _ e0 vs alts : bs) e) l) = do
  let e0' = if P.null bs then e else B.TE τ (S.Let bs e) l
      alts' = S.Alt p Regular e0' : alts
  desugarExpr (B.TE τ (S.Match e0 vs alts') l)
desugarExpr (B.TE τ (S.Let (b:bs) e) l) = desugarExpr $ B.TE τ (S.Let [b] e') l
  where e' = B.TE τ (S.Let bs e) l
desugarExpr (B.TE _ (S.Put e []) _) = desugarExpr e
desugarExpr (B.TE _ (S.Put e [Nothing]) _) = __impossible "desugarExpr (Put)"
desugarExpr (B.TE τ (S.Put e [Just (f,a)]) _) = do
  τ' <- desugarType τ
  let TRecord _ fs _ = τ'
      Just f' = elemIndex f (P.map fst fs)
  TE <$> desugarType τ <*> (Put <$> desugarExpr e <*> pure f' <*> desugarExpr a)
desugarExpr (B.TE τ (S.Put e (fa@(Just (f0,_)):fas)) l) = do
  let B.DT (S.TRecord rp fs s) = τ
      fs' = map (\ft@(f,(t,b)) -> if f == f0 then (f,(t,False)) else ft) fs
      t' = B.DT (S.TRecord rp fs' s)
  desugarExpr $ B.TE τ (S.Put (B.TE t' (S.Put e [fa]) l) fas) l
desugarExpr (B.TE τ (S.Upcast e) _) = do
  τ' <- desugarType τ
  TE τ' <$> (Cast τ' <$> desugarExpr e)
desugarExpr (B.TE τ (S.Annot e t) _) = do
  -- NOTE: τ and t are not always equal
  -- XXX | __assert (τ == t) $
  -- XXX |   "desugarExpr (Annot): inferred type doesn't agree with annotated type:\n" ++
  -- XXX |   "  τ = " ++ show (pretty τ) ++ "\n" ++
  -- XXX |   "  t = " ++ show (pretty t)
  τ' <- desugarType τ
  TE τ' <$> (Promote τ' <$> desugarExpr e)
  -- \ ^^^ NOTE [How to handle type annotations?]
  -- We need to insert a `Promote' node here, even the type of `e' is the same
  -- as the annotated type `tau'. The reason is, the core-tc will infer `e''s type
  -- to be the "smallest", if `e' is a data constructor. This could render the type
  -- of `e' different from what the surface typechecker has inferred. For example,
  -- (Success a : <Success A | Error B>) :: <Success A | Error B>
  -- If the above is given by the surface Tc, after desugaring the inner, it becomes
  -- `(Success a <Success A | Error* E>)' with `Error' taken.
  -- In the case where the annotated type is indeed the same as the core-tc-inferred
  -- type, we can remove the `Promote' later, or keep it even. / zilinc
desugarExpr (B.TE _ (S.Con c es) p) = __impossible "desugarExpr (Con)"
-- = do
--   S.RT (S.TVariant ts) <- return t
--   let Just ([tes], False) = M.lookup c ts
--   E . Con c <$> desugarExpr (B.TE tes (S.Tuple es) p)
desugarExpr (B.TE _ (S.Put _ _) _) = __impossible "desugarExpr (Put)"

desugarConst :: (VarName, B.TypedExpr) -> DS 'Zero 'Zero 'Zero (CoreConst TypedExpr)
desugarConst (n,e) = (n,) <$> desugarExpr e

-- NOTE: assume the first argument consists of constants only
desugarConsts :: [S.TopLevel B.DepType B.TypedPatn B.TypedExpr] -> DS 'Zero 'Zero 'Zero [CoreConst TypedExpr]
desugarConsts = mapM desugarConst . P.map (\(S.ConstDef v _ e) -> (v,e))


-- ----------------------------------------------------------------------------
-- custTyGen

desugarCustTyGen :: [(B.DepType, String)] -> DS t l v [(SupposedlyMonoType VarName, String)]
desugarCustTyGen = mapM $ firstM (return . SMT <=< desugarType)

