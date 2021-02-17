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

{- LANGUAGE AllowAmbiguousTypes -}
{-# LANGUAGE DataKinds #-}
{- LANGUAGE DeriveDataTypeable -}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- LANGUAGE InstanceSigs -}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cogent.InferenceV2 (tc, retype, tcConsts) where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core
import Cogent.Dargent.Allocation
#ifdef REFINEMENT_TYPES
import Cogent.Inference.SMT
#endif
import Cogent.Inference.Util
import Cogent.Util
import Cogent.PrettyPrint (indent')
import Data.Ex
import Data.Fin
import Data.Nat
import qualified Data.OMap as OM
import Data.PropEq
import Data.Vec hiding (repeat, splitAt, length, zipWith, zip, unzip)
import qualified Data.Vec as Vec

import Control.Applicative
import Control.Arrow hiding ((<+>))
import Control.Monad.Except hiding (fmap, forM_)
import Control.Monad.IO.Class
import Control.Monad.Reader hiding (fmap, forM_)
import Control.Monad.State hiding (fmap, forM_)
import Control.Monad.Trans.Maybe
import Data.Foldable (forM_)
import Data.Function (on)
import qualified Data.IntMap as IM
import Data.Map (Map)
import Data.Maybe (isJust)
import qualified Data.Map as M
import Data.Monoid
#ifdef REFINEMENT_TYPES
import qualified Data.SBV as SMT hiding (proveWith)
import qualified Data.SBV.Dynamic as SMT
#endif
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable(traverse)
#endif
import Data.Word (Word32)
import Lens.Micro (_2)
import Lens.Micro.Mtl (view)
import Text.PrettyPrint.ANSI.Leijen as L hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as L
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)  -- NOTE: used safely to coerce phantom types only

-- import Debug.Trace

guardShow :: String -> Bool -> TC t v b ()
guardShow x b = unless b $ TC (throwError $ "GUARD: " ++ x)

guardShow' :: String -> [String] -> Bool -> TC t v b ()
guardShow' mh mb b = unless b $ TC (throwError $ "GUARD: " ++ mh ++ "\n" ++ unlines mb)

-- ----------------------------------------------------------------------------
-- Type reconstruction

-- Types that don't have the same representation / don't satisfy subtyping.
isUpcastable :: (Eq b, Ord b, Pretty b, Show b) => Type t b -> Type t b -> TC t v b Bool
isUpcastable (TPrim p1) (TPrim p2) = return $ isSubtypePrim p1 p2
isUpcastable (TSum s1) (TSum s2) = do
  c1 <- flip allM s1 (\(c,(t,b)) -> case lookup c s2 of
          Nothing -> return False
          Just (t',b') -> (&&) <$> t `isSubtype` t' <*> pure (b == b'))
  c2 <- flip allM s2 (\(c,(t,b)) -> return $ case lookup c s1 of Nothing -> b; Just _ -> True)  -- other tags are all taken
  return $ c1 && c2
#ifdef REFINEMENT_TYPES
isUpcastable (TPrim p1) (TRefine (TPrim p2) _) = return $ isSubtypePrim p1 p2
isUpcastable (TRefine (TPrim p1) _) (TPrim p2) = return $ isSubtypePrim p1 p2
isUpcastable (TRefine (TPrim p1) _) (TRefine (TPrim p2) _) = return $ isSubtypePrim p1 p2
#endif
isUpcastable _ _ = return False

#ifdef REFINEMENT_TYPES
entails :: (Eq b, Ord b, Pretty b, Show b)
        => Type t b -> LExpr t b -> LExpr t b -> TC t v b Bool
entails β p1 p2 = get >>= \(vec, ls, _) -> liftIO (smtProve vec ls β p1 p2)
#endif


isSubtype :: (Eq b, Pretty b, Show b, Ord b) => Type t b -> Type t b -> TC t v b Bool
isSubtype t1 t2 | t1 == t2 = return True

isSubtype (TRecord rp1 fs1 s1) (TRecord rp2 fs2 s2)
  | map fst fs1 == map fst fs2, s1 == s2, rp1 == rp2 = do
    oks <- flip3 zipWithM fs2 fs1 $ \(_,(t1,b1)) (_, (t2,b2)) -> do
      sub <- t1 `isSubtype` t2
      return $ sub && (not b1 || b2)
    return $ and oks

isSubtype (TSum s1) (TSum s2)
  | s1' <- M.fromList s1, s2' <- M.fromList s2, M.keys s1' == M.keys s2' = do
    oks <- flip3 zipWithM s2 s1 $ \(_,(t1,b1)) (_,(t2,b2)) -> do
      sub <- t1 `isSubtype` t2
      return $ sub && (not b2 || b1)
    return $ and oks

isSubtype (TProduct t11 t12) (TProduct t21 t22) =
  (&&) <$> t11 `isSubtype` t21 <*> t12 `isSubtype` t22

isSubtype (TFun t1 s1) (TFun t2 s2) =
  (&&) <$> t2 `isSubtype` t1 <*> s1 `isSubtype` s2

-- At this point, we can assume recursive parameters and records agree 
isSubtype t1@(TRecord rp fs s) t2@(TRPar v ctxt)    = return True
isSubtype t1@(TRPar v ctxt)    t2@(TRecord rp fs s) = return True
isSubtype t1@(TRPar v1 c1)     t2@(TRPar v2 c2)     = return True

#ifdef REFINEMENT_TYPES
isSubtype rt1@(TRefine t1 p1) rt2@(TRefine t2 p2) | t1 == t2 = entails t1 p1 p2
isSubtype rt1@(TRefine t1 p1) t2 | t1 == t2 = return True
isSubtype t1 rt2@(TRefine t2 p2) | t1 == t2 = entails t1 (LILit 1 Boolean) p2

isSubtype (TArray t1 l1 s1 mhole1) (TArray t2 l2 s2 mhole2)
  | s1 == s2
  = do sub <- t1 `isSubtype` t2
       let holesOk = subHoles mhole1 mhole2
       return $ sub && l1 == l2 && holesOk  -- FIXME: change to propositional equality
  where
    subHoles Nothing   Nothing   = True
    subHoles (Just i1) (Just i2) = i1 == i2  -- FIXME: change to propositional equality
    subHoles Nothing   (Just i2) = False
    subHoles (Just i1) Nothing   = True
#endif

isSubtype t1 t2 = __impossible $
                    "isSubtype: incomparable types:\n" ++
                    "  ... t1 = " ++ show (pretty t1) ++ "\n" ++
                    "  ... t2 = " ++ show (pretty t2)



listIsSubtype :: (Eq b, Ord b, Pretty b, Show b) => [Type t b] -> [Type t b] -> TC t v b Bool
listIsSubtype [] [] = return True
listIsSubtype (x:xs) (y:ys) = (&&) <$> isSubtype x y <*> listIsSubtype xs ys

unroll :: RecParName -> RecContext (Type t b) -> Type t b
unroll v (Just ctxt) = erp (Just ctxt) (ctxt M.! v)
  where
    -- Embed rec pars
    erp :: RecContext (Type t b) -> Type t b -> Type t b
    erp c (TCon n ts s) = TCon n (map (erp c) ts) s
    erp c (TFun t1 t2) = TFun (erp c t1) (erp c t2)
    erp c (TSum r) = TSum $ map (\(a,(t,b)) -> (a, (erp c t, b))) r
    erp c (TProduct t1 t2) = TProduct (erp c t1) (erp c t2)
    erp (Just c) t@(TRecord rp fs s) =
      let c' = case rp of Rec v -> M.insert v t c; _ -> c
      in TRecord rp (map (\(a,(t,b)) -> (a, (erp (Just c') t, b))) fs) s
    -- Context must be Nothing at this point
    erp c (TRPar v Nothing) = TRPar v c
#ifdef REFINEMENT_TYPES
    erp c (TArray t l s h) = TArray (erp c t) l s h
    -- TODO: TRefine
#endif
    erp _ t = t


bang :: Type t b -> Type t b
bang (TVar v)          = TVarBang v
bang (TVarBang v)      = TVarBang v
bang (TVarUnboxed v)   = TVarUnboxed v
bang (TCon n ts s)     = TCon n (map bang ts) (bangSigil s)
bang (TFun ti to)      = TFun ti to
bang (TPrim i)         = TPrim i
bang (TString)         = TString
bang (TSum ts)         = TSum (map (second $ first bang) ts)
bang (TProduct t1 t2)  = TProduct (bang t1) (bang t2)
bang (TRecord rp ts s) = TRecord rp (map (second $ first bang) ts) (bangSigil s)
bang (TRPar n ctxt)    = TRPar n ctxt
bang (TUnit)           = TUnit
#ifdef REFINEMENT_TYPES
bang (TArray t l s tkns) = TArray (bang t) l (bangSigil s) tkns
bang (TRefine b p)     = TRefine (bang b) p
#endif

unbox :: Type t b -> Type t b
unbox (TVar v)         = TVarUnboxed v
unbox (TVarBang v)     = TVarUnboxed v
unbox (TVarUnboxed v)  = TVarUnboxed v
unbox (TCon n ts s)    = TCon n ts (unboxSigil s)
unbox (TRecord rp ts s)= TRecord rp ts (unboxSigil s)
unbox t                = t  -- NOTE that @#@ type operator behaves differently to @!@.
                            -- The application of @#@ should NOT be pushed inside of a
                            -- data type. / zilinc


substitute :: Vec t (Type u b) -> Type t b -> Type u b
substitute vs (TVar v)         = vs `at` v
substitute vs (TVarBang v)     = bang (vs `at` v)
substitute vs (TVarUnboxed v)  = unbox (vs `at` v)
substitute vs (TCon n ts s)    = TCon n (map (substitute vs) ts) s
substitute vs (TFun ti to)     = TFun (substitute vs ti) (substitute vs to)
substitute _  (TPrim i)        = TPrim i
substitute _  (TString)        = TString
substitute vs (TProduct t1 t2) = TProduct (substitute vs t1) (substitute vs t2)
substitute vs (TRecord rp ts s) = TRecord rp (map (second (first $ substitute vs)) ts) s
substitute vs (TSum ts)         = TSum (map (second (first $ substitute vs)) ts)
substitute _  (TUnit)           = TUnit
substitute vs (TRPar v m)       = TRPar v $ fmap (M.map (substitute vs)) m
#ifdef REFINEMENT_TYPES
substitute vs (TArray t l s mhole) = TArray (substitute vs t) (substituteLE vs l) s (fmap (substituteLE vs) mhole)
substitute vs (TRefine t b)     = TRefine (substitute vs t) (substituteLE vs b) -- check this
#endif

substituteL :: [DataLayout BitRange] -> Type t b -> Type t b
substituteL ls (TCon n ts s)     = TCon n (map (substituteL ls) ts) s
substituteL ls (TFun ti to)      = TFun (substituteL ls ti) (substituteL ls to)
substituteL ls (TProduct t1 t2)  = TProduct (substituteL ls t1) (substituteL ls t2)
substituteL ls (TRecord rp ts s) = TRecord rp (map (second (first $ substituteL ls)) ts) (substituteS ls s)
substituteL ls (TSum ts)         = TSum (map (second (first $ substituteL ls)) ts)
#ifdef REFINEMENT_TYPES
substituteL ls (TArray t l s mhole) = TArray (substituteL ls t) l (substituteS ls s) mhole
substituteL ls (TRefine t b)     = TRefine (substituteL ls t) b -- check this 
#endif
substituteL _  t                 = t

substituteS :: [DataLayout BitRange] -> Sigil (DataLayout BitRange) -> Sigil (DataLayout BitRange)
substituteS ls Unboxed = Unboxed
substituteS ls (Boxed b CLayout) = Boxed b CLayout
substituteS ls (Boxed b (Layout l)) = Boxed b . Layout $ substituteS' ls l
  where
    substituteS' :: [DataLayout BitRange] -> DataLayout' BitRange -> DataLayout' BitRange
    substituteS' ls l = case l of
      VarLayout n -> case ls !! (natToInt n) of
                       CLayout -> __impossible "substituteS in Inference: CLayout shouldn't be here"
                       Layout l -> l
      SumLayout tag alts ->
        let altl = M.toList alts
            fns = fmap fst altl
            fis = fmap fst $ fmap snd altl
            fes = fmap snd $ fmap snd altl
         in SumLayout tag $ M.fromList (zip fns $ zip fis (fmap (substituteS' ls) fes))
      RecordLayout fs ->
        let fsl = M.toList fs
            fns = fmap fst fsl
            fes = fmap snd fsl
         in RecordLayout $ M.fromList (zip fns (fmap (substituteS' ls) fes))
#ifdef REFINEMENT_TYPES
      ArrayLayout e -> ArrayLayout $ substituteS' ls e
#endif
      _ -> l

#ifdef REFINEMENT_TYPES
substituteLE :: Vec t (Type u b) -> LExpr t b -> LExpr u b
substituteLE vs = \case
  LVariable va       -> LVariable va
  LFun fn ts ls      -> LFun fn (fmap (substitute vs) ts) ls
  LOp op es          -> LOp op $ fmap go es
  LApp e1 e2         -> LApp (go e1) (go e2)
  LCon tn e t        -> LCon tn (go e) (substitute vs t)
  LUnit              -> LUnit
  LILit n t          -> LILit n t
  LSLit s            -> LSLit s
  LLet a e e'        -> LLet a (go e) (go e')
  LLetBang bs a e e' -> LLetBang bs a (go e) (go e')
  LTuple e1 e2       -> LTuple (go e1) (go e2)
  LStruct fs         -> LStruct $ fmap (second go) fs
  LIf c th el        -> LIf (go c) (go th) (go el)
  LCase e tn (a1,e1) (a2,e2)
                     -> LCase (go e) tn (a1,go e1) (a2,go e2)
  LEsac e            -> LEsac $ go e
  LSplit as e e'     -> LSplit as (go e) (go e')
  LMember e f        -> LMember (go e) f
  LTake as rec f e'  -> LTake as (go rec) f (go e')
  LPut rec f e       -> LPut (go rec) f (go e)
  LPromote t e       -> LPromote (substitute vs t) (go e)
  LCast t e          -> LCast (substitute vs t) (go e)
 where go = substituteLE vs
#endif

remove :: (Eq a) => a -> [(a,b)] -> [(a,b)]
remove k = filter ((/= k) . fst)

adjust :: (Eq a) => a -> (b -> b) -> [(a,b)] -> [(a,b)]
adjust k f = map (\(a,b) -> (a,) $ if a == k then f b else b)


newtype TC (t :: Nat) (v :: Nat) b x
  = TC {unTC :: ExceptT String
                        (ReaderT (Vec t Kind, Map FunName (FunctionType b))
                                 (StateT (Vec v (Maybe (Type t b)), Vec v [LExpr t b], Int) IO))
                        x}
  deriving (Functor, Applicative, Alternative, Monad, MonadIO, MonadPlus,
            MonadReader (Vec t Kind, Map FunName (FunctionType b)), 
            MonadState ((Vec v (Maybe (Type t b)), Vec v [LExpr t b], Int)))

#if MIN_VERSION_base(4,13,0)
instance MonadFail (TC t v b) where
  fail = __impossible
#endif

infixl 4 <||>
(<||>) :: TC t v b (x -> y) -> TC t v b x -> TC t v b y
(TC a) <||> (TC b) = TC $ do x <- get
                             f <- a
                             x1 <- get
                             put x
                             arg <- b
                             x2 <- get
                             -- XXX | unTC $ guardShow "<||>" $ x1 == x2
                             -- \ ^^^ NOTE: This check is taken out to fix
                             -- #296.  The issue here is that, if we define a
                             -- variable of permission D alone (w/o S), it will
                             -- be marked as used after it's been used, which
                             -- is correct. But when it is used in one branch
                             -- but not in the other one, which is allowed as
                             -- it's droppable, it will be marked as used in
                             -- the context of one branch but not the other and
                             -- render the two contexts different. The formal
                             -- specification requires that both contexts are
                             -- the same, but it is tantamount to merging two
                             -- differerent (correct) contexts correctly, which
                             -- can be established in the typing proof.
                             -- / v.jackson, zilinc
                             return (f arg)

#ifdef REFINEMENT_TYPES
-- returns list of inputs, and (base) type of output
-- ASSUME inputs are base types.
opType :: (Pretty b) => Op -> [Type t b] -> TC t v b (Maybe ([Type t VarName], Type t b))
opType opr [TPrim t1, TPrim t2]
  | opr `elem` [Plus, Minus, Times,
                BitAnd, BitOr, BitXor, LShift, RShift]
  , t1 /= Boolean, t1 == t2
  = pure $ Just ([TPrim t1, TPrim t1], TPrim t1)
opType opr [TPrim t1, TPrim t2]
  | opr `elem` [Divide, Mod]
  , t1 /= Boolean, t1 == t2
  = if __cogent_ftypecheck_undef then
      do v <- freshVarName
         let nonZeroPred = LOp Gt [LVariable (Zero, v), LILit 0 t1]
             nonZeroType = TRefine (TPrim t1) nonZeroPred
         return $ Just ([TPrim t1, nonZeroType], TPrim t1)
    else pure $ Just ([TPrim t1, TPrim t1], TPrim t1)
opType opr [TPrim t1, TPrim t2]
  | opr `elem` [Gt, Lt, Le, Ge, Eq, NEq], t1 /= Boolean, t1 == t2
  = pure $ Just ([TPrim t1, TPrim t1], TPrim Boolean)
opType opr [TPrim Boolean, TPrim Boolean]
  | opr `elem` [And, Or, Eq, NEq]
  = pure $ Just ([TPrim Boolean, TPrim Boolean], TPrim Boolean)
opType Not [TPrim Boolean]
  = pure $ Just ([TPrim Boolean], TPrim Boolean)
opType Complement [TPrim t]
  | t /= Boolean
  = pure $ Just ([TPrim t], TPrim t)
#else
opType :: Op -> [Type t b] -> Maybe (Type t b)
opType opr [TPrim p1, TPrim p2]
  | opr `elem` [Plus, Minus, Times, Divide, Mod,
                BitAnd, BitOr, BitXor, LShift, RShift],
    p1 == p2, p1 /= Boolean = Just $ TPrim p1
opType opr [TPrim p1, TPrim p2]
  | opr `elem` [Gt, Lt, Le, Ge, Eq, NEq],
    p1 == p2, p1 /= Boolean = Just $ TPrim Boolean
opType opr [TPrim Boolean, TPrim Boolean]
  | opr `elem` [And, Or, Eq, NEq] = Just $ TPrim Boolean
opType Not [TPrim Boolean] = Just $ TPrim Boolean
opType Complement [TPrim p] | p /= Boolean = Just $ TPrim p
#endif
opType opr ts = __impossible $ "opType(" ++ show opr ++ ")\n" ++
                               "ts = " ++ show (pretty ts) 


useVariable :: (Pretty b) => Fin v -> TC t v b (Maybe (Type t b))
useVariable v = TC $ do
  ret <- (`at` v) <$> fst3 <$> get
  case ret of
    Nothing -> return ret
    Just t  -> do
      ok <- canShare <$> unTC (kindcheck t)
      unless ok $ modify (\(s, p, n) -> (update s v Nothing, p, n))
      let t' = insertIdxAtByT (Suc $ finNat v) (Suc Zero) t
      -- traceM ("*****> v is " ++ show v ++
      --         "\n ..... t was " ++ show (pretty t) ++
      --         "\n ..... t' is " ++ show (pretty t'))
      return $ Just t'
      -- return ret

funType :: CoreFunName -> TC t v b (Maybe (FunctionType b))
funType v = TC $ (M.lookup (unCoreFunName v) . snd) <$> ask

runTC :: TC t v b x
      -> (Vec t Kind, Map FunName (FunctionType b))
      -> (Vec v (Maybe (Type t b)), Vec v [LExpr t b], Int)
      -> IO (Either String ((Vec v (Maybe (Type t b)), Vec v [LExpr t b], Int), x))
runTC (TC a) readers st = do
  tc <- liftIO $ runStateT (runReaderT (runExceptT a) readers) st
  return $ case tc of
    (Left x, s)  -> Left x
    (Right x, s) -> Right (s, x)


retype :: [Definition TypedExpr VarName VarName]
       -> IO (Either String [Definition TypedExpr VarName VarName])
retype ds = do ds' <- tc ds
               return $ fst <$> ds'

tc :: [Definition TypedExpr VarName VarName]
   -> IO (Either String ([Definition TypedExpr VarName VarName], Map FunName (FunctionType VarName)))
tc = flip tc' M.empty
  where
    tc' :: [Definition TypedExpr VarName VarName]
        -> Map FunName (FunctionType VarName)  -- the reader
        -> IO (Either String ([Definition TypedExpr VarName VarName], Map FunName (FunctionType VarName)))
    tc' [] reader = return $ Right ([], reader)
    tc' ((FunDef attr fn ks ls t rt e):ds) reader =
      -- Enable recursion by inserting this function's type into the function type dictionary
      let ft = FT (snd <$> ks) (snd <$> ls) t rt in
      do 
        rtc <- liftIO $ runTC (check e rt)
                              (fmap snd ks, M.insert fn ft reader)
                              ((Cons (Just t) Nil), Cons [] Nil, 0)
        case rtc of
          Left x -> return $ Left x
          Right (_, e') -> (fmap $ first (FunDef attr fn ks ls t rt e':)) <$> tc' ds (M.insert fn (FT (fmap snd ks) (fmap snd ls) t rt) reader)
    tc' (d@(AbsDecl _ fn ks ls t rt):ds) reader = (fmap $ first (Unsafe.unsafeCoerce d:)) <$> tc' ds (M.insert fn (FT (fmap snd ks) (fmap snd ls) t rt) reader)
    tc' (d:ds) reader = (fmap $ first (Unsafe.unsafeCoerce d:)) <$> tc' ds reader

tc_ :: [Definition TypedExpr VarName VarName]
    -> IO (Either String [Definition TypedExpr VarName VarName])
tc_ ds = tc ds >>= (\r -> return (fst <$> r))

tcConsts :: [CoreConst TypedExpr]
         -> Map FunName (FunctionType VarName)
         -> IO (Either String ([CoreConst TypedExpr], Map FunName (FunctionType VarName)))
tcConsts [] reader = return $ Right ([], reader)
tcConsts ((v,e):ds) reader = do 
    rtc <- liftIO $ runTC (pure e) (Nil, reader) (Nil, Nil, 0)
    case rtc of
      Left x -> return $ Left x
      Right (_,e') -> (fmap $ first ((v,e'):)) <$> (tcConsts ds reader)

withBinding :: Type t b -> TC t ('Suc v) b x -> TC t v b x
withBinding t x
  = TC $ do readers <- ask
            (tvec, pvec, n) <- get
            rtc <- lift . liftIO $ runTC x readers (Cons (Just t) tvec, Cons [] pvec, n)
            case rtc of
              Left e -> throwError e
              Right ((Cons Nothing s, Cons _ p, n), r)  -> do put (s, p, n); return r
              Right ((Cons (Just t) s, Cons _ p, n), r) -> do
                ok <- canDiscard <$> unTC (kindcheck t)
                if ok then put (s,p,n) >> return r
                      else throwError "Didn't use linear variable"

withBindings :: Vec k (Type t b) -> TC t (v :+: k) b x -> TC t v b x
withBindings Nil tc = tc
withBindings (Cons x xs) tc = withBindings xs (withBinding x tc)

withPredicate :: (Show b) => LExpr t b -> TC t v b x -> TC t v b x
withPredicate l x
  = TC $ do readers <- ask
            (s, Cons p ps, n) <- get
            rtc <- lift . liftIO $ runTC x readers (s, Cons (l:p) ps, n) 
            case rtc of
              Left e -> throwError e
              Right ((s', Cons (l':p') ps', n), r) -> do put (s', Cons p' ps', n); return r

withBang :: [Fin v] -> TC t v b x -> TC t v b x
withBang vs (TC x) = TC $ do (st, p', n) <- get
                             mapM_ (\v -> modify (\(s,p,n) -> (modifyAt v (fmap bang) s, p, n))) vs
                             ret <- x
                             mapM_ (\v -> modify (\(s,p,n) -> (modifyAt v (const $ st `at` v) s, p, n))) vs
                             return ret

freshVarPrefix = "_v"

freshVarName :: TC t v b VarName
freshVarName = TC $ do readers <- ask
                       (st, p, n) <- get
                       put (st, p, n + 1)
                       return $ freshVarPrefix ++ show n

lookupKind :: Fin t -> TC t v b Kind
lookupKind f = TC ((`at` f) . fst <$> ask)

kindcheck_ :: (Monad m) => (Fin t -> m Kind) -> Type t a -> m Kind
kindcheck_ f (TVar v)         = f v
kindcheck_ f (TVarBang v)     = bangKind <$> f v
kindcheck_ f (TVarUnboxed v)  = return mempty
kindcheck_ f (TCon n vs s)    = return $ sigilKind s
kindcheck_ f (TFun ti to)     = return mempty
kindcheck_ f (TPrim i)        = return mempty
kindcheck_ f (TString)        = return mempty
kindcheck_ f (TProduct t1 t2) = mappend <$> kindcheck_ f t1 <*> kindcheck_ f t2
kindcheck_ f (TRecord _ ts s) = mconcat <$> ((sigilKind s :) <$> mapM (kindcheck_ f . fst . snd) (filter (not . snd . snd) ts))
kindcheck_ f (TSum ts)        = mconcat <$> mapM (kindcheck_ f . fst . snd) (filter (not . snd . snd) ts)
kindcheck_ f (TUnit)          = return mempty
kindcheck_ f (TRPar _ _)      = return mempty

#ifdef REFINEMENT_TYPES
kindcheck_ f (TArray t l s _) = mappend <$> kindcheck_ f t <*> pure (sigilKind s)
kindcheck_ f (TRefine t _) = kindcheck_ f t
#endif

kindcheck = kindcheck_ lookupKind

checkSub :: String -> Type t VarName -> Type t VarName -> TC t v VarName ()
checkSub s t1 t2 = do
  traceTc ("sub/" ++ s)
          (L.line <>
           text "t1:" <+> pretty t1 L.<$>
           text "t2:" <+> pretty t2)
  guardShow s =<< t1 `isSubtype` t2

check :: TypedExpr t v VarName VarName
      -> Type t VarName
      -> TC t v VarName (TypedExpr t v VarName VarName)
check e@(TE t _) τ = do
  checkSub ("check(" ++ show (pretty e) ++ ")") t τ
  check' e

check' :: TypedExpr t v VarName VarName -> TC t v VarName (TypedExpr t v VarName VarName)
check' e@(TE t (Variable v))
  = do Just t' <- useVariable (fst v)
       traceTc "check'/var" (text "checking variable" <+> pretty e L.<$>
                             text "type from the context is" <+> pretty t' L.<$>
                             text "surface tc gives" <+> pretty t)
       t'' <- case inEqTypeClass t' of
                True -> do
                  vn <- freshVarName
                  let ϕ = LOp Eq [ LVariable (Zero, vn)
                                 , insertIdxAtLE Zero $ LVariable (first finNat v) ]
                  case t' of
                    TRefine β _ -> return $ TRefine β ϕ
                    _           -> return $ TRefine t' ϕ
                False -> return t'
       -- t'' is the selfified type
       checkSub "check'(var)" t'' t
       return $ TE t (Variable v)

check' (TE t (Fun f ts ls note))
  | ExI (Flip ts') <- Vec.fromList ts
  , ExI (Flip ls') <- Vec.fromList ls
  = funType f >>= \case
      Just (FT ks lts ti to) ->
        case (Vec.length ts' =? Vec.length ks, Vec.length ls' =? Vec.length lts)
          of (Just Refl, Just Refl) -> do
               let ti' = substitute ts' $ substituteL ls ti
                   to' = substitute ts' $ substituteL ls to
               forM_ (Vec.zip ts' ks) $ \(t, k) -> do
                 k' <- kindcheck t
                 when ((k <> k') /= k) $ __impossible "kind not matched in type instantiation"
               checkSub "check'(fun)" (TFun ti' to') t
               return $ TE t (Fun f ts ls note)
             _ -> __impossible "lengths don't match"
      _ -> error $ "Something went wrong in lookup of function type: '" ++ unCoreFunName f ++ "'"

check' (TE t (Op o es)) = do
  es' <- mapM infer es
  let operandsTypes = map exprType es'
  vn <- freshVarName
  Just (expectedInputs, to) <- opType o (map toBaseType operandsTypes)
  inputsOk <- listIsSubtype operandsTypes expectedInputs
  guardShow "check'(op)-in" inputsOk
  checkSub "check'(op)-out" t to
  return (TE t (Op o es'))

check' (TE t (App e1 e2)) = do
  e1'@(TE (TFun ti to) _) <- infer e1
  e2' <- check e2 ti
  checkSub "check'(app)" to t
  return $ TE t (App e1' e2')

check' (TE t (Con tag e tfull)) = do
  -- Find type of payload for given tag
  let TSum ts          = tfull
      Just (t', False) = lookup tag ts
  e' <- check e t'
  checkSub "check'(con)" tfull t
  return $ TE t (Con tag e' tfull)

check' (TE t Unit) = do
  checkSub "check'(unit)" t TUnit
  return $ TE t Unit

check' (TE t (ILit i pt)) = do
  checkSub "check'(int)" t (TPrim pt)
  return $ TE t (ILit i pt)

check' (TE t (SLit s)) = do
  checkSub "check'(string)" t TString
  return $ TE t (SLit s)

#ifdef REFINEMENT_TYPES
-- array stuff

check' (TE t (ALit [])) = __impossible "We don't allow 0-size array literals"

check' (TE t (ALit es)) = do
  let TArray telt n _ _ = t
  -- n == |es|
  es' <- mapM (flip check telt) es
  return $ TE t (ALit es')

check' (TE t (ArrayIndex arr idx)) = do
  arr'@(TE ta _) <- infer arr
  let TArray te len _ _ = ta
  vn <- freshVarName
  let ϕ = LOp Lt [LVariable (Zero, vn), len]
  idx' <- check idx (TRefine (TPrim U32) ϕ)
  guardShow ("arr-idx on non-linear") . canShare =<< kindcheck ta
  checkSub "check'(index)" te t
  return $ TE t (ArrayIndex arr' idx')

check' (TE t (ArrayMap2 (as,f) (e1,e2))) = do
  e1'@(TE t1 _) <- infer e1
  e2'@(TE t2 _) <- infer e2
  let TArray te1 l1 _ _ = t1
      TArray te2 l2 _ _ = t2
  f' <- withBindings (Cons te2 (Cons te1 Nil)) $ infer f
  let t' = case __cogent_ftuples_as_sugar of
             False -> TProduct t1 t2
             True  -> TRecord NonRec (zipWith (\f t -> (f,(t,False))) tupleFieldNames [t1,t2]) Unboxed
  checkSub "check'(map2)" t' t
  return $ TE t $ ArrayMap2 (as,f') (e1',e2')

check' (TE t (Pop a e1 e2)) = do
  e1'@(TE t1 _) <- infer e1
  let TArray te l s tkns = t1
      thd = te
      ttl = TArray te (LOp Minus [l, LILit 1 U32]) s tkns
  -- guardShow "arr-pop on a singleton array" $ l > 1
  e2' <- withBindings (Cons thd (Cons ttl Nil)) $ check e2 t
  return $ TE t (Pop a e1' e2')

check' (TE t (Singleton e)) = do
  e'@(TE tarr _) <- infer e
  let TArray te l _ _ = t
  -- guardShow "singleton on a non-singleton array" $ l == 1
  return $ TE te (Singleton e')

check' (TE t (ArrayTake as arr i e)) = do
  arr'@(TE tarr _) <- infer arr
  v <- freshVarName
  let TArray telt len s Nothing = tarr
      ϕ = LOp Lt [LVariable (Zero, v), len]
  i' <- check i (TRefine (TPrim U32) ϕ)
  let tarr' = TArray telt len s (Just $ texprToLExpr id i')
  e' <- withBindings (Cons telt (Cons tarr' Nil)) $ check e t
  return $ TE t (ArrayTake as arr' i' e')

check' (TE t (ArrayPut arr i e)) = do
  arr'@(TE tarr _) <- infer arr
  v <- freshVarName
  let TArray telt len s tkns = tarr
      ϕ = LOp Lt [LVariable (Zero, v), len]
  -- check i is not present if it's linear
  i' <- check i (TRefine (TPrim U32) ϕ)
  e' <- check e telt
  -- XXX | mi <- evalExpr i'
  -- XXX | guardShow "@put index not a integral constant" $ isJust mi
  -- XXX | let Just i'' = mi
  -- XXX | guardShow "@put index is out of range" $ i'' `IM.member` tkns
  -- XXX | let Just itkn = IM.lookup i'' tkns
  -- XXX | k <- kindcheck telm
  -- XXX | unless itkn $ guardShow "@put a non-Discardable untaken element" $ canDiscard k
  return $ TE t (ArrayPut arr' i' e')

#endif
-- end of arrays extension

check' (TE t (Let a e1 e2)) = do
  e1' <- infer e1
  e2' <- withBinding (exprType e1') $ check e2 (insertIdxAtT Zero t)
  return $ TE t (Let a e1' e2')

check' (TE t (LetBang vs a e1 e2)) = do
  e1' <- withBang (map fst vs) (infer e1)
  k <- kindcheck (exprType e1')
  guardShow "let!" $ canEscape k
  e2' <- withBinding (exprType e1') $ check e2 (insertIdxAtT Zero t)
  return $ TE t (LetBang vs a e1' e2')

check' (TE t (Tuple e1 e2)) = do
  e1' <- infer e1
  e2' <- infer e2
  checkSub "check'(tuple)" (TProduct (exprType e1') (exprType e2')) t
  return $ TE t (Tuple e1' e2')

check' (TE t (Struct fs)) = do
  let (ns,es) = unzip fs
  es' <- mapM infer es
  let ts' = zipWith (\n e' -> (n, (exprType e', False))) ns es'
  checkSub "check'(struct)" (TRecord NonRec ts' Unboxed) t
  return $ TE t $ Struct $ zip ns es'

check' (TE t (If c th el)) = do
  c' <- check c (TPrim Boolean)
#ifdef REFINEMENT_TYPES
  let lc = texprToLExpr id c'
  (th',el') <- (,) <$>  withPredicate lc (check th t)
                   <||> withPredicate (LOp Not [lc]) (check el t)
  -- \ ^^^ have to use <||>, as they share the same initial env
#else
  (th',el') <- (,) <$>  check th t
                   <||> check el t
#endif
  return $ TE t (If c' th' el')

check' (TE t (Case e tag (lt,at,et) (le,ae,ee))) = do
  e' <- infer e
  let TSum ts = exprType e'
      Just (t', taken) = lookup tag ts
      restt = TSum $ adjust tag (second $ const True) ts  -- set the tag to taken
      e'' = case taken of
              True  -> promote (TSum $ OM.toList $ OM.adjust (\(t,True) -> (t,False)) tag $ OM.fromList ts) e'
              False -> e'
  (et',ee') <- (,) <$>  withBinding t'    (check et $ insertIdxAtT Zero t)
                   <||> withBinding restt (check ee $ insertIdxAtT Zero t)
  return $ TE t (Case e'' tag (lt,at,et') (le,ae,ee'))

check' (TE t (Esac e)) = do
  e'@(TE (TSum ts) _) <- infer e
  let [(_, (t', False))] = filter (not . snd . snd) ts
  checkSub "check'(esac)" t' t
  return $ TE t (Esac e')

check' (TE t (Split a e1 e2)) = do
  e1' <- infer e1
  let TProduct t1 t2 = exprType e1'
  e2' <- withBindings (Cons t1 (Cons t2 Nil)) (check e2 t)
  return $ TE t (Split a e1' e2')

check' (TE t (Member e f)) = do
  e'@(TE trec _) <- infer e  -- canShare
  let TRecord _ fs _ = trec
  guardShow "member-1" . canShare =<< kindcheck trec
  guardShow "member-2" $ f < length fs
  let (_,(t',c)) = fs !! f
  guardShow "member-3" $ not c  -- not taken
  checkSub "check'(member)" t' t
  return $ TE t (Member e' f)

check' (TE t (Take a e f e2)) = do
  e'@(TE trec _) <- infer e
  traceTc "check'/take" (text "checking" <+> pretty e <+> text "of type" <+> pretty trec)
  let TRecord rp ts s = trec
  -- a common cause of this error is taking a field when you could have used member
  guardShow ("take: sigil cannot be readonly: " ++ show (pretty e)) $ not (readonly s)
  guardShow "take-1" $ f < length ts
  let (init, (fn,(t',False)):rest) = splitAt f ts
  k <- kindcheck t'
  let trec' = TRecord rp (init ++ (fn,(t',True)):rest) s
  e2' <- withBindings (Cons t' (Cons trec' Nil)) (check e2 t)  -- take that field regardless of its shareability
  return $ TE t (Take a e' f e2')

check' (TE t (Put e1 f e2)) = do
  e1'@(TE t1 _) <- infer e1
  let TRecord rp ts s = t1
  guardShow "put: sigil not readonly" $ not (readonly s)
  guardShow "put-1" $ f < length ts
  let (init, (fn,(t',taken)):rest) = splitAt f ts
  k <- kindcheck t'
  unless taken $ guardShow "put-2" $ canDiscard k  -- if it's not taken, then it has to be discardable; if taken, then just put
  e2' <- check e2 t'
  checkSub "check'(put)" (TRecord rp (init ++ (fn,(t',False)):rest) s) t
  return $ TE t (Put e1' f e2')  -- put it regardless

check' (TE t (Cast τ e)) = do
  e'@(TE t' _) <- infer e
  guardShow ("cast: " ++ show t' ++ " <<< " ++ show τ) =<< t' `isUpcastable` τ
  checkSub "check'(cast)" τ t
  return $ TE t (Cast τ e')

check' (TE t (Promote τ e)) = do
  e' <- check e τ
  checkSub "check'(promote)" τ t
  return $ TE t (Promote τ e)


infer :: TypedExpr t v VarName VarName -> TC t v VarName (TypedExpr t v VarName VarName)
infer e = check' e



-- | Promote an expression to a given type, pushing down the promote as far as possible.
-- This structure is useful when destructing runs of case expressions, for example in Cogent.Isabelle.Compound.
--
-- Consider this example of a ternary case:
-- > Case scrutinee tag1
-- >  when_tag1
-- >  (Promote ty
-- >    (Case (Var 0) tag2
-- >      when_tag2
-- >      (Promote ty
-- >        (Let
-- >          (Esac (Var 0))
-- >          when_tag3))))))
--
-- Here, the promote expressions obscure the nested pattern-matching structure of the program.
-- We would like instead to push down the promotes to the following:
-- > Case scrutinee tag1
-- >  when_tag1
-- >  (Case (Var 0) tag2
-- >    (Promote ty when_tag2)
-- >    (Let
-- >      (Esac (Var 0))
-- >      (Promote ty when_tag3)))
--
-- In this pushed version, the promotion and the pattern matching are separate.
--
-- A-normalisation results in a similar structure, but when squashing case expressions for the
-- shallow embedding, we want this to apply to desugared as well as normalised.
--
promote :: Type t b -> TypedExpr t v a b -> TypedExpr t v a b
promote t (TE t' e) = case e of
  -- For continuation forms, push the promote into the continuations
  Let a e1 e2         -> TE t $ Let a e1 $ promote (insertIdxAtT Zero t) e2
  LetBang vs a e1 e2  -> TE t $ LetBang vs a e1 $ promote t e2
  If ec et ee         -> TE t $ If ec (promote t et) (promote t ee)
  Case e tag (l1,a1,e1) (l2,a2,e2)
                      -> TE t $ Case e tag
                                  (l1, a1, promote (insertIdxAtT Zero t) e1)
                                  (l2, a2, promote (insertIdxAtT Zero t) e2)
  -- Collapse consecutive promotes
  Promote _ e'        -> promote t e'
  -- Otherwise, no simplification is necessary; construct a Promote expression as usual.
  _                   -> TE t $ Promote t (TE t' e)


