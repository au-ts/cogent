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
import Control.Arrow
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
import Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
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
#ifdef REFINEMENT_TYPES
isSubtype rt1@(TRefine t1 p1) rt2@(TRefine t2 p2) | t1 == t2 = entails t1 p1 p2
isSubtype rt1@(TRefine t1 p1) t2 | t1 == t2 = return True
isSubtype t1 rt2@(TRefine t2 p2) | t1 == t2 = entails t1 (LILit 1 Boolean) p2
#endif
isSubtype t1 t2 = runMaybeT (t1 `lub` t2) >>= \case Just t  -> return $ t == t2
-- The structural equality check t == t2 is not adequate for refinement equality.
                                                    Nothing -> return False

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

bound :: (Show b, Eq b, Pretty b, Ord b)
      => Bound -> Type t b -> Type t b -> MaybeT (TC t v b) (Type t b)
bound _ t1 t2 | t1 == t2 = return t1
bound b (TRecord rp1 fs1 s1) (TRecord rp2 fs2 s2)
  | map fst fs1 == map fst fs2, s1 == s2, rp1 == rp2 = do
    let op = case b of LUB -> (||); GLB -> (&&)
    blob <- flip3 zipWithM fs2 fs1 $ \(f1,(t1,b1)) (_, (t2,b2)) -> do
      t <- bound b t1 t2
      ok <- lift $ if b1 == b2 then return True
                               else kindcheck t >>= \k -> return (canDiscard k)
      return ((f1, (t, b1 `op` b2)), ok)
    let (fs, oks) = unzip blob
    if and oks then return $ TRecord rp1 fs s1
               else MaybeT (return Nothing)
bound b (TSum s1) (TSum s2)
  | s1' <- M.fromList s1, s2' <- M.fromList s2, M.keys s1' == M.keys s2' = do
    let op = case b of LUB -> (&&); GLB -> (||)
    s <- flip3 unionWithKeyM s2' s1' $
           \k (t1,b1) (t2,b2) -> (,) <$> bound b t1 t2 <*> pure (b1 `op` b2)
    return $ TSum $ M.toList s
bound b (TProduct t11 t12) (TProduct t21 t22) = TProduct <$> bound b t11 t21 <*> bound b t12 t22
bound b (TCon c1 t1 s1) (TCon c2 t2 s2)
  | c1 == c2, s1 == s2 = TCon c1 <$> zipWithM (bound b) t1 t2 <*> pure s1
bound b (TFun t1 s1) (TFun t2 s2) = TFun <$> bound (theOtherB b) t1 t2 <*> bound b s1 s2
-- At this point, we can assume recursive parameters and records agree 
bound b t1@(TRecord rp fs s) t2@(TRPar v ctxt)    = return t2
bound b t1@(TRPar v ctxt)    t2@(TRecord rp fs s) = return t2
bound b t1@(TRPar v1 c1)     t2@(TRPar v2 c2)     = return t2
#ifdef REFINEMENT_TYPES
bound b (TArray t1 l1 s1 mhole1) (TArray t2 l2 s2 mhole2)
  | l1 == l2, s1 == s2
  = do t <- bound b t1 t2
       ok <- lift $ case (mhole1, mhole2) of
               (Nothing, Nothing) -> return True
               (Just i1, Just i2) -> return $ i1 == i2  -- FIXME: change to propositional equality / zilinc
               _ -> kindcheck t >>= \k -> return (canDiscard k)
       let mhole = combineHoles b mhole1 mhole2
       if ok then return $ TArray t l1 s1 mhole
             else MaybeT (return Nothing)
  where
    combineHoles b Nothing   Nothing   = Nothing
    combineHoles b (Just i1) (Just _ ) = Just i1
    combineHoles b Nothing   (Just i2) = case b of GLB -> Nothing; LUB -> Just i2
    combineHoles b (Just i1) Nothing   = case b of GLB -> Nothing; LUB -> Just i1
bound b rt1@(TRefine t1 p1) rt2@(TRefine t2 p2)
  | t1 == t2
  = do isSub <- lift $ entails t1 p1 p2  -- subtype
       isSup <- lift $ entails t1 p2 p1  -- supertype
       case (isSub, isSup) of
         (True, True) -> return rt1 -- doesn't matter which one is returned
         (True, False) -> return $ case b of GLB -> rt1; LUB -> rt2
         (False, True) -> return $ case b of GLB -> rt2; LUB -> rt1
         (False, False) -> case b of
                             GLB -> return (TRefine t1 (LOp And [p1, p2]))
                             LUB -> return (TRefine t1 (LOp Or  [p1, p2]))
bound b t1@(TRefine t l) t2
  | t == t2 = return $ case b of GLB -> t1; LUB -> t2
bound b t1 t2@(TRefine t l)
  | t1 == t = return $ case b of GLB -> t2; LUB -> t1
#endif
bound _ t1 t2 = __impossible ("bound: not comparable:\n" ++ show t1 ++ "\n" ++ 
                              "----------------------------------------\n" ++ show t2 ++ "\n")

lub :: (Show b, Eq b, Pretty b, Ord b) => Type t b -> Type t b -> MaybeT (TC t v b) (Type t b)
lub = bound LUB

glb :: (Show b, Eq b, Pretty b, Ord b) => Type t b -> Type t b -> MaybeT (TC t v b) (Type t b)
glb = bound GLB


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

-- returns list of inputs, and (base) type of output
#ifdef REFINEMENT_TYPES
opType :: Op -> [Type t b] -> TC t v b (Maybe ([Type t VarName], Type t b))
opType opr [(TRefine (TPrim t1) p1), (TRefine (TPrim t2) p2)]
  | opr `elem` [Plus, Minus, Times,
                BitAnd, BitOr, BitXor, LShift, RShift]
  , t1 /= Boolean, t1 == t2
  = pure $ Just ([TPrim t1, TPrim t1], TPrim t1)
opType opr [(TRefine (TPrim t1) p1), (TRefine (TPrim t2) p2)]
  | opr `elem` [Divide, Mod]
  , t1 /= Boolean, t1 == t2
  = if __cogent_ftypecheck_undef then
      do v <- freshVarName
         let nonZeroPred = LOp Gt [LVariable (Zero, v), LILit 0 t1]
             nonZeroType = TRefine (TPrim t1) nonZeroPred
         return $ Just ([TPrim t1, nonZeroType], TPrim t1)
    else pure $ Just ([TPrim t1, TPrim t1], TPrim t1)
opType opr [(TRefine (TPrim t1) p1), (TRefine (TPrim t2) p2)]
  | opr `elem` [Gt, Lt, Le, Ge, Eq, NEq], t1 /= Boolean, t1 == t2
  = pure $ Just ([TPrim t1, TPrim t1], TPrim Boolean)
opType opr [(TRefine (TPrim Boolean) p1), (TRefine (TPrim Boolean) p2)]
  | opr `elem` [And, Or, Eq, NEq]
  = pure $ Just ([TPrim Boolean, TPrim Boolean], TPrim Boolean)
opType Not [TRefine (TPrim Boolean) p]
  = pure $ Just ([TPrim Boolean], TPrim Boolean)
opType Complement [(TRefine (TPrim t) p)]
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
opType opr ts = __impossible "opType"


useVariable :: (Pretty b) => Fin v -> TC t v b (Maybe (Type t b))
useVariable v = TC $ do ret <- (`at` v) <$> fst3 <$> get
                        case ret of
                          Nothing -> return ret
                          Just t  -> do
                            ok <- canShare <$> unTC (kindcheck t)
                            unless ok $ modify (\(s, p, n) -> (update s v Nothing, p, n))
                            let t' = insertIdxAtByT (Suc $ finNat v) (Suc Zero) t
                            traceM ("*****> v is " ++ show v ++ "\n ..... t was " ++ show (pretty t) ++ "\n ..... t' is " ++ show (pretty t'))
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
retype ds = do 
  unt <- tc $ map untypeD ds
  return $ fst <$> unt

tc :: [Definition UntypedExpr VarName VarName]
   -> IO (Either String ([Definition TypedExpr VarName VarName], Map FunName (FunctionType VarName)))
tc = flip tc' M.empty
  where
    tc' :: [Definition UntypedExpr VarName VarName]
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

tc_ :: [Definition UntypedExpr VarName VarName]
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


typecheck :: (Pretty a, Show a, Eq a, Ord a)
          => TypedExpr t v a a -> Type t a -> TC t v a (TypedExpr t v a a)
typecheck e t = do
  let t' = exprType e
  (vec, _, _) <- get
  traceM ("!!!!! under context " ++ show (pretty vec) ++ "\n ... checking if " ++ show (pretty t') ++ " ... is a subtype of " ++ show (pretty t))
  isSub <- t' `isSubtype` t
  if | t == t' -> return e
     | isSub -> return (promote t e)
     | otherwise -> __impossible $ "Under context\n" ++
                                   show (indent' $ pretty vec) ++
                                   "\nInferred type of\n" ++
                                   show (indent' $ pretty e) ++
                                   "\ndoesn't agree with the given type signature:\n" ++
                                   "Inferred type:\n" ++
                                   show (indent' $ pretty t') ++
                                   "\nGiven type:\n" ++
                                   show (indent' $ pretty t) ++ "\n"


-- We for now only check those where a continuation is involved. When we have refinement types,
-- when there's a continuation and when the context is popped, then we cannot infer the refinement
-- type; we have to check using the Promote node.
check :: UntypedExpr t v VarName VarName -> Type t VarName -> TC t v VarName (TypedExpr t v VarName VarName)
check (E (Let a e1 e2)) t = do
  e1' <- infer e1
  traceM ("------> (check let) push a = " ++ show a ++ " of type " ++ show (pretty $ exprType e1'))
  e2' <- withBinding (exprType e1') $ check e2 (insertIdxAtT Zero t)
  return $ TE t (Let a e1' e2')

check (E (If c th el)) t = do
  c' <- infer c
#ifdef REFINEMENT_TYPES
  guardShow "check: if-1" $ toBaseType (exprType c') == TPrim Boolean
  let lc = texprToLExpr id c'
  -- guardShow (show lec) False
  (th',el') <- (,) <$>  withPredicate lc (check th t)
                   <||> withPredicate (LOp Not [lc]) (check el t)
  -- \ ^^^ have to use <||>, as they share the same initial env
#else
  guardShow "check: if-1" $ exprType c' == TPrim Boolean
  (th',el') <- (,) <$>  check th t
                   <||> check el t
#endif
  return $ TE t (If c' th' el')

check (E (Case e tag (lt,at,et) (le,ae,ee))) t
   = do e' <- infer e
        let TSum ts = exprType e'
            Just (t', taken) = lookup tag ts
            restt = TSum $ adjust tag (second $ const True) ts  -- set the tag to taken
            e'' = case taken of
                    True  -> promote (TSum $ OM.toList $ OM.adjust (\(t,True) -> (t,False)) tag $ OM.fromList ts) e'
                    False -> e'
        traceM ("------> (check case) push at = " ++ show at ++ " of type " ++ show (pretty $ t'))
        traceM ("------> (check case) push ae = " ++ show ae ++ " of type " ++ show (pretty $ restt))
        (et',ee') <- (,) <$>  withBinding t'    (check et $ insertIdxAtT Zero t)
                         <||> withBinding restt (check ee $ insertIdxAtT Zero t)
        return $ TE t (Case e'' tag (lt,at,et') (le,ae,ee'))

-- TODO: other cases
check e t = do e' <- infer e
               typecheck e' t

infer :: UntypedExpr t v VarName VarName -> TC t v VarName (TypedExpr t v VarName VarName)
infer (E (Op o es))
#ifdef REFINEMENT_TYPES
  = do es' <- mapM infer es
       let operandsTypes = map toRefType $ map exprType es'
       vn <- freshVarName
       Just (expectedInputs, to) <- opType o operandsTypes
       -- check that each of o is a subtype of expectedInputs
       -- traceM ("operandsTypes " ++ (show $ pretty operandsTypes))
       -- traceM ("expectedInputs " ++ (show $ pretty expectedInputs))
       -- (_,ls,_) <- get
       -- trace ("context " ++ (show ls)) $ return ()
       inputsOk <- listIsSubtype operandsTypes expectedInputs
       let pred = LOp Eq [LVariable (Zero, vn), insertIdxAtLE Zero (LOp o (map (texprToLExpr id) es'))]
       case inputsOk of
         True -> return (TE (TRefine to pred) (Op o es'))
         _ -> __impossible "op types don't match" -- fix me /blaisep
#else
  = do es' <- mapM infer es
       let Just t = opType o (map exprType es')
       return (TE t (Op o es'))
#endif
infer (E (ILit i t))
#ifdef REFINEMENT_TYPES
  = do vn <- freshVarName
       let pred = LOp Eq [LVariable (Zero, vn), LILit i t]
       return (TE (TRefine (TPrim t) pred) (ILit i t))
#else
  = return (TE (TPrim t) (ILit i t))
#endif
infer (E (SLit s))
#ifdef REFINEMENT_TYPES
  = do vn <- freshVarName
       let pred = LOp Eq [LVariable (Zero, vn), LSLit s]
       return (TE (TRefine TString pred) (SLit s))
#else
  = return (TE TString (SLit s))
#endif
#ifdef REFINEMENT_TYPES
infer (E (ALit [])) = __impossible "We don't allow 0-size array literals"
infer (E (ALit es))
   = do es' <- mapM infer es
        let ts = map exprType es'
            n = LILit (fromIntegral $ length es) U32
        t <- lubAll ts
        isSub <- allM (`isSubtype` t) ts
        return (TE (TArray t n Unboxed Nothing) (ALit es'))
  where
    lubAll :: [Type t VarName] -> TC t v VarName (Type t VarName)
    lubAll [] = __impossible "lubAll: empty list"
    lubAll [t] = return t
    lubAll (t1:t2:ts) = do Just t <- runMaybeT $ lub t1 t2
                           lubAll (t:ts)
infer (E (ArrayIndex arr idx))
   = do arr'@(TE ta _) <- infer arr
        let TArray te l _ _ = ta
        idx' <- infer idx
        vn <- freshVarName
        let idxt = exprType idx'
            LILit len t = l -- could be any lexpr, not just LILit
            bt@(TPrim pt) = toBaseType idxt
            pred = LOp Lt [LVariable (Zero, vn), LILit len t]
        inBound <- idxt `isSubtype` (TRefine bt pred) 
        -- guardShow ("arr-idx out of bound") $ idx >= 0 && idx < l  -- no way to check it. need ref types. / zilinc
        guardShow ("arr-idx on non-linear") . canShare =<< kindcheck ta
        return (TE te (ArrayIndex arr' idx'))
infer (E (ArrayMap2 (as,f) (e1,e2)))
   = do e1'@(TE t1 _) <- infer e1
        e2'@(TE t2 _) <- infer e2
        let TArray te1 l1 _ _ = t1
            TArray te2 l2 _ _ = t2
        f' <- withBindings (Cons te2 (Cons te1 Nil)) $ infer f
        let t = case __cogent_ftuples_as_sugar of
                  False -> TProduct t1 t2
                  True  -> TRecord NonRec (zipWith (\f t -> (f,(t,False))) tupleFieldNames [t1,t2]) Unboxed
        return $ TE t $ ArrayMap2 (as,f') (e1',e2')
infer (E (Pop a e1 e2))
   = do e1'@(TE t1 _) <- infer e1
        let TArray te l s tkns = t1
            thd = te
            ttl = TArray te (LOp Minus [l, LILit 1 U32]) s tkns
        -- guardShow "arr-pop on a singleton array" $ l > 1
        e2'@(TE t2 _) <- withBindings (Cons thd (Cons ttl Nil)) $ infer e2
        return (TE t2 (Pop a e1' e2'))
infer (E (Singleton e))
   = do e'@(TE t _) <- infer e
        let TArray te l _ _ = t
        -- guardShow "singleton on a non-singleton array" $ l == 1
        return (TE te (Singleton e'))
infer (E (ArrayTake as arr i e))
   = do arr'@(TE tarr _) <- infer arr
        i' <- infer i
        let TArray telt len s Nothing = tarr
            tarr' = TArray telt len s (Just $ texprToLExpr id i')
        e'@(TE te _) <- withBindings (Cons telt (Cons tarr' Nil)) $ infer e
        return (TE te $ ArrayTake as arr' i' e')
infer (E (ArrayPut arr i e))
   = do arr'@(TE tarr _) <- infer arr
        i' <- infer i
        e'@(TE te _)   <- infer e
        -- FIXME: all the checks are disabled here, for the lack of a proper
        -- refinement type system. Also, we cannot know the exact index that
        -- is being put, thus there's no way that we can infer the precise type
        -- for the new array (tarr').
        let TArray telm len s tkns = tarr
        -- XXX | mi <- evalExpr i'
        -- XXX | guardShow "@put index not a integral constant" $ isJust mi
        -- XXX | let Just i'' = mi
        -- XXX | guardShow "@put index is out of range" $ i'' `IM.member` tkns
        -- XXX | let Just itkn = IM.lookup i'' tkns
        -- XXX | k <- kindcheck telm
        -- XXX | unless itkn $ guardShow "@put a non-Discardable untaken element" $ canDiscard k
        let tarr' = TArray telm len s Nothing
        return (TE tarr' (ArrayPut arr' i' e'))
#endif
infer (E (Variable v))
   = do Just t <- useVariable (fst v)
        xxx <- get
#ifdef REFINEMENT_TYPES
        case inEqTypeClass t of
          True -> do
            vn <- freshVarName
            let pred = LOp Eq [ LVariable (Zero, vn)
                              , insertIdxAtLE Zero $ LVariable (finNat $ fst v, snd v) 
                              ]
            case t of
              TRefine base _ -> return $ TE (TRefine base pred) (Variable v)
              _ -> return $ TE (TRefine t pred) (Variable v)
          False -> return $ trace ("!!!!! Under the context " ++ show (pretty xxx) ++ "\n... the type of variable " ++ show v ++ " is " ++ show (pretty t)) $ TE t (Variable v)
#else
        return $ TE t (Variable v)
#endif
infer (E (Fun f ts ls note))
   | ExI (Flip ts') <- Vec.fromList ts
   , ExI (Flip ls') <- Vec.fromList ls
   = do funType f >>= \case
          Just (FT ks lts ti to) ->
            case (Vec.length ts' =? Vec.length ks, Vec.length ls' =? Vec.length lts)
              of (Just Refl, Just Refl) -> let ti' = substitute ts' $ substituteL ls ti
                                               to' = substitute ts' $ substituteL ls to
                                            in do forM_ (Vec.zip ts' ks) $ \(t, k) -> do
                                                    k' <- kindcheck t
                                                    when ((k <> k') /= k) $ __impossible "kind not matched in type instantiation"
                                                  return $ TE (TFun ti' to') (Fun f ts ls note)
                 _ -> __impossible "lengths don't match"
          _        -> error $ "Something went wrong in lookup of function type: '" ++ unCoreFunName f ++ "'"
infer (E (App e1 e2))
   = do e1'@(TE (TFun ti to) _) <- infer e1
        e2'@(TE ti' _) <- infer e2
        isSub <- ti' `isSubtype` ti
        guardShow ("app (actual: " ++ show ti' ++ "; formal: " ++ show ti ++ ")") $ isSub
        if ti' /= ti then return $ TE to (App e1' (promote ti e2'))
                     else return $ TE to (App e1' e2')
infer (E (Let a e1 e2))
   = do e1' <- infer e1
        traceM ("------> push a = " ++ show a ++ " of type " ++ show (pretty $ exprType e1'))
        e2' <- withBinding (exprType e1') (infer e2)
        return $ TE (insertIdxAtT Zero $ exprType e2') (Let a e1' e2')
infer (E (LetBang vs a e1 e2))
   = do e1' <- withBang (map fst vs) (infer e1)
        k <- kindcheck (exprType e1')
        guardShow "let!" $ canEscape k
        e2' <- withBinding (exprType e1') (infer e2)
        return $ TE (insertIdxAtT Zero $ exprType e2') (LetBang vs a e1' e2')
infer (E Unit) = return $ TE TUnit Unit
infer (E (Tuple e1 e2))
   = do e1' <- infer e1
        e2' <- infer e2
        return $ TE (TProduct (exprType e1') (exprType e2')) (Tuple e1' e2')
infer (E (Con tag e tfull))
   = do e' <- infer e
        -- Find type of payload for given tag
        let TSum ts          = tfull
            Just (t, False) = lookup tag ts
        -- Make sure to promote the payload to type t if necessary
        e'' <- typecheck e' t
        return $ TE tfull (Con tag e'' tfull)
infer (E (If ec et ee))
   = do ec' <- infer ec
#ifdef REFINEMENT_TYPES
        guardShow "if-1" $ toBaseType (exprType ec') == TPrim Boolean
        let lec = texprToLExpr id ec'
        -- guardShow (show lec) False
        (et',ee') <- (,) <$>  withPredicate lec (infer et)
                         <||> withPredicate (LOp Not [lec]) (infer ee)
        -- \ ^^^ have to use <||>, as they share the same initial env
#else
        guardShow "if-1" $ exprType ec' == TPrim Boolean
        (et',ee') <- (,) <$>  infer et
                         <||> infer ee
#endif
        let tt = exprType et'
            te = exprType ee'
        Just tlub <- runMaybeT $ tt `lub` te
#ifdef REFINEMENT_TYPES
        (isSubThen, isSubElse) <- (,) <$>  withPredicate lec             (tt `isSubtype` tlub)
                                      <||> withPredicate (LOp Not [lec]) (te `isSubtype` tlub)
#else
        (isSubThen, isSubElse) <- (,) <$> tt `isSubtype` tlub <*> te `isSubtype` tlub
#endif
        guardShow' "if-2" ["Then type:", show (pretty tt) ++ ";",
                           "else type:", show (pretty te) ++ ";",
                           "calculated LUB type:", show (pretty tlub)] (isSubThen && isSubElse)
        let et'' = if tt /= tlub then promote tlub et' else et'
            ee'' = if te /= tlub then promote tlub ee' else ee'
        return $ TE tlub (If ec' et'' ee'')
infer (E (Case e tag (lt,at,et) (le,ae,ee)))
   = do e' <- infer e
        let TSum ts = exprType e'
            Just (t, taken) = lookup tag ts
            restt = TSum $ adjust tag (second $ const True) ts  -- set the tag to taken
            e'' = case taken of
                    True  -> promote (TSum $ OM.toList $ OM.adjust (\(t,True) -> (t,False)) tag $ OM.fromList ts) e'
                    False -> e'
        traceM ("------> push at = " ++ show at ++ " of type " ++ show (pretty $ t))
        traceM ("------> push ae = " ++ show ae ++ " of type " ++ show (pretty $ restt))
        (et',ee') <- (,) <$>  withBinding t     (infer et)
                         <||> withBinding restt (infer ee)
        let tt = exprType et'
            te = exprType ee'
        Just tlub <- runMaybeT $ tt `lub` te
        isSub <- (&&) <$> tt `isSubtype` tlub <*> te `isSubtype` tlub
        guardShow' "case" ["Match type:", show (pretty tt) ++ ";", "rest type:", show (pretty te)] isSub
        let et'' = if tt /= tlub then promote tlub et' else et'
            ee'' = if te /= tlub then promote tlub ee' else ee'
        return $ TE tlub (Case e'' tag (lt,at,et'') (le,ae,ee''))
infer (E (Esac e))
   = do e'@(TE (TSum ts) _) <- infer e
        let t1 = filter (not . snd . snd) ts
        case t1 of
          [(_, (t, False))] -> return $ TE t (Esac e')
          _ -> __impossible $ "infer: esac (t1 = " ++ show t1 ++ ", ts = " ++ show ts ++ ")"
infer (E (Split a e1 e2))
   = do e1' <- infer e1
        let (TProduct t1 t2) = exprType e1'
        e2' <- withBindings (Cons t1 (Cons t2 Nil)) (infer e2)
        return $ TE (exprType e2') (Split a e1' e2')
infer (E (Member e f))
   = do e'@(TE t _) <- infer e  -- canShare
        let TRecord _ fs _ = t
        guardShow "member-1" . canShare =<< kindcheck t
        guardShow "member-2" $ f < length fs
        let (_,(tau,c)) = fs !! f
        guardShow "member-3" $ not c  -- not taken
        return $ TE tau (Member e' f)
infer (E (Struct fs))
   = do let (ns,es) = unzip fs
        es' <- mapM infer es
        let ts' = zipWith (\n e' -> (n, (exprType e', False))) ns es'
        return $ TE (TRecord NonRec ts' Unboxed) $ Struct $ zip ns es'
infer (E (Take a e f e2))
   = do e'@(TE t _) <- infer e
        -- trace ("@@@@t is " ++ show t) $ return ()
        let TRecord rp ts s = t
        -- a common cause of this error is taking a field when you could have used member
        guardShow ("take: sigil cannot be readonly: " ++ show (pretty e)) $ not (readonly s)
        guardShow "take-1" $ f < length ts
        let (init, (fn,(tau,False)):rest) = splitAt f ts
        k <- kindcheck tau
        let trec = TRecord rp (init ++ (fn,(tau,True)):rest) s
        traceM ("------> push a = " ++ show a ++ " of type " ++ show (pretty $ (tau, trec)))
        e2' <- withBindings (Cons tau (Cons trec Nil)) (infer e2)  -- take that field regardless of its shareability
        return $ TE (exprType e2') (Take a e' f e2')
infer (E (Put e1 f e2))
   = do e1'@(TE t1 _) <- infer e1
        let TRecord rp ts s = t1
        guardShow "put: sigil not readonly" $ not (readonly s)
        guardShow "put-1" $ f < length ts
        let (init, (fn,(tau,taken)):rest) = splitAt f ts
        k <- kindcheck tau
        unless taken $ guardShow "put-2" $ canDiscard k  -- if it's not taken, then it has to be discardable; if taken, then just put
        e2'@(TE t2 _) <- infer e2
        isSub <- t2 `isSubtype` tau
        guardShow "put-3" isSub
        let e2'' = if t2 /= tau then promote tau e2' else e2'
        return $ TE (TRecord rp (init ++ (fn,(tau,False)):rest) s) (Put e1' f e2'')  -- put it regardless
infer (E (Cast τ e))
   = do (TE t e') <- infer e
        guardShow ("cast: " ++ show t ++ " <<< " ++ show τ) =<< t `isUpcastable` τ
        return $ TE τ (Cast τ $ TE t e')
infer (E (Promote τ e))
#ifdef REFINEMENT_TYPES
   = TE τ <$> (Promote τ <$> check e τ)  -- keeps the Promote nodes
#else
   = do (TE t e') <- infer e
        guardShow ("promote: " ++ show t ++ " << " ++ show τ) =<< t `isSubtype` τ
        return $ if t /= τ then promote τ $ TE t e'
                           else TE t e'  -- see NOTE [How to handle type annotations?] in Desugar
#endif

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


