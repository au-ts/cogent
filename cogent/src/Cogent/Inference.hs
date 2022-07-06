--
-- Copyright 2018, Data61
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

module Cogent.Inference where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core
import Cogent.Dargent.Allocation
import Cogent.Dargent.Util
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
import Control.Monad.Fail
import Control.Monad.Reader hiding (fmap, forM_)
import Control.Monad.State hiding (fmap, forM_)
import Control.Monad.Trans.Maybe
import Data.Foldable (forM_)
import Data.Function (on)
import Data.List (nub)
import qualified Data.IntMap as IM
import Data.Map (Map)
import Data.Maybe (isJust)
import qualified Data.Map as M
import Data.Monoid
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable(traverse)
#endif
import Lens.Micro hiding (at)
import Lens.Micro.Mtl (view, use, (%=))
import Text.PrettyPrint.ANSI.Leijen (Pretty, pretty)
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)  -- NOTE: used safely to coerce phantom types only

import Debug.Trace

guardShow :: String -> Bool -> TC t v b ()
guardShow x b = unless b $ TC (throwError $ "GUARD: " ++ x)

guardShow' :: String -> [String] -> Bool -> TC t v b ()
guardShow' mh mb b = unless b $ TC (throwError $ "GUARD: " ++ mh ++ "\n" ++ unlines mb)

-- ----------------------------------------------------------------------------
-- Type reconstruction

-- Types that don't have the same representation / don't satisfy subtyping.
isUpcastable :: (Show b, Eq b) => Type t b -> Type t b -> TC t v b Bool
isUpcastable (TPrim p1) (TPrim p2) = return $ isSubtypePrim p1 p2
isUpcastable (TSum s1) (TSum s2) = do
  c1 <- flip allM s1 (\(c,(t,b)) -> case lookup c s2 of
          Nothing -> return False
          Just (t',b') -> (&&) <$> t `isSubtype` t' <*> pure (b == b'))
  c2 <- flip allM s2 (\(c,(t,b)) -> return $ case lookup c s1 of Nothing -> b; Just _ -> True)  -- other tags are all taken
  return $ c1 && c2
isUpcastable _ _ = return False

isSubtype :: (Show b, Eq b) => Type t b -> Type t b -> TC t v b Bool
isSubtype t1 t2 = runMaybeT (t1 `lub` t2) >>= \case Just t  -> return $ t == t2
                                                    Nothing -> return False

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
#ifdef BUILTIN_ARRAYS
    erp c (TArray t l s h) = TArray (erp c t) l s h
#endif
    erp _ t = t

bound :: (Show b, Eq b) => Bound -> Type t b -> Type t b -> MaybeT (TC t v b) (Type t b)
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
bound b (TSum s1) (TSum s2) | s1' <- M.fromList s1, s2' <- M.fromList s2, M.keys s1' == M.keys s2' = do
  let op = case b of LUB -> (&&); GLB -> (||)
  s <- flip3 unionWithKeyM s2' s1' $ \k (t1,b1) (t2,b2) -> (,) <$> bound b t1 t2 <*> pure (b1 `op` b2)
  return $ TSum $ M.toList s
bound b (TProduct t11 t12) (TProduct t21 t22) = TProduct <$> bound b t11 t21 <*> bound b t12 t22
bound b (TCon c1 t1 s1) (TCon c2 t2 s2) | c1 == c2, s1 == s2 = TCon c1 <$> zipWithM (bound b) t1 t2 <*> pure s1
bound b (TFun t1 s1) (TFun t2 s2) = TFun <$> bound (theOtherB b) t1 t2 <*> bound b s1 s2
-- At this point, we can assume recursive parameters and records agree
bound b t1@(TRecord rp fs s) t2@(TRPar v ctxt)    = return t2
bound b t1@(TRPar v ctxt)    t2@(TRecord rp fs s) = return t2
bound b t1@(TRPar v1 c1)     t2@(TRPar v2 c2)     = return t2
#ifdef BUILTIN_ARRAYS
bound b (TArray t1 l1 s1 mhole1) (TArray t2 l2 s2 mhole2)
  | l1 == l2, s1 == s2 = do
      t <- bound b t1 t2
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
#endif
bound _ t1 t2 = __impossible ("bound: not comparable:\n" ++ show t1 ++ "\n" ++ 
                              "----------------------------------------\n" ++ show t2 ++ "\n")

lub :: (Show b, Eq b) => Type t b -> Type t b -> MaybeT (TC t v b) (Type t b)
lub = bound LUB

glb :: (Show b, Eq b) => Type t b -> Type t b -> MaybeT (TC t v b) (Type t b)
glb = bound GLB

-- checkUExpr_B :: UntypedExpr -> TC t v Bool
-- checkUExpr_B (E (Op op [e])) = return True
-- checkUExpr_B (E (Op op [e1,e2])) = return True
-- checkUExpr_B _ = return True


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
#ifdef BUILTIN_ARRAYS
bang (TArray t l s tkns) = TArray (bang t) l (bangSigil s) tkns
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
#ifdef BUILTIN_ARRAYS
substitute vs (TArray t l s mhole) = TArray (substitute vs t) (substituteLE vs l) s (fmap (substituteLE vs) mhole)
#endif

substituteL :: [DataLayout BitRange] -> Type t b -> Type t b
substituteL ls (TCon n ts s)     = TCon n (map (substituteL ls) ts) s
substituteL ls (TFun ti to)      = TFun (substituteL ls ti) (substituteL ls to)
substituteL ls (TProduct t1 t2)  = TProduct (substituteL ls t1) (substituteL ls t2)
substituteL ls (TRecord rp ts s) = TRecord rp (map (second (first $ substituteL ls)) ts) (substituteS ls s)
substituteL ls (TSum ts)         = TSum (map (second (first $ substituteL ls)) ts)
#ifdef BUILTIN_ARRAYS
substituteL ls (TArray t l s mhole) = TArray (substituteL ls t) l (substituteS ls s) mhole
#endif
substituteL _  t                 = t

substituteS :: [DataLayout BitRange] -> Sigil (DataLayout BitRange) -> Sigil (DataLayout BitRange)
substituteS ls Unboxed = Unboxed
substituteS ls (Boxed b CLayout) = Boxed b CLayout
substituteS ls (Boxed b (Layout l)) = Boxed b . Layout $ substituteDL ls l
  
substituteDL :: [DataLayout BitRange] -> DataLayout' BitRange -> DataLayout' BitRange
substituteDL ls l = case l of
  VarLayout n s -> case ls !! (natToInt n) of
                   CLayout -> __impossible "substituteS in Inference: CLayout shouldn't be here"
                   Layout l -> offset s l
  SumLayout tag alts ->
    let altl = M.toList alts
        fns = fmap fst altl
        fis = fmap fst $ fmap snd altl
        fes = fmap snd $ fmap snd altl
     in SumLayout tag $ M.fromList (zip fns $ zip fis (fmap (substituteDL ls) fes))
  RecordLayout fs ->
    let fsl = M.toList fs
        fns = fmap fst fsl
        fes = fmap snd fsl
     in RecordLayout $ M.fromList (zip fns (fmap (substituteDL ls) fes))
#ifdef BUILTIN_ARRAYS
  ArrayLayout e l -> ArrayLayout  (substituteDL ls e) l
#endif
  _ -> l

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
  LTruncate t e      -> LTruncate (substitute vs t) (go e)
 where go = substituteLE vs

remove :: (Eq a) => a -> [(a,b)] -> [(a,b)]
remove k = filter ((/= k) . fst)

adjust :: (Eq a) => a -> (b -> b) -> [(a,b)] -> [(a,b)]
adjust k f = map (\(a,b) -> (a,) $ if a == k then f b else b)


newtype TC (t :: Nat) (v :: Nat) b x
  = TC {unTC :: ExceptT String
                        (ReaderT (Vec t Kind, Map FunName (FunctionType b))
                                 (State (Vec v (Maybe (Type t b)))))
                        x}
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus,
            MonadReader (Vec t Kind, Map FunName (FunctionType b)))

instance MonadFail (TC t v b) where
  fail = __impossible

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
opType opr ts = __impossible "opType"

useVariable :: Fin v -> TC t v b (Maybe (Type t b))
useVariable v = TC $ do ret <- (`at` v) <$> get
                        case ret of
                          Nothing -> return ret
                          Just t  -> do
                            ok <- canShare <$> unTC (kindcheck t)
                            unless ok $ modify (\s -> update s v Nothing)
                            return ret

funType :: CoreFunName -> TC t v b (Maybe (FunctionType b))
funType v = TC $ (M.lookup (unCoreFunName v) . snd) <$> ask

runTC :: TC t v b x
      -> (Vec t Kind, Map FunName (FunctionType b))
      -> Vec v (Maybe (Type t b))
      -> Either String (Vec v (Maybe (Type t b)), x)
runTC (TC a) readers st = case runState (runReaderT (runExceptT a) readers) st of
                            (Left x, s)  -> Left x
                            (Right x, s) -> Right (s,x)

-- XXX | tc_debug :: [Definition UntypedExpr a] -> IO ()
-- XXX | tc_debug = flip tc_debug' M.empty
-- XXX |   where
-- XXX |     tc_debug' :: [Definition UntypedExpr a] -> Map FunName FunctionType -> IO ()
-- XXX |     tc_debug' [] _ = putStrLn "tc2... OK!"
-- XXX |     tc_debug' ((FunDef _ fn ts t rt e):ds) reader =
-- XXX |       case runTC (infer e) (fmap snd ts, reader) (Cons (Just t) Nil) of
-- XXX |         Left x -> putStrLn $ "tc2... failed! Due to: " ++ x
-- XXX |         Right _ -> tc_debug' ds (M.insert fn (FT (fmap snd ts) t rt) reader)
-- XXX |     tc_debug' ((AbsDecl _ fn ts t rt):ds) reader = tc_debug' ds (M.insert fn (FT (fmap snd ts) t rt) reader)
-- XXX |     tc_debug' (_:ds) reader = tc_debug' ds reader

retype :: (Show b, Eq b, Pretty b, a ~ b)
       => [Definition TypedExpr a b]
       -> Either String [Definition TypedExpr a b]
retype ds = fmap fst $ tc $ map untypeD ds

tc :: (Show b, Eq b, Pretty b, a ~ b)
   => [Definition UntypedExpr a b]
   -> Either String ([Definition TypedExpr a b], Map FunName (FunctionType b))
tc = flip tc' M.empty
  where
    tc' :: (Show b, Eq b, Pretty b, a ~ b)
        => [Definition UntypedExpr a b]
        -> Map FunName (FunctionType b)  -- the reader
        -> Either String ([Definition TypedExpr a b], Map FunName (FunctionType b))
    tc' [] reader = return ([], reader)
    tc' ((FunDef attr fn ks ls t rt e):ds) reader =
      -- Enable recursion by inserting this function's type into the function type dictionary
      -- here
      let ft = FT (snd <$> ks) (Vec.length ls) [] t rt in
      case runTC (infer e >>= flip typecheck rt) (fmap snd ks, M.insert fn ft reader) (Cons (Just t) Nil) of
        Left x -> Left x
        Right (_, e') ->
           let c0 = zip (fmap (`VarLayout` 0) [Zero ..]) $ Vec.cvtToList ls <&> (^._2) in
           let cls = nub $ inferLayConstraints t ++ inferLayConstraints rt ++ inferLayConstraintsTE reader e' ++ c0 in
           let m = (M.insert fn (FT (fmap snd ks) (Vec.length ls) cls t rt) reader) in
           
             (first (FunDef attr fn ks ls t rt e':)) <$> tc' ds m
    tc' (d@(AbsDecl _ fn ks ls t rt):ds) reader =
      let cls = nub $ 
            (zip (fmap (`VarLayout` 0) [Zero ..]) $ Vec.cvtToList ls <&> (^._2))
            ++ inferLayConstraints t ++ inferLayConstraints rt 
      in      
      first (Unsafe.unsafeCoerce d:) <$>
        tc' ds (M.insert fn (FT (fmap snd ks) (Vec.length ls) cls t rt) reader)
    tc' (d:ds) reader = (first (Unsafe.unsafeCoerce d:)) <$> tc' ds reader

tc_ :: (Show b, Eq b, Pretty b, a ~ b)
    => [Definition UntypedExpr a b]
    -> Either String [Definition TypedExpr a b]
tc_ = fmap fst . tc

isMonoType :: Type t b -> Bool
isMonoType (TVar _) = False
isMonoType (TVarBang _) = False
isMonoType (TVarUnboxed _) = False
isMonoType (TCon _ l _) = all isMonoType l
isMonoType (TFun t rt) = isMonoType t && isMonoType rt
isMonoType (TPrim _) = True
isMonoType TString = True
isMonoType (TSum l) = all (isMonoType . fst . snd) l
isMonoType (TProduct t1 t2) = isMonoType t1 && isMonoType t2
isMonoType (TRecord _ fs _) = all (isMonoType . fst . snd) fs     
isMonoType TUnit = True
isMonoType (TRPar _ _)  = True -- TODO (not sure if something must be done)
isMonoType (TRParBang _ _) = True -- TODO (not sure if something must be done)
-- #ifdef BUILTIN_ARRAYS
isMonoType (TArray t _ s _) = isMonoType t -- TODO
isMonoType (TRefine t _) = isMonoType t -- TODO
-- #endif

isMonoDataLayout' :: DataLayout' BitRange -> Bool
isMonoDataLayout' UnitLayout = True
isMonoDataLayout' (PrimLayout _ _) = True
isMonoDataLayout' (RecordLayout fs) = all isMonoDataLayout' fs  
isMonoDataLayout' (SumLayout tag alts) = all (isMonoDataLayout' . snd) alts
isMonoDataLayout' (VarLayout v offset) = False
#ifdef BUILTIN_ARRAYS
isMonoDataLayout' (ArrayLayout l _) = isMonoDataLayout' l
#endif


-- TODO ne garder que les types/data layouts pas clos
inferLayConstraints :: Type t b -> [(DataLayout' BitRange, Type t b)]
inferLayConstraints (TVar _) = []
inferLayConstraints (TVarBang _) = []
inferLayConstraints (TVarUnboxed _) = []
inferLayConstraints (TCon _ l _) = concatMap inferLayConstraints l
inferLayConstraints (TFun t rt) = inferLayConstraints t ++ inferLayConstraints rt
inferLayConstraints (TPrim _) = []
inferLayConstraints TString = []
inferLayConstraints (TSum l) = concatMap (inferLayConstraints . fst . snd) l
inferLayConstraints (TProduct t1 t2) = inferLayConstraints t1 ++ inferLayConstraints t2
inferLayConstraints (TRecord r fs s) =    
    let cs = concatMap (inferLayConstraints . fst . snd) fs in
    case s of
      Boxed _ (Layout l) ->
            if isMonoDataLayout' l && all (isMonoType . fst . snd) fs then 
                cs
            else
                (l, TRecord r fs Unboxed) : cs
      _ -> cs
inferLayConstraints TUnit = []
inferLayConstraints (TRPar _ _)  = [] -- TODO (not sure if something must be done)
inferLayConstraints (TRParBang _ _) = [] -- TODO (not sure if something must be done)
-- #ifdef BUILTIN_ARRAYS
inferLayConstraints (TArray t _ s _) = [] -- TODO
inferLayConstraints (TRefine t _) = inferLayConstraints t
-- #endif

inferLayConstraintsTE :: Map FunName (FunctionType a) -> TypedExpr t v a a -> [(DataLayout' BitRange, Type t a)]
inferLayConstraintsTE m (TE t e) = inferLayConstraintsTE' m e ++ inferLayConstraints t



inferLayConstraintsTE' :: Map FunName (FunctionType a) -> Expr t v a a TypedExpr -> [(DataLayout' BitRange, Type t a)]
inferLayConstraintsTE' m (Variable _) = []
inferLayConstraintsTE' m (Fun f ts ls note) 
   | ExI (Flip ts') <- Vec.fromList ts  
   = 
        case M.lookup (unCoreFunName f) m of
          Just (FT ks nl lts _ _) ->
             case Vec.length ts' =? Vec.length ks
               of Just Refl ->
                     concatMap inferLayConstraints ts ++                         
                          map (substituteDL ls *** (substitute ts' . substituteL ls)) lts            
          _        -> error $ "Something went wrong in lookup of function type: '" ++ unCoreFunName f ++ "'"
inferLayConstraintsTE' m (Op _ l) = concatMap (inferLayConstraintsTE m) l
inferLayConstraintsTE' m (Con _ _ t) = inferLayConstraints t
inferLayConstraintsTE' m Unit = []
inferLayConstraintsTE' m (ILit _ _) = []
inferLayConstraintsTE' m (SLit _) = []
#ifdef BUILTIN_ARRAYS
inferLayConstraintsTE' m (ALit l) = concatMap (inferLayConstraintsTE m) l
inferLayConstraintsTE' m (ArrayIndex t u) = concatMap (inferLayConstraintsTE m) [t, u]
inferLayConstraintsTE' m (Pop _ t u) = concatMap (inferLayConstraintsTE m) [t, u]
inferLayConstraintsTE' m (Singleton t) = inferLayConstraintsTE t
-- TODO check de Bruijn indices
inferLayConstraintsTE' m (ArrayMap2 (_, e1) (e2, e3)) = concatMap (inferLayConstraintsTE m) [e1, e2, e3]
inferLayConstraintsTE' m (ArrayTake _ e1 e2 e3) = concatMap (inferLayConstraintsTE m) [e1, e2, e3]
inferLayConstraintsTE' m (ArrayPut _ e2 e3) = concatMap (inferLayConstraintsTE m) [e2, e3]
#endif
-- TODO check de Bruijn indices
inferLayConstraintsTE' m (Let _ t u) = inferLayConstraintsTE m t ++ inferLayConstraintsTE m u
inferLayConstraintsTE' m (LetBang _ _ t u) = inferLayConstraintsTE m t ++ inferLayConstraintsTE m u
inferLayConstraintsTE' m (Tuple t u) = inferLayConstraintsTE m t ++ inferLayConstraintsTE m u 
inferLayConstraintsTE' m (Struct l) = concatMap (inferLayConstraintsTE m . snd) l
inferLayConstraintsTE' m (If e1 e2 e3) =  concatMap (inferLayConstraintsTE m) [e1, e2, e3]
inferLayConstraintsTE' m (Case e1 _ (_, _, e2) (_, _, e3)) = 
      inferLayConstraintsTE m e1 ++ inferLayConstraintsTE m e2 ++ inferLayConstraintsTE m e3
inferLayConstraintsTE' m (Esac t) = inferLayConstraintsTE m t
inferLayConstraintsTE' m (Split _ e1 e2) = inferLayConstraintsTE m e1 ++ inferLayConstraintsTE m e2
inferLayConstraintsTE' m (Member e _) =  inferLayConstraintsTE m e
inferLayConstraintsTE' m (Take _ e1 _ e2) = inferLayConstraintsTE m e1 ++ inferLayConstraintsTE m e2
inferLayConstraintsTE' m (Put e1 _ e2) =  concatMap (inferLayConstraintsTE m) [e1, e2]
inferLayConstraintsTE' m (Promote t e) = inferLayConstraints t ++ inferLayConstraintsTE m e
inferLayConstraintsTE' m (Cast t e) = inferLayConstraints t ++ inferLayConstraintsTE m e
inferLayConstraintsTE' m (App t u) =  inferLayConstraintsTE m t ++ inferLayConstraintsTE m u 

tcConsts :: [CoreConst UntypedExpr]
         -> Map FunName (FunctionType VarName)
         -> Either String ([CoreConst TypedExpr], Map FunName (FunctionType VarName))
tcConsts [] reader = return ([], reader)
tcConsts ((v,e):ds) reader =
  case runTC (infer e) (Nil, reader) Nil of
    Left x -> Left x
    Right (_,e') -> (first ((v,e'):)) <$> tcConsts ds reader

withBinding :: Type t b -> TC t ('Suc v) b x -> TC t v b x
withBinding t x
  = TC $ do readers <- ask
            st      <- get
            case runTC x readers (Cons (Just t) st) of
              Left e -> throwError e
              Right (Cons Nothing s,r)   -> do put s; return r
              Right (Cons (Just t) s, r) -> do
                ok <- canDiscard <$> unTC (kindcheck t)
                if ok then put s >> return r
                      else throwError "Didn't use linear variable"

withBindings :: Vec k (Type t b) -> TC t (v :+: k) b x -> TC t v b x
withBindings Nil tc = tc
withBindings (Cons x xs) tc = withBindings xs (withBinding x tc)

withBang :: [Fin v] -> TC t v b x -> TC t v b x
withBang vs (TC x) = TC $ do st <- get
                             mapM_ (\v -> modify (modifyAt v (fmap bang))) vs
                             ret <- x
                             mapM_ (\v -> modify (modifyAt v (const $ st `at` v))) vs
                             return ret

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

#ifdef BUILTIN_ARRAYS
kindcheck_ f (TArray t l s _) = mappend <$> kindcheck_ f t <*> pure (sigilKind s)
#endif

kindcheck = kindcheck_ lookupKind


typecheck :: (Pretty a, Show a, Eq a) => TypedExpr t v a a -> Type t a -> TC t v a (TypedExpr t v a a)
typecheck e t = do
  let t' = exprType e
  isSub <- isSubtype t' t
  if | t == t' -> return e
     | isSub -> return (promote t e)
     | otherwise -> __impossible $ "Inferred type of\n" ++
                                   show (indent' $ pretty e) ++
                                   "\ndoesn't agree with the given type signature:\n" ++
                                   "Inferred type:\n" ++
                                   show (indent' $ pretty t') ++
                                   "\nGiven type:\n" ++
                                   show (indent' $ pretty t) ++ "\n"

infer :: (Pretty a, Show a, Eq a) => UntypedExpr t v a a -> TC t v a (TypedExpr t v a a)
infer (E (Op o es))
   = do es' <- mapM infer es
        let Just t = opType o (map exprType es')
        return (TE t (Op o es'))
infer (E (ILit i t)) = return (TE (TPrim t) (ILit i t))
infer (E (SLit s)) = return (TE TString (SLit s))
#ifdef BUILTIN_ARRAYS
infer (E (ALit [])) = __impossible "We don't allow 0-size array literals"
infer (E (ALit es))
   = do es' <- mapM infer es
        let ts = map exprType es'
            n = LILit (fromIntegral $ length es) (UInt 32)
        t <- lubAll ts
        isSub <- allM (`isSubtype` t) ts
        return (TE (TArray t n Unboxed Nothing) (ALit es'))
  where
    lubAll :: (Show b, Eq b) => [Type t b] -> TC t v b (Type t b)
    lubAll [] = __impossible "lubAll: empty list"
    lubAll [t] = return t
    lubAll (t1:t2:ts) = do Just t <- runMaybeT $ lub t1 t2
                           lubAll (t:ts)
infer (E (ArrayIndex arr idx))
   = do arr'@(TE ta _) <- infer arr
        let TArray te l _ _ = ta
        idx' <- infer idx
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
            ttl = TArray te (LOp Minus [l, LILit 1 (UInt 32)]) s tkns
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
        return (TE t (Variable v))
infer (E (Fun f ts ls note))
   | ExI (Flip ts') <- Vec.fromList ts
   , ExI (Flip ls') <- Vec.fromList ls
   = funType f >>= \case
       Just (FT ks nl lts ti to) ->
         case (Vec.length ts' =? Vec.length ks, Vec.length ls' =? nl)
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
        e2' <- withBinding (exprType e1') (infer e2)
        return $ TE (exprType e2') (Let a e1' e2')
infer (E (LetBang vs a e1 e2))
   = do e1' <- withBang (map fst vs) (infer e1)
        k <- kindcheck (exprType e1')
        guardShow "let!" $ canEscape k
        e2' <- withBinding (exprType e1') (infer e2)
        return $ TE (exprType e2') (LetBang vs a e1' e2')
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
        guardShow "if-1" $ exprType ec' == TPrim Boolean
        (et', ee') <- (,) <$> infer et <||> infer ee  -- have to use applicative functor, as they share the same initial env
        let tt = exprType et'
            te = exprType ee'
        Just tlub <- runMaybeT $ tt `lub` te
        isSub <- (&&) <$> tt `isSubtype` tlub <*> te `isSubtype` tlub
        guardShow' "if-2" ["Then type:", show (pretty tt) ++ ";", "else type:", show (pretty te)] isSub
        let et'' = if tt /= tlub then promote tlub et' else et'
            ee'' = if te /= tlub then promote tlub ee' else ee'
        return $ TE tlub (If ec' et'' ee'')
infer (E (Case e tag (lt,at,et) (le,ae,ee)))
   = do e' <- infer e
        let TSum ts = exprType e'
            Just (t, taken) = lookup tag ts
            restt = TSum $ adjust tag (second $ const True) ts  -- set the tag to taken
        let e'' = case taken of
                    True  -> promote (TSum $ OM.toList $ OM.adjust (\(t,True) -> (t,False)) tag $ OM.fromList ts) e'
                    False -> e'
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
        e2' <- withBindings (Cons tau (Cons (TRecord rp (init ++ (fn,(tau,True)):rest) s) Nil)) (infer e2)  -- take that field regardless of its shareability
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
infer (E (Cast ty e))
   = do (TE t e') <- infer e
        guardShow ("cast: " ++ show t ++ " <<< " ++ show ty) =<< t `isUpcastable` ty
        return $ TE ty (Cast ty $ TE t e')
infer (E (Truncate ty e))
   = do (TE t e') <- infer e
        guardShow ("truncate: " ++ show t ++ " >>> " ++ show ty) =<< ty `isUpcastable` t
        return $ TE ty (Truncate ty $ TE t e')
infer (E (Promote ty e))
   = do (TE t e') <- infer e
        guardShow ("promote: " ++ show t ++ " << " ++ show ty) =<< t `isSubtype` ty
        return $ if t /= ty then promote ty $ TE t e'
                            else TE t e'  -- see NOTE [How to handle type annotations?] in Desugar


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
  Let a e1 e2         -> TE t $ Let a e1 $ promote t e2
  LetBang vs a e1 e2  -> TE t $ LetBang vs a e1 $ promote t e2
  If ec et ee         -> TE t $ If ec (promote t et) (promote t ee)
  Case e tag (l1,a1,e1) (l2,a2,e2)
                      -> TE t $ Case e tag
                                  (l1, a1, promote t e1)
                                  (l2, a2, promote t e2)
  -- Collapse consecutive promotes
  Promote _ e'        -> promote t e'
  -- Otherwise, no simplification is necessary; construct a Promote expression as usual.
  _                   -> TE t $ Promote t (TE t' e)


