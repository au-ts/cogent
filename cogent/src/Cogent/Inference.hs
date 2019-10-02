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
import Cogent.Util
import Data.Ex
import Data.Nat
import Data.PropEq
import Data.Vec hiding (repeat, splitAt, length, zipWith, zip, unzip)
import qualified Data.Vec as Vec

import Control.Applicative
import Control.Arrow
import Control.Monad.Except hiding (fmap, forM_)
import Control.Monad.Reader hiding (fmap, forM_)
import Control.Monad.State hiding (fmap, forM_)
import Control.Monad.Trans.Maybe
import Data.Foldable (forM_)
import Data.Function (on)
import Data.IntMap as IM (elems, fromList, unionWith)
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable(traverse)
#endif
import Lens.Micro (_2)
import Lens.Micro.Mtl (view)
import Text.PrettyPrint.ANSI.Leijen (pretty)
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)  -- NOTE: used safely to coerce phantom types only

import Debug.Trace

guardShow :: String -> Bool -> TC t v ()
guardShow x b = unless b $ TC (throwError $ "GUARD: " ++ x)

guardShow' :: String -> [String] -> Bool -> TC t v ()
guardShow' mh mb b = unless b $ TC (throwError $ "GUARD: " ++ mh ++ "\n" ++ unlines mb)

-- ----------------------------------------------------------------------------
-- Type reconstruction

-- Types that don't have the same representation / don't satisfy subtyping.
isUpcastable :: Type t -> Type t -> TC t v Bool
isUpcastable (TPrim p1) (TPrim p2) = return $ isSubtypePrim p1 p2
isUpcastable (TSum s1) (TSum s2) = do
  c1 <- flip allM s1 (\(c,(t,b)) -> case lookup c s2 of
          Nothing -> return False
          Just (t',b') -> (&&) <$> t `isSubtype` t' <*> pure (b == b'))
  c2 <- flip allM s2 (\(c,(t,b)) -> return $ case lookup c s1 of Nothing -> b; Just _ -> True)  -- other tags are all taken
  return $ c1 && c2
isUpcastable _ _ = return False

isSubtype :: Type t -> Type t -> TC t v Bool
isSubtype t1 t2 = runMaybeT (t1 `lub` t2) >>= \case Just t  -> return $ t == t2
                                                    Nothing -> return False

bound :: Bound -> Type t -> Type t -> MaybeT (TC t v) (Type t)
bound _ t1 t2 | t1 == t2 = return t1
bound b (TRecord fs1 s1) (TRecord fs2 s2) | map fst fs1 == map fst fs2, s1 == s2 = do
  let op = case b of LUB -> (||); GLB -> (&&)
  blob <- flip3 zipWithM fs2 fs1 $ \(f1,(t1,b1)) (_, (t2,b2)) -> do
    t <- bound b t1 t2
    ok <- lift $ if b1 == b2 then return True
                             else kindcheck t >>= \k -> return (canDiscard k)
    return ((f1, (t, b1 `op` b2)), ok)
  let (fs, oks) = unzip blob
  if and oks then return $ TRecord fs s1
             else MaybeT (return Nothing)
bound b (TSum s1) (TSum s2) | s1' <- M.fromList s1, s2' <- M.fromList s2, M.keys s1' == M.keys s2' = do
  let op = case b of LUB -> (&&); GLB -> (||)
  s <- flip3 unionWithKeyM s2' s1' $ \k (t1,b1) (t2,b2) -> (,) <$> bound b t1 t2 <*> pure (b1 `op` b2)
  return $ TSum $ M.toList s
bound b (TProduct t11 t12) (TProduct t21 t22) = TProduct <$> bound b t11 t21 <*> bound b t12 t22
bound b (TCon c1 t1 s1) (TCon c2 t2 s2) | c1 == c2, s1 == s2 = TCon c1 <$> zipWithM (bound b) t1 t2 <*> pure s1
bound b (TFun t1 s1) (TFun t2 s2) = TFun <$> bound (theOtherB b) t1 t2 <*> bound b s1 s2
#ifdef BUILTIN_ARRAYS
bound b (TArray t1 l1 s1 takens1) (TArray t2 l2 s2 takens2)
  | l1 == l2, s1 == s2 = do
      let op = case b of LUB -> (||); GLB -> (&&)
      t <- bound b t1 t2
      oks <- lift $ flip3 zipWithM (elems takens2) (elems takens1) $ \tk1 tk2 ->
               (if tk1 == tk2 then return True else
                   kindcheck t >>= \k -> return (canDiscard k))
      let takens = flip3 unionWith takens2 takens1 $ \tk1 tk2 -> tk1 `op` tk2
      if and oks then return $ TArray t l1 s1 takens
                 else MaybeT (return Nothing)
#endif
bound _ t1 t2 = __impossible ("bound: not comparable: " ++ show (t1,t2))

lub :: Type t -> Type t -> MaybeT (TC t v) (Type t)
lub = bound LUB

glb :: Type t -> Type t -> MaybeT (TC t v) (Type t)
glb = bound GLB

-- checkUExpr_B :: UntypedExpr -> TC t v Bool
-- checkUExpr_B (E (Op op [e])) = return True
-- checkUExpr_B (E (Op op [e1,e2])) = return True
-- checkUExpr_B _ = return True


bang :: Type t -> Type t
bang (TVar v)         = TVarBang v
bang (TVarBang v)     = TVarBang v
bang (TCon n ts s)    = TCon n (map bang ts) (bangSigil s)
bang (TFun ti to)     = TFun ti to
bang (TPrim i)        = TPrim i
bang (TString)        = TString
bang (TSum ts)        = TSum (map (second $ first bang) ts)
bang (TProduct t1 t2) = TProduct (bang t1) (bang t2)
bang (TRecord ts s)   = TRecord (map (second $ first bang) ts) (bangSigil s)
bang (TUnit)          = TUnit
#ifdef BUILTIN_ARRAYS
bang (TArray t l s tkns) = TArray (bang t) l (bangSigil s) tkns
#endif

substitute :: Vec t (Type u) -> Type t -> Type u
substitute vs (TVar v)         = vs `at` v
substitute vs (TVarBang v)     = bang (vs `at` v)
substitute vs (TCon n ts s)    = TCon n (map (substitute vs) ts) s
substitute vs (TFun ti to)     = TFun (substitute vs ti) (substitute vs to)
substitute _  (TPrim i)        = TPrim i
substitute _  (TString)        = TString
substitute vs (TProduct t1 t2) = TProduct (substitute vs t1) (substitute vs t2)
substitute vs (TRecord ts s)   = TRecord (map (second (first $ substitute vs)) ts) s
substitute vs (TSum ts)        = TSum (map (second (first $ substitute vs)) ts)
substitute _  (TUnit)          = TUnit
#ifdef BUILTIN_ARRAYS
substitute vs (TArray t l s tkns) = TArray (substitute vs t) l s tkns
#endif

remove :: (Eq a) => a -> [(a,b)] -> [(a,b)]
remove k = filter ((/= k) . fst)

adjust :: (Eq a) => a -> (b -> b) -> [(a,b)] -> [(a,b)]
adjust k f = map (\(a,b) -> (a,) $ if a == k then f b else b)

newtype TC (t :: Nat) (v :: Nat) a = TC {unTC :: ExceptT String
                                                         (ReaderT (Vec t Kind, Map FunName FunctionType)
                                                                  (State (Vec v (Maybe (Type t)))))
                                                         a}
                                   deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadReader (Vec t Kind, Map FunName FunctionType))

infixl 4 <||>
(<||>) :: TC t v (a -> b) -> TC t v a -> TC t v b
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

opType :: Op -> [Type t] -> Maybe (Type t)
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

useVariable :: Fin v -> TC t v (Maybe (Type t))
useVariable v = TC $ do ret <- (`at` v) <$> get
                        case ret of
                          Nothing -> return ret
                          Just t  -> do
                            ok <- canShare <$> unTC (kindcheck t)
                            unless ok $ modify (\s -> update s v Nothing)
                            return ret

funType :: CoreFunName -> TC t v (Maybe FunctionType)
funType v = TC $ (M.lookup (unCoreFunName v) . snd) <$> ask

runTC :: TC t v a -> (Vec t Kind, Map FunName FunctionType) -> Vec v (Maybe (Type t))
      -> Either String (Vec v (Maybe (Type t)), a)
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

retype :: [Definition TypedExpr a] -> Either String [Definition TypedExpr a]
retype ds = fmap fst $ tc $ map untypeD ds

tc :: [Definition UntypedExpr a] -> Either String ([Definition TypedExpr a], Map FunName FunctionType)
tc = flip tc' M.empty
  where
    tc' :: [Definition UntypedExpr a]
        -> Map FunName FunctionType    -- the reader
        -> Either String ([Definition TypedExpr a], Map FunName FunctionType)
    tc' [] reader = return ([], reader)
    tc' ((FunDef attr fn ts t rt e):ds) reader =
      case runTC (infer e >>= flip typecheck rt) (fmap snd ts, reader) (Cons (Just t) Nil) of
        Left x -> Left x
        Right (_, e') -> (first (FunDef attr fn ts t rt e':)) <$> tc' ds (M.insert fn (FT (fmap snd ts) t rt) reader)
    tc' (d@(AbsDecl _ fn ts t rt):ds) reader = (first (Unsafe.unsafeCoerce d:)) <$> tc' ds (M.insert fn (FT (fmap snd ts) t rt) reader)
    tc' (d:ds) reader = (first (Unsafe.unsafeCoerce d:)) <$> tc' ds reader

tc_ :: [Definition UntypedExpr a] -> Either String [Definition TypedExpr a]
tc_ = fmap fst . tc

tcConsts :: [CoreConst UntypedExpr]
         -> Map FunName FunctionType
         -> Either String ([CoreConst TypedExpr], Map FunName FunctionType)
tcConsts [] reader = return ([], reader)
tcConsts ((v,e):ds) reader =
  case runTC (infer e) (Nil, reader) Nil of
    Left x -> Left x
    Right (_,e') -> (first ((v,e'):)) <$> tcConsts ds reader

withBinding :: Type t -> TC t ('Suc v) x -> TC t v x
withBinding t a
  = TC $ do readers <- ask
            st      <- get
            case runTC a readers (Cons (Just t) st) of
              Left e -> throwError e
              Right (Cons Nothing s,r)   -> do put s; return r
              Right (Cons (Just t) s, r) -> do
                ok <- canDiscard <$> unTC (kindcheck t)
                if ok then put s >> return r
                      else throwError "Didn't use linear variable"

withBindings :: Vec k (Type t) -> TC t (v :+: k) x -> TC t v x
withBindings Nil tc = tc
withBindings (Cons x xs) tc = withBindings xs (withBinding x tc)

withBang :: [Fin v] -> TC t v x -> TC t v x
withBang vs (TC x) = TC $ do st <- get
                             mapM_ (\v -> modify (modifyAt v (fmap bang))) vs
                             ret <- x
                             mapM_ (\v -> modify (modifyAt v (const $ st `at` v))) vs
                             return ret

lookupKind :: Fin t -> TC t v Kind
lookupKind f = TC ((`at` f) . fst <$> ask)

kindcheck_ :: (Monad m) => (Fin t -> m Kind) -> Type t -> m Kind
kindcheck_ f (TVar v)         = f v
kindcheck_ f (TVarBang v)     = bangKind <$> f v
kindcheck_ f (TCon n vs s)    = mconcat <$> ((sigilKind s :) <$> mapM (kindcheck_ f) vs)
kindcheck_ f (TFun ti to)     = return mempty
kindcheck_ f (TPrim i)        = return mempty
kindcheck_ f (TString)        = return mempty
kindcheck_ f (TProduct t1 t2) = mappend <$> kindcheck_ f t1 <*> kindcheck_ f t2
kindcheck_ f (TRecord ts s)   = mconcat <$> ((sigilKind s :) <$> mapM (kindcheck_ f . fst . snd) (filter (not . snd . snd) ts))
kindcheck_ f (TSum ts)        = mconcat <$> mapM (kindcheck_ f . fst . snd) (filter (not . snd . snd) ts)
kindcheck_ f (TUnit)          = return mempty

#ifdef BUILTIN_ARRAYS
kindcheck_ f (TArray t l s _) = mappend <$> kindcheck_ f t <*> pure (sigilKind s)
#endif

kindcheck = kindcheck_ lookupKind


typecheck :: TypedExpr t v a -> Type t -> TC t v (TypedExpr t v a)
typecheck e t = do
  let t' = exprType e
  isSub <- isSubtype t' t
  if | t == t' -> return e
     | isSub -> return (promote t e)
     | otherwise -> __impossible "Inferred type doesn't agree with the given type signature"

infer :: UntypedExpr t v a -> TC t v (TypedExpr t v a)
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
            n = fromIntegral $ length es
        t <- lubAll ts
        isSub <- allM (`isSubtype` t) ts
        return (TE (TArray t n Unboxed (IM.fromList $ zip [1..fromIntegral n] (repeat False))) (ALit es'))
  where
    lubAll :: [Type t] -> TC t v (Type t)
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
                  True  -> TRecord (zipWith (\f t -> (f,(t,False))) tupleFieldNames [t1,t2]) Unboxed
        return $ TE t $ ArrayMap2 (as,f') (e1',e2')
infer (E (Pop a e1 e2))
   = do e1'@(TE t1 _) <- infer e1
        let TArray te l s tkns = t1
            thd = te
            ttl = TArray te (l - 1) s tkns
        guardShow "arr-pop on a singleton array" $ l > 1
        e2'@(TE t2 _) <- withBindings (Cons thd (Cons ttl Nil)) $ infer e2
        return (TE t2 (Pop a e1' e2'))
infer (E (Singleton e))
   = do e'@(TE t _) <- infer e
        let TArray te l _ _ = t
        guardShow "singleton on a non-singleton array" $ l == 1
        return (TE te (Singleton e'))
#endif
infer (E (Variable v))
   = do Just t <- useVariable (fst v)
        return (TE t (Variable v))
infer (E (Fun f ts note))
   | ExI (Flip ts') <- Vec.fromList ts
   = do myMap <- ask
        x <- funType f
        case x of
          Just (FT ks ti to) -> 
            ( case Vec.length ts' =? Vec.length ks
                of Just Refl -> let ti' = substitute ts' ti
                                    to' = substitute ts' to
                                in do forM_ (Vec.zip ts' ks) $ \(t, k) -> do
                                        k' <- kindcheck t
                                        when ((k <> k') /= k) $ __impossible "kind not matched in type instantiation"
                                      return $ TE (TFun ti' to') (Fun f ts note)
                   Nothing -> __impossible "lengths don't match")
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
            Just (t, False) = lookup tag ts  -- must not have been taken
            restt = TSum $ adjust tag (second $ const True) ts  -- set the tag to taken
        (et',ee') <- (,) <$>  withBinding t     (infer et)
                         <||> withBinding restt (infer ee)
        let tt = exprType et'
            te = exprType ee'
        Just tlub <- runMaybeT $ tt `lub` te
        isSub <- (&&) <$> tt `isSubtype` tlub <*> te `isSubtype` tlub
        guardShow' "case" ["Match type:", show (pretty tt) ++ ";", "rest type:", show (pretty te)] isSub
        let et'' = if tt /= tlub then promote tlub et' else et'
            ee'' = if te /= tlub then promote tlub ee' else ee'
        return $ TE tlub (Case e' tag (lt,at,et'') (le,ae,ee''))
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
        let TRecord fs _ = t
        guardShow "member-1" . canShare =<< kindcheck t
        guardShow "member-2" $ f < length fs
        let (_,(tau,c)) = fs !! f
        guardShow "member-3" $ not c  -- not taken
        return $ TE tau (Member e' f)
infer (E (Struct fs))
   = do let (ns,es) = unzip fs
        es' <- mapM infer es
        let ts' = zipWith (\n e' -> (n, (exprType e', False))) ns es'
        return $ TE (TRecord (sortBy (compare `on` fst) ts') Unboxed) $ Struct $ zip ns es'
infer (E (Take a e f e2))
   = do e'@(TE t _) <- infer e
        -- trace ("@@@@t is " ++ show t) $ return ()
        let TRecord ts s = t
        -- a common cause of this error is taking a field when you could have used member
        guardShow "take: sigil not readonly" $ not (readonly s)
        guardShow "take-1" $ f < length ts
        let (init, (fn,(tau,False)):rest) = splitAt f ts
        k <- kindcheck tau
        e2' <- withBindings (Cons tau (Cons (TRecord (init ++ (fn,(tau,True)):rest) s) Nil)) (infer e2)  -- take that field regardless of its shareability
        return $ TE (exprType e2') (Take a e' f e2')
infer (E (Put e1 f e2))
   = do e1'@(TE t1 _) <- infer e1
        let TRecord ts s = t1
        guardShow "put: sigil not readonly" $ not (readonly s)
        guardShow "put-1" $ f < length ts
        let (init, (fn,(tau,taken)):rest) = splitAt f ts
        k <- kindcheck tau
        unless taken $ guardShow "put-2" $ canDiscard k  -- if it's not taken, then it has to be discardable; if taken, then just put
        e2'@(TE t2 _) <- infer e2
        isSub <- t2 `isSubtype` tau
        guardShow "put-3" isSub
        let e2'' = if t2 /= tau then promote tau e2' else e2'
        return $ TE (TRecord (init ++ (fn,(tau,False)):rest) s) (Put e1' f e2'')  -- put it regardless
infer (E (Cast ty e))
   = do (TE t e') <- infer e
        guardShow ("cast: " ++ show t ++ " <<< " ++ show ty) =<< t `isUpcastable` ty
        return $ TE ty (Cast ty $ TE t e')
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
promote :: Type t -> TypedExpr t v a -> TypedExpr t v a
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

