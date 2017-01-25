--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
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
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cogent.Inference where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import Cogent.Core
import Cogent.PrettyCore ()
import Cogent.Util
import Cogent.Vec hiding (splitAt, length, zipWith, zip, unzip)
import qualified Cogent.Vec as Vec

import Control.Applicative
import Control.Arrow
import Control.Monad.Except hiding (fmap, forM_)
import Control.Monad.Reader hiding (fmap, forM_)
import Control.Monad.State hiding (fmap, forM_)
-- import Data.Data hiding (Refl)
import Data.Foldable (forM_)
#if __GLASGOW_HASKELL__ < 709
import Data.Traversable(traverse)
#endif
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
-- import Data.Monoid.Cancellative
import Text.PrettyPrint.ANSI.Leijen (pretty)
import qualified Unsafe.Coerce as Unsafe (unsafeCoerce)  -- NOTE: used safely to coerce phantom types only

-- import Debug.Trace

guardShow :: String -> Bool -> TC t v ()
guardShow x b = if b then return () else TC (throwError $ "GUARD: " ++ x)

guardShow' :: String -> [String] -> Bool -> TC t v ()
guardShow' mh mb b = if b then return () else TC (throwError $ "GUARD: " ++ mh ++ "\n" ++ unlines mb)

isSubtype :: Type t -> Type t -> Bool
isSubtype (TPrim p1) (TPrim p2) = isSubtypePrim p1 p2
isSubtype (TSum  s1) (TSum  s2) = and $ zipWith (\(c1,(t1,b1)) (c2,(t2,b2)) -> (c1,t1) == (c2,t2) && b1 >= b2) s1 s2
isSubtype (TRecord r1 s1) (TRecord r2 s2) =
  s1 == s2 && and (zipWith (\(f1,(t1,b1)) (f2,(t2,b2)) -> (f1,t1) == (f2,t2) && b1 >= b2) r1 r2)
isSubtype a b = a == b

-- ----------------------------------------------------------------------------
-- Type reconstruction

bang :: Type t -> Type t
bang (TVar v)         = TVarBang v
bang (TVarBang v)     = TVarBang v
bang (TUnit)          = TUnit
bang (TProduct t1 t2) = TProduct (bang t1) (bang t2)
bang (TSum ts)        = TSum (map (second $ first bang) ts)
bang (TFun ti to)     = TFun ti to
bang (TRecord ts s)   = TRecord (map (second $ first bang) ts) (bangSigil s)
bang (TPrim i)        = TPrim i
bang (TString)        = TString
bang (TCon n ts s)    = TCon n (map bang ts) (bangSigil s)

substitute :: Vec t (Type u) -> Type t -> Type u
substitute vs (TVar v)         = vs `at` v
substitute vs (TVarBang v)     = bang (vs `at` v)
substitute _  (TUnit)          = TUnit
substitute vs (TProduct t1 t2) = TProduct (substitute vs t1) (substitute vs t2)
substitute vs (TSum ts)        = TSum (map (second (first $ substitute vs)) ts)
substitute vs (TFun ti to)     = TFun (substitute vs ti) (substitute vs to)
substitute vs (TRecord ts t)   = TRecord (map (second (first $ substitute vs)) ts) t
substitute vs (TCon n ps s)    = TCon n (map (substitute vs) ps) s
substitute _  (TPrim i)        = TPrim i
substitute _  (TString)        = TString

remove :: (Eq a) => a -> [(a,b)] -> [(a,b)]
remove k = filter ((/= k) . fst)

adjust :: (Eq a) => a -> (b -> b) -> [(a,b)] -> [(a,b)]
adjust k f = map (\(a,b) -> (a,) $ if a == k then f b else b)

newtype TC (t :: Nat) (v :: Nat) a = TC {unTC :: ExceptT String
                                                         (ReaderT (Vec t Kind, Map FunName FunctionType)
                                                                  (State (Vec v (Maybe (Type t)))))
                                                         a}
                                   deriving (Functor, Applicative, Alternative, Monad, MonadPlus)

infixl 4 <||>
(<||>) :: TC t v (a -> b) -> TC t v a -> TC t v b
(TC a) <||> (TC b) = TC $ do x <- get
                             f <- a
                             x1 <- get
                             put x
                             arg <- b
                             x2 <- get
                             unTC $ guardShow "<||>" $ x1 == x2
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
                            ok <- canShare <$> (unTC (kindcheck t))
                            when (not ok) $ modify (\s -> update s v Nothing)
                            return ret

funType :: FunName -> TC t v (Maybe FunctionType)
funType v = TC $ (M.lookup v . snd) <$> ask

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
-- XXX |       case runTC (typecheck e) (fmap snd ts, reader) (Cons (Just t) Nil) of
-- XXX |         Left x -> putStrLn $ "tc2... failed! Due to: " ++ x
-- XXX |         Right _ -> tc_debug' ds (M.insert fn (FT (fmap snd ts) t rt) reader)
-- XXX |     tc_debug' ((AbsDecl _ fn ts t rt):ds) reader = tc_debug' ds (M.insert fn (FT (fmap snd ts) t rt) reader)
-- XXX |     tc_debug' (_:ds) reader = tc_debug' ds reader

retype :: [Definition TypedExpr a] -> Either String [Definition TypedExpr a]
retype ds = fmap fst $ tc $ map untypeD ds

tc :: [Definition UntypedExpr a] -> Either String ([Definition TypedExpr a], Map FunName FunctionType)
tc = flip tc' M.empty
  where
    tc' :: [Definition UntypedExpr a] -> Map FunName FunctionType -> Either String ([Definition TypedExpr a], Map FunName FunctionType)
    tc' [] reader = return ([], reader)
    tc' ((FunDef attr fn ts t rt e):ds) reader =
      case runTC (typecheck e) (fmap snd ts, reader) (Cons (Just t) Nil) of
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
  case runTC (typecheck e) (Nil, reader) Nil of
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

kindcheck :: Type t -> TC t v Kind
kindcheck (TVar v)         = lookupKind v
kindcheck (TVarBang v)     = bangKind <$> lookupKind v
kindcheck (TUnit)          = return mempty
kindcheck (TProduct t1 t2) = mappend <$> kindcheck t1 <*> kindcheck t2
kindcheck (TSum ts)        = mconcat <$> mapM (kindcheck . fst . snd) (filter (not . snd . snd) ts)
kindcheck (TFun ti to)     = return mempty
kindcheck (TRecord ts s)   = mappend (sigilKind s) <$> (mconcat <$> (mapM (kindcheck . fst . snd) (filter (not . snd . snd) ts)))
kindcheck (TPrim i)        = return mempty
kindcheck (TString)        = return mempty
kindcheck (TCon n vs s)    = mapM_ kindcheck vs >> return (sigilKind s)

typecheck :: UntypedExpr t v a -> TC t v (TypedExpr t v a)
typecheck (E (Op o es))
   = do es' <- mapM typecheck es
        let Just t = opType o (map exprType es')
        return (TE t (Op o es'))
typecheck (E (ILit i t)) = return (TE (TPrim t) (ILit i t))
typecheck (E (SLit s)) = return (TE TString (SLit s))
typecheck (E (Variable v))
   = do Just t <- useVariable (fst v)
        return (TE t (Variable v))
typecheck (E (Fun f ts note))
   | ExI (Flip ts') <- Vec.fromList ts
   = do Just (FT ks ti to) <- funType f
        case Vec.length ts' =? Vec.length ks
          of Just Refl -> let ti' = substitute ts' ti
                              to' = substitute ts' to
                           in do forM_ (Vec.zip ts' ks) $ \(t, k) -> do
                                   k' <- kindcheck t
                                   when ((k <> k') /= k) $ fail "kind not matched in type instantiation"
                                 return $ TE (TFun ti' to') (Fun f ts note)
             Nothing -> fail "lengths don't match"
typecheck (E (App e1 e2))
   = do e1'@(TE (TFun ti to) _) <- typecheck e1
        e2'@(TE ti' _) <- typecheck e2
        guardShow "app" $ ti' == ti
        return $ TE to (App e1' e2')
typecheck (E (Let a e1 e2))
   = do e1' <- typecheck e1
        e2' <- withBinding (exprType e1') (typecheck e2)
        return $ TE (exprType e2') (Let a e1' e2')
typecheck (E (LetBang vs a e1 e2))
   = do e1' <- withBang (map fst vs) (typecheck e1)
        k <- kindcheck (exprType e1')
        guardShow "let!" $ canEscape k
        e2' <- withBinding (exprType e1') (typecheck e2)
        return $ TE (exprType e2') (LetBang vs a e1' e2')
typecheck (E Unit) = return $ TE TUnit Unit
typecheck (E (Tuple e1 e2))
   = do e1' <- typecheck e1
        e2' <- typecheck e2
        return $ TE (TProduct (exprType e1') (exprType e2')) (Tuple e1' e2')
typecheck (E (Con tag e))
   = do e' <- typecheck e
        return $ TE (TSum [(tag, (exprType e', False))]) (Con tag e')
typecheck (E (If ec et ee))
   = do ec' <- typecheck ec
        guardShow "if-1" $ exprType ec' == TPrim Boolean
        (et', ee') <- (,) <$> typecheck et <||> typecheck ee  -- have to use applicative functor, as they share the same initial env
        guardShow' "if-2" 
                   ["Then type:", show (pretty $ exprType et') ++ ";", "else type:", show (pretty $ exprType ee')] $ 
                   exprType et' == exprType ee'  -- promoted
        return $ TE (exprType et') (If ec' et' ee')
typecheck (E (Case e tag (lt,at,et) (le,ae,ee)))
   = do e' <- typecheck e
        let TSum ts = exprType e'
            Just (t, False) = lookup tag ts  -- must not have been taken
            restt = TSum $ adjust tag (second $ const True) ts  -- set the tag to taken
        (et',ee') <- (,) <$>  withBinding t     (typecheck et)
                         <||> withBinding restt (typecheck ee)
        guardShow' "case" 
                   ["Match type:", show (pretty $ exprType et') ++ ";", "unmatch type:", show (pretty $ exprType ee')] $ 
                   exprType et' == exprType ee'  -- promoted
        return $ TE (exprType et') (Case e' tag (lt,at,et') (le,ae,ee'))
typecheck (E (Esac e))
   = do e'@(TE (TSum [(_,(t,False))]) _) <- typecheck e
        return $ TE t (Esac e')
typecheck (E (Split a e1 e2))
   = do e1' <- typecheck e1
        let (TProduct t1 t2) = exprType e1'
        e2' <- withBindings (Cons t1 (Cons t2 Nil)) (typecheck e2)
        return $ TE (exprType e2') (Split a e1' e2')
typecheck (E (Member e f))
   = do e'@(TE t@(TRecord ts s) _) <- typecheck e  -- canShare
        guardShow "member-1" . canShare =<< kindcheck t
        guardShow "member-2" $ f < length ts
        let (_,(tau,c)) = ts !! f
        guardShow "member-3" $ not c  -- not taken
        return $ TE tau (Member e' f)
typecheck (E (Struct fs))
   = do let (ns,es) = unzip fs
        es' <- mapM typecheck es
        return $ TE (TRecord (zipWith (\n e' -> (n, (exprType e', False))) ns es') Unboxed) $ Struct $ zip ns es'
typecheck (E (Take a e f e2))
   = do e' <- typecheck e
        let (TE (TRecord ts s) _) = e'
        guardShow "take-1" $ s /= ReadOnly
        guardShow "take-2" $ f < length ts
        let (init, (fn,(tau,False)):rest) = splitAt f ts
        k <- kindcheck tau
        e2' <- withBindings (Cons tau (Cons (TRecord (init ++ (fn,(tau,True )):rest) s) Nil)) (typecheck e2)  -- take that field regardless of its shareability
        return $ TE (exprType e2') (Take a e' f e2')
typecheck (E (Put e1 f e2))
   = do e1'@(TE (TRecord ts s) _) <- typecheck e1
        guardShow "put-1" $ f < length ts
        let (init, (fn,(tau,taken)):rest) = splitAt f ts
        k <- kindcheck tau
        when (not taken) $ guardShow "put-2" $ canDiscard k  -- if it's not taken, then it has to be discardable; if taken, then just put
        e2' <- typecheck e2
        guardShow "put-3" $ exprType e2' == tau
        return $ TE (TRecord (init ++ (fn,(tau,False)):rest) s) (Put e1' f e2')  -- put it regardless
typecheck (E (Promote ty e))
   = do (TE t e') <- typecheck e
        guardShow "promote" $ t `isSubtype` ty
        return $ TE ty (Promote ty $ TE t e')

