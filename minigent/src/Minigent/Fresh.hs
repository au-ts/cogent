-- |
-- Module      : Minigent.Fresh
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- This module provides functionality for /fresh variable/ generation, for use in type inference, constraint
-- solving, code generation or elsewhere.
--
-- It exports a @transformers@-style /monad transformer/ 'FreshT', as well as an @mtl@ style
-- type class 'MonadFresh'. An alias 'Fresh' is also provided for cases where a full-blown
-- monad transformer is not needed.
--
-- It expects to be imported unqualified.
{-# LANGUAGE FunctionalDependencies, KindSignatures, FlexibleInstances,
             GeneralizedNewtypeDeriving, UndecidableInstances
#-}
module Minigent.Fresh
  ( -- * Monad Transformer
    FreshT
  , MonadFresh(..)
  , runFreshT
  , evalFreshT
    -- * Plain Monad
  , Fresh(..)
  , runFresh
  , evalFresh
    -- * Utility Functions
  , freshes
  ) where

import qualified Data.Stream as S

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Cont.Class
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State.Strict
import Control.Monad.Identity

-- | A @FreshT s m a@ is a monadic action that, on top of the underlying monad @m@, also may create
--   fresh values of type @s@, ultimately returning a value of type @a@.
--
--   Internally implemented as a state monad over an infinite 'S.Stream' of (assumed) unique values.
newtype FreshT s m a = FreshT (StateT (S.Stream s) m a)
        deriving ( Monad, Applicative, Functor
                 , Alternative, MonadPlus
                 , MonadFix, MonadIO, MonadTrans
                 , MonadCont, MonadError e
                 , MonadReader r, MonadWriter w
                 )

instance MonadState x m => MonadState x (FreshT s m) where
  get = FreshT (lift get)
  put x = FreshT (lift $ put x)

instance (Monad m, MonadFresh x m) => MonadFresh x (MaybeT m) where
  fresh = lift fresh
instance (Monad m, MonadFresh x m) => MonadFresh x (StateT s m) where
  fresh = lift fresh
instance (Monad m, MonadFresh x m) => MonadFresh x (ReaderT s m) where
  fresh = lift fresh
instance (Monad m, MonadFresh x m) => MonadFresh x (ExceptT s m) where
  fresh = lift fresh
instance (Monad m, Monoid s, MonadFresh x m) => MonadFresh x (WriterT s m) where
  fresh = lift fresh

instance Monad m => MonadFresh s (FreshT s m) where
  fresh = FreshT (state (\s -> (S.head s, S.tail s)))

-- | Any monad @m@ that is an instance of @MonadFresh s m@ may call the 'fresh' function, which will
--   return a unique value of type @s@.
--
--   Any transformer stack with a 'FreshT' somewhere in it is probably an instance of 'MonadFresh'
--   automatically.
class MonadFresh s (m :: * -> *) | m -> s where
  -- | Returns a unique value of type @s@ in the monad @m@.
  fresh :: m s


-- | Given an input 'S.Stream' of values, run a 'FreshT' computation, additionally returning the
--   remaining unused fresh values.
--
--   The given stream must never cycle or repeat values. That is, for a stream @s@ and indices
--   @m@ and @n@, @s ! m == s ! n@ if an only if @m == n@.
runFreshT :: Monad m => S.Stream s -> FreshT s m a -> m (a, S.Stream s)
runFreshT stream (FreshT st) = runStateT st stream
-- | Given an input 'S.Stream' of values, run a 'FreshT' computation, only returning the
--   result of the computation.
--
--   The given stream must never cycle or repeat values. That is, for a stream @s@ and indices
--   @m@ and @n@, @s ! m == s ! n@ if an only if @m == n@.
evalFreshT :: Monad m => S.Stream s -> FreshT s m a -> m a
evalFreshT stream (FreshT st) = evalStateT st stream

-- | An alias for convenience, where monad transformers are not required.
type Fresh s = FreshT s Identity

-- | Given an input 'S.Stream' of values, run a 'Fresh' computation, additionally returning the
--   remaining unused fresh values.
--
--   The given stream must never cycle or repeat values. That is, for a stream @s@ and indices
--   @m@ and @n@, @s ! m == s ! n@ if an only if @m == n@.
runFresh :: S.Stream s -> Fresh s a -> (a, S.Stream s)
runFresh stream = runIdentity . runFreshT stream

-- | Given an input 'S.Stream' of values, run a 'Fresh' computation, only returning the
--   result of the computation.
--
--   The given stream must never cycle or repeat values. That is, for a stream @s@ and indices
--   @m@ and @n@, @s ! m == s ! n@ if an only if @m == n@.
evalFresh :: S.Stream s -> Fresh s a -> a
evalFresh stream = runIdentity . evalFreshT stream

-- | @freshes n@ is equivalent to calling 'fresh' @n@ times, returning the results in a list.
freshes :: (Monad m, MonadFresh x m) => Int -> m [x]
freshes 0 = pure []
freshes n = (:) <$> fresh <*> freshes (n-1)
