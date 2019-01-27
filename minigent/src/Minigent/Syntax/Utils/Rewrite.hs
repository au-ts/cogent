-- |
-- Module      : Minigent.Syntax.Utils.Rewrite
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- Contains a mini-library for rewrites, that is, partial functions
-- from some type to the same type, which may access some external effects (such as fresh names)
-- through an underlying monad.
--
-- It can be imported qualified or unqualified.
module Minigent.Syntax.Utils.Rewrite
  ( -- * Types
    Rewrite
  , run
  , Rewrite' (..)
  , lift
  , -- * Composition
    andThen
  , untilFixedPoint
  , -- * Pre and Postprocessing
    pre
  , post
  , -- * Making Rewrites
    -- ** Pure Rewrites
    rewrite
  , pickOne
    -- ** Effectful Rewrites
  , rewrite'
  , pickOne'
  , withTransform
  , -- * Debugging
    debug
  ) where
import Control.Monad.Identity
import Control.Monad.Trans.Maybe
import Control.Applicative
import Debug.Trace

-- | Intuitively a @Rewrite a@ is a partial function from @a@ to @a@.
--   It can be composed disjuctively using the 'Semigroup' instance, or
--   sequentially using the 'andThen' function.
type Rewrite a = Rewrite' Identity a

-- | A @Rewrite' m a@ may in full generality access the effects of a monad @m@ while
--   attempting to rewrite values of type @a@.
newtype Rewrite' m a = Rewrite { run' :: a -> MaybeT m a }

-- | Disjunctive composition, that is: @r <> s@ will first attempt to rewrite with @r@.
--   If @r@ successfully rewrites, then the result of @r@ is returned. If @r@ does not
--   rewrite (i.e. it returns @Nothing@), then the second rewrite @s@ is attempted instead.
instance Monad m => Semigroup (Rewrite' m a) where
  Rewrite f <> Rewrite g = Rewrite (\a -> f a <|> g a)

-- | The 'mempty' is the rewrite that never successfully rewrites any term.
instance Monad m => Monoid (Rewrite' m a) where
  mempty = Rewrite (const empty)


-- | Run a function to post-process a rewrite's output.
post :: (Functor m) => (a -> a) -> Rewrite' m a -> Rewrite' m a
post op (Rewrite f) = Rewrite (fmap op . f)

-- | Run a function to pre-process a rewrite's input.
pre :: (Functor m) => (a -> a) -> Rewrite' m a -> Rewrite' m a
pre op (Rewrite f) = Rewrite (f . op)

-- | Sequential composition, that is: @r `andThen` s@ will first rewrite with @r@ and, if that
--   succeeds, rewrite the result with @s@. If either @r@ or @s@ fails to rewrite, the whole thing
--   fails to rewrite.
andThen :: Monad m => Rewrite' m a -> Rewrite' m a -> Rewrite' m a
andThen (Rewrite f) (Rewrite g) = Rewrite $ \x -> f x >>= g

-- | Given a partial function from @a@ to @a@, produce a @Rewrite'@ value.
rewrite :: Applicative m => (a -> Maybe a) -> Rewrite' m a
rewrite f = Rewrite (MaybeT . pure . f)

-- | Given a partial, effectful function from @a@ to @a@ in some monad @m@,
--   produce a @Rewrite'@ value.
rewrite' :: Applicative m => (a -> MaybeT m a) -> Rewrite' m a
rewrite' = Rewrite

-- | Given a non-effectful rewrite, returns a partial function.
--   For effectful rewrites, the 'run'' field can be used.
run :: Rewrite a -> a -> Maybe a
run rw = runIdentity . runMaybeT . run' rw

-- | A rewrite that exhausts itself only when it cannot rewrite anymore
untilFixedPoint :: Monad m => Rewrite' m a -> Rewrite' m a
untilFixedPoint rw = (rw `andThen` untilFixedPoint rw) <> rw

-- | A somewhat niche function. Given a /selector function/
--   which extracts a special value @a@ from a collection of items of type @x@,
--   rewrite that @a@ value into a new collection of @x@ values.
--
--   This function is usually applied to collections of constraints.
--   Given a set of constraints, we can identify soluble subproblems in the constraint
--   set, along with the set of other constraints that are not part of that subproblem.
--   This is the selector function.
--
--   After identifying the subproblem, we can reduce it into a smaller set of constraints
--   which are then merged with the leftover constraints from the selector function to
--   form the new constraint set.
withTransform :: Monad m => ([x] -> Maybe (a, [x])) -> (a -> MaybeT m [x]) -> Rewrite' m [x]
withTransform transform f = Rewrite $ \cs -> do
                              (c, cs1) <- MaybeT (pure (transform cs))
                              cs2 <- f c
                              pure (cs1 ++ cs2)

-- | Given a function that, given a value of type @x@, possibly returns many values of type @x@,
--   produce a rewrite that applies this wherever possible to a list of values of type @x@, merging
--   the results back into the list.
--
--   Typically applied to constraints, where individual reducible constraints are picked out
--   of the set and broken down into some subconstraints.
pickOne :: (x -> Maybe [x]) -> Rewrite [x]
pickOne f = pickOne' (MaybeT . pure . f)

-- | Just as 'pickOne', but with monadic effects like fresh names.
pickOne' :: Monad m => (x -> MaybeT m [x]) -> Rewrite' m [x]
pickOne' f = Rewrite each
  where
    each [] = empty
    each (c:cs) = MaybeT $ do
      m <- runMaybeT (f c)
      case m of
        Nothing  -> fmap (c:) <$> runMaybeT (each cs)
        Just cs' -> pure (Just (cs' ++ cs))

-- | Given a pure 'Rewrite', produce an effectful rewrite in any monad.
lift :: Applicative m => Rewrite a -> Rewrite' m a
lift (Rewrite f) = rewrite (runIdentity . runMaybeT . f)

-- | For debugging, prints the contents of the rewrite to the console, with a string prefix.
debug :: (Monad m) => String -> (a -> String) -> Rewrite' m a
debug pfx show = Rewrite (\cs -> case () of () | trace (pfx ++ ": " ++ show cs) False -> undefined
                                               | otherwise                            -> empty )
