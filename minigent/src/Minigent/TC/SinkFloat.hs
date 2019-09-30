-- |
-- Module      : Minigent.TC.SinkFloat
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- The sink/float phase of constraint solving.
--
-- May be used qualified or unqualified.
{-# LANGUAGE FlexibleContexts, TupleSections, ScopedTypeVariables #-}
module Minigent.TC.SinkFloat
  ( -- * Sink/Float Phase
    sinkFloat
  ) where

import Minigent.Syntax
import Minigent.Syntax.Utils
import qualified Minigent.Syntax.Utils.Row as Row
import qualified Minigent.Syntax.Utils.Rewrite as Rewrite

import Minigent.TC.Assign
import Minigent.Fresh
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Applicative
import Data.Foldable (asum)
import qualified Data.Map as M

-- | The sinkFloat phase propagates the structure of types containing
--   rows (i.e. Records and Variants) through subtyping/equality constraints
sinkFloat :: forall m. (MonadFresh VarName m, MonadWriter [Assign] m) => Rewrite.Rewrite' m [Constraint]
sinkFloat = Rewrite.rewrite' $ \cs -> do 
               (cs',as) <- tryEach cs
               tell as
               pure (map (constraintTypes (traverseType (foldMap substAssign as))) cs')
  where 
    tryEach :: [Constraint] -> MaybeT m ([Constraint], [Assign])
    tryEach [] = empty
    tryEach (c:cs) = (tryOne c >>= \(cs',as) -> pure (cs' ++ cs, as))
                 <|> fmap (\(cs,x) -> (c:cs,x)) (tryEach cs)
    
    tryOne :: Constraint -> MaybeT m ([Constraint], [Assign])
    tryOne c@(Record n r s :< v)
      | fs <- discardCommon v (getTaken r)
      , not (M.null fs) = rowConstraints (\r' -> Record n r' s) (:<) fs c v
    tryOne c@(v :< Record n r s) 
      | fs <- discardCommon v (getPresent r)
      , not (M.null fs) = rowConstraints (\r' -> Record n r' s) (flip (:<)) fs c v
    tryOne c@(Variant r :< v)
      | fs <- discardCommon v (getPresent r)
      , not (M.null fs) = rowConstraints Variant (:<) fs c v
    tryOne c@(v :< Variant r)
      | fs <- discardCommon v (getTaken r)
      , not (M.null fs) = rowConstraints Variant (flip (:<)) fs c v
    tryOne _                 = empty

    rowConstraints fRow fSub fs c v = do 
        v' <- fresh
        ts <- mapM (\x -> (x,) . UnifVar <$> fresh) fs
        let r' = Row (fmap (\(Entry n _ tk, u) -> (Entry n u tk)) ts) (Just v')
        as <- substOf v fRow r'
        let cs = map (\(Entry _ t _, u) -> t `fSub` u) $ M.elems ts
        pure (c : cs, as)

    substOf (UnifVar v) fRow t = pure [TyAssign v (fRow t)]
    substOf (Variant r) fRow t | Just v <- rowVar r 
                               = pure [RowAssign v t]
    substOf (Record _ r s) fRow t | Just v <- rowVar r 
                                = pure [RowAssign v t]
    substOf _ fRow t = empty

    discardCommon (UnifVar _)  fs = fs
    discardCommon (Record _ r _) fs = M.difference fs $ Row.entriesMap r
    discardCommon (Variant r)  fs = M.difference fs $ Row.entriesMap r
    discardCommon _ _             = M.empty

    getTaken   = M.filter (\(Entry _ _ t) -> t)     . Row.entriesMap
    getPresent = M.filter (\(Entry _ _ t) -> not t) . Row.entriesMap