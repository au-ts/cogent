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

{-# OPTIONS_GHC -Werror -Wall #-}
module Cogent.TypeCheck.Solver.SinkFloat ( sinkfloat ) where 

import Cogent.TypeCheck.Base 
import Cogent.TypeCheck.Solver.Goal 
import Cogent.TypeCheck.Solver.Monad
import qualified Cogent.TypeCheck.Solver.Rewrite as Rewrite
import qualified Cogent.TypeCheck.Row as Row
import qualified Cogent.TypeCheck.Subst as Subst
import Cogent.TypeCheck.Util

import Control.Applicative
import Control.Arrow (first)
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import qualified Data.Map as M
import Lens.Micro
import Text.PrettyPrint.ANSI.Leijen (text, pretty, (<+>))

sinkfloat :: Rewrite.RewriteT TcSolvM [Goal]
sinkfloat = Rewrite.rewrite' $ \cs -> do
  (cs',as) <- try_each cs
  tell as
  traceTc "solver" (text "Sink/Float writes subst:" <+> pretty as)
  pure (foldr (\a -> map (goal %~ Subst.applyC a)) cs' as)
 where
  try_each [] = empty
  try_each (c:cs) = MaybeT $ do
    m <- runMaybeT (try_one c)
    case m of
      Nothing       -> fmap (first (c:)) <$> runMaybeT (try_each cs)
      Just (cs',as) -> pure $ Just (cs' ++ cs, as)

  try_one g = case _goal g of
    R r s :< v
     | fs <- discard_common v $ get_taken r
     , not $ M.null fs
     -> make_constraints (flip R s) (:<) fs g v
    v :< R r s
     | fs <- discard_common v $ get_present r
     , not $ M.null fs
     -> make_constraints (flip R s) (flip (:<)) fs g v

    V r :< v
     | fs <- discard_common v $ get_present r
     , not $ M.null fs
     -> make_constraints V (:<) fs g v
    v :< V r
     | fs <- discard_common v $ get_taken r
     , not $ M.null fs
     -> make_constraints V (flip (:<)) fs g v

    _ -> empty

  make_constraints frow fsub fs g v = do
    v' <- lift solvFresh
    ts <- mapM (\t -> (,) t <$> lift solvFresh) fs
    let r' = Row.Row (fmap (\((fn,(_,tk)),u) -> (fn, (U u, tk))) ts) (Just v')
    as <- subst_of v frow r'
    let cs = fmap (\(_,((_,(t,_)),u)) -> fsub t (U u)) $ M.toList ts
    pure (g : fmap (derivedGoal g) cs, as)

  subst_of (U v) frow t
   = pure [Subst.ofType v (frow t)]
  subst_of (R r _) _ t
   | Just v <- Row.var r
   = pure [Subst.ofRow v t]
  subst_of (V r) _ t
   | Just v <- Row.var r
   = pure [Subst.ofRow v t]
  subst_of _ _ _
   = MaybeT $ pure Nothing

  get_taken    = get_fields True
  get_present  = get_fields False
  get_fields t = M.filter (\(_,(_,t')) -> t == t') . Row.entries

  discard_common (U _)   fs = fs
  discard_common (R r _) fs = M.difference fs $ Row.entries r
  discard_common (V r)   fs = M.difference fs $ Row.entries r
  discard_common _ _        = M.empty

