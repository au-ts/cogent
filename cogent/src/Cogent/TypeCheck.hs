--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

module Cogent.TypeCheck where

import Cogent.TypeCheck.Generator
import Cogent.TypeCheck.Base

-- ----------------------------------------------------------------------------
-- custTyGen

typecheckCustTyGen :: [(LocType, String)] -> TC [(RawType, String)]
typecheckCustTyGen = mapM $ firstM $ \t ->
  if not (isMonoType t)
    then typeError (CustTyGenIsPolymorphic t)
    else isSynonym t >>= \case
           True -> typeError (CustTyGenIsSynonym t)
           _    -> validateType t

isMonoType :: LocType -> Bool
isMonoType (LocType _ (TVar {})) = False
isMonoType (LocType _ t) = getAll $ foldMap (All . isMonoType) t
isMonoType _ = __impossible "isMonoType: not a type at all"

isSynonym :: LocType -> TC Bool
isSynonym (LocType _ (TCon c _ _)) = lookup c <$> use knownTypes >>= \case
  Nothing -> __impossible "isSynonym: type not in scope"
  Just (vs,Just _ ) -> return True
  Just (vs,Nothing) -> return False
isSynonym (LocType _ t) = foldM (\b a -> (b ||) <$> isSynonym a) False t
isSynonym _ = __impossible "isSynonym: not a type at all"

