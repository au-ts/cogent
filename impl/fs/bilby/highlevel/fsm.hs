{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Foreign
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Data.Set as S
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad
import FFI (Ct432, Ct435)
import Fsop_Shallow_Desugar 
import WordArray


hs_fsm_init :: MountState -> FsmState -> Cogent_monad (Either ErrCode FsmState)
hs_fsm_init mount_st fsm_st = do
  nb_free_eb <- return $ nb_eb (super mount_st) - bilbyFsFirstLogEbNum
  (return $ Left eNoMem) `alternative` (return $ Right $ fsm_st { nb_free_eb })


r_result :: Either ErrCode FsmState -> Cogent_monad (Either ErrCode FsmState) -> Bool
r_result r1 r2 = r1 `member` r2

gen_MountState :: Gen MountState
gen_MountState = undefined

gen_FsmState :: Gen FsmState
gen_FsmState = undefined

prop_fsm_init_refine = forAll (gen_MountState) $ \mount_st ->
                       forAll (gen_FsmState) $ \fsm_st ->
                         cogent_fsm_init mount_st fsm_st `r_result` hs_fsm_init mount_st fsm_st

foreign import ccall unsafe "wrapper_pp_inferred.c fsm_init"
  c_fsm_init :: Ptr Ct432 -> IO (Ptr Ct435)

mk_fsm_init_arg :: MountState -> FsmState -> Ct432
mk_fsm_init_arg = undefined

mk_fsm_init_ret :: Ct432 -> Either ErrCode FsmState
mk_fsm_init_ret = undefined


cogent_fsm_init :: MountState -> FsmState -> Either ErrCode FsmState
cogent_fsm_init = undefined

