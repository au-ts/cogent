{-# LANGUAGE PackageImports #-}

module Main where

import "cogent-quickcheck" WordArray
import Test.QuickCheck hiding (Success)

-- /////////////////////////////////////////////////////////////////////////////
--
-- * Main function

main = do quickCheck prop_corres_wordarray_create_u8
          quickCheck prop_corres_wordarray_create_u8_nd
          quickCheck prop_equiv_wordarray_create_u8
          quickCheck prop_corres_wordarray_create_nz_u8
          quickCheck prop_corres_wordarray_get_bounded_u8
          quickCheck prop_corres_wordarray_get_bounded_u8'
          quickCheck prop_corres_wordarray_put_u8
          quickCheck prop_corres_wordarray_set_u8
          quickCheck prop_corres_wordarray_copy_u8
          quickCheck prop_corres_wordarray_modify_u8
          quickCheck prop_corres_wordarray_map_u8
          quickCheck prop_wordarray_get_put
