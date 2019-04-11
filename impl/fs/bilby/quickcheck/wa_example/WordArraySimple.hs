{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ImplicitParams #-}
{- LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures #-}
{- LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-missing-fields #-}
{- OPTIONS_GHC -F -pgmFderive -optF-F #-}

module WordArraySimple where

import Control.Exception (bracket)
import Control.Lens hiding (elements)
-- import Control.Monad.State
import Control.Monad (void)
import Control.Monad.Trans.Class (lift)
import Data.Either.Extra  -- extra-1.6
-- import Data.Function
import Data.Functor.Classes
import Data.Ix
import Data.List (genericDrop, genericTake)
import qualified Data.Set as S
-- import qualified Data.Set.Internal as S
import Enumerate
import Foreign hiding (void)
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc
import Foreign.Marshal.Unsafe (unsafeLocalState)
import Foreign.Ptr
import Foreign.Storable
import GHC.Generics
import Prelude as P
-- import QuickCheck.GenT
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Function
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad
import Corres
import Wa_FFI_Types
import Wa_FFI_Types_Abs
import Wa_FFI
import Util

-- import Debug.Trace

{- |
To run the REPL: 
> cabal v1-repl wa-example --ghc-options=" wa_example/build/wa.o"
-}


-- * Haskell specification

-- | The Haskell type for wordarrays
type WordArray e = [e]

data O = O_mallocFail
       | O_zeroLengthFail
       | O_good
       deriving (Show, Generic, Enumerable)

empty_array :: WordArray e
empty_array = []

hs_wordarray_create :: (?o :: O, Integral e) => Word32 -> Maybe (WordArray e)
hs_wordarray_create l
  | O_mallocFail <- ?o = Nothing
  | otherwise          = Just $ replicate (fromIntegral l) 0

hs_wordarray_create_nd :: (Integral e) => Word32 -> CogentMonad (Maybe (WordArray e))
hs_wordarray_create_nd 0 = return Nothing <|> return (Just [])  -- either nothing or empty array
hs_wordarray_create_nd l = return Nothing <|> return (Just (replicate (fromIntegral l) 0))

hs_wordarray_create_nz :: (Integral e, ?o :: O) => Word32 -> Maybe (WordArray e)
hs_wordarray_create_nz l
  | O_mallocFail <- ?o = Nothing
  | otherwise          = Just $ replicate (fromIntegral l) 0

hs_wordarray_free :: WordArray e -> ()
hs_wordarray_free _ = ()

hs_wordarray_get_bounded :: Integral e => WordArray e -> Word32 -> Maybe e
hs_wordarray_get_bounded xs i = 
  if i `is_inbound` xs then Just $ xs !! (fromIntegral i) else Nothing

is_inbound :: Word32 -> WordArray e -> Bool
is_inbound i xs = i >= 0 && i < fromIntegral (length xs)

hs_wordarray_modify :: WordArray e
                    -> Word32
                    -> ((e, acc, obsv) -> (e, acc))
                    -> acc
                    -> obsv
                    -> (WordArray e, acc)
hs_wordarray_modify xs i f acc obsv
  | i `is_inbound` xs = 
    let (e',acc') = f (xs !! fromIntegral i, acc, obsv)
     in (list_update xs i e', acc')
  | otherwise = P.error "out-of-bound index not allowed in wordarray_modify"

-- | __NOTE__: We also need to specify all inner functions used. As on the Cogent
-- side, due to the way higher-order function calls are made, we cannot generate
-- random functions for testing. The way we test higher-order functions is
-- to show that for all callable inner functions, the outer function behaves
-- correctly. 
--
-- In the case of @wordarray_modify@, @modify_bofy_f@ is the only callable
-- function. This can be seem in the @dispatch@ functions generated in the .h file. / zilinc
hs_modify_body_f :: (Word8, Word8, Bool) -> (Word8, Word8)
hs_modify_body_f (e, acc, obsv) =
  if obsv then (e + acc, e + acc) else (e, acc)

hs_wordarray_put :: WordArray e -> Word32 -> e -> Either (WordArray e) (WordArray e)
hs_wordarray_put xs i _ | not (i `is_inbound` xs) = Left xs
hs_wordarray_put xs i a = Right $ list_update xs i a

hs_wordarray_length :: WordArray e -> Word32
hs_wordarray_length = fromIntegral . length

hs_wordarray_clone :: (?o :: O) => WordArray e -> Maybe (WordArray e)
hs_wordarray_clone xs
  | O_mallocFail <- ?o = Nothing
  | otherwise          = Just xs

hs_wordarray_set :: WordArray a -> Word32 -> Word32 -> a -> WordArray a
hs_wordarray_set arr frm n a 
  | fromIntegral frm > length arr = arr 
  | fromIntegral (frm + n) > length arr = take (fromIntegral frm) arr ++ replicate (length arr - fromIntegral frm) a
  | otherwise = take (fromIntegral frm) arr ++ replicate (fromIntegral n) a ++ drop (fromIntegral $ frm + n) arr


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Testing @wordarray_set@

prop_corres_wordarray_set_u8 :: Property
prop_corres_wordarray_set_u8 = monadicIO $
  forAllM gen_wordarray_set_u8_arg' $ \ia -> run $ do
    let oa = uncurry4 hs_wordarray_set ia
    ic <- mk_c_wordarray_set_u8_arg ia
    oc <- cogent_wordarray_set_u8 ic
    corresM' rel_wordarray_u8 oa oc

rel_wordarray_u8 :: WordArray Word8 -> Ptr (CWordArray_u8) -> IO Bool
rel_wordarray_u8 hs_arr c_arr = do
  CWordArray_u8 len pvalues <- peek c_arr
  arr <- peekArray (fromIntegral len) pvalues
  return $ map fromIntegral hs_arr == arr

gen_wordarray_set_u8_arg' :: Gen ([Word8], Word32, Word32, Word8)
gen_wordarray_set_u8_arg' = do
  l <- choose (1, 200) :: Gen Word32
  arr <- vector $ fromIntegral l
  frm <- choose (0, 250)
  n <- choose (0, 150)
  a <- arbitrary :: Gen Word8
  return (arr, frm, n, a)

mk_c_wordarray_set_u8_arg :: ([Word8], Word32, Word32, Word8) -> IO (Ptr Ct5)
mk_c_wordarray_set_u8_arg (arr, frm, n, a) = do
  p_arr <- mk_c_wordarray_u8 arr
  new $ Ct5 p_arr (fromIntegral frm) (fromIntegral n) (fromIntegral a)

mk_c_wordarray_u8 :: [Word8] -> IO (Ptr CWordArray_u8)
mk_c_wordarray_u8 elems = do
  let l = length elems
  pvalues <- newArray (map fromIntegral elems :: [Cu8])
  new $ CWordArray_u8 (fromIntegral l) pvalues


-- /////////////////////////////////////////////////////////////////////////////
--
-- * Helper functions

list_update :: (Integral n) => [a] -> n -> a -> [a]
list_update [] i v = []
list_update (x:xs) i v = 
  case i of 0 -> v:xs
            k | k > 0 -> x : list_update xs (k-1) v
            k -> P.error "negative index"

-- /////////////////////////////////////////////////////////////////////////////
--
-- * Main function

return []
main = $quickCheckAll
