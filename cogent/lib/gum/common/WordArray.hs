
module WordArray where

import Data.Either.Extra  -- extra-1.6

type U8 = Int

type WordArray a = [a]
type CString = WordArray U8

-- wordarray_create_nz
--

wordarray_get :: WordArray a -> Int -> a
wordarray_get xs i | is_inbound xs i = xs !! i
                   | otherwise = 0

wordarray_get_bounded :: WordArray a -> Int -> Maybe a
wordarray_get_bounded xs i =
  if is_inbound xs i then Just wordarray_get xs i
                     else Nothing

wordarray_modify :: WordArray a -> Int -> ((a, acc, obsv) -> (a, acc)) -> acc -> obsv -> (WordArray a, acc)
wordarray_modify xs i f acc obsv = 
  let (xs1,x:xs2) = splitAt i
      (x',acc') = f (x,acc,obsv)
   in (xs1 ++ x':xs2, acc')

is_inbound :: WordArray a -> Int -> Bool
is_inbound xs i = i < length xs

wordarray_put :: WordArray a -> Int -> a -> Either (WordArray a) (WordArray a)
wordarray_put xs i _ | not (is_inbound xs i) = Left xs
wordarray_put xs i a = let (xs1,x:xs2) = splitAt i
                        in (xs1 ++ a:xs2)

wordarray_put2 :: WordArray a -> Int -> a -> WordArray a
wordarray_put2 = (fromEither .) . wordarray_put

wordarray_length = length


