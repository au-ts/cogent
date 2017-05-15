{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
 
module Main where

import Control.Arrow    (first)
import Data.Foldable    (foldl')
import Data.Monoid
import Data.Word

import Search_Shallow_Desugar
import Util

spec_main = 
  case spec_find_str buffer "Cogent\NUL" of
    Nothing -> putStrLn "Not found!"
    Just nd -> putStrLn $ key nd
  where l1@(b10,b11,b12,b13) = readWord32 7
        l2@(b20,b21,b22,b23) = readWord32 3
        l3@(b30,b31,b32,b33) = l1
        buffer = [b10,b11,b12,b13] ++ map (fromIntegral . fromEnum) "Data61" ++ [0]
              ++ [b20,b21,b22,b23] ++ map (fromIntegral . fromEnum) "TS"     ++ [0]
              ++ [b30,b31,b32,b33] ++ map (fromIntegral . fromEnum) "Cogent" ++ [0]

main = 
  let (R12 _ r) = find_str (R13 {p1 = (), p2 = buffer, p3 = "Cogent\NUL"} :: R13 _ _ _)
  in case r of
       None _  -> putStrLn "Not found!"
       Some nd -> putStrLn $ key nd
  where l1@(b10,b11,b12,b13) = readWord32 7
        l2@(b20,b21,b22,b23) = readWord32 3
        l3@(b30,b31,b32,b33) = l1
        buffer = [b10,b11,b12,b13] ++ map (fromIntegral . fromEnum) "Data61" ++ [0]
              ++ [b20,b21,b22,b23] ++ map (fromIntegral . fromEnum) "TS"     ++ [0]
              ++ [b30,b31,b32,b33] ++ map (fromIntegral . fromEnum) "Cogent" ++ [0]





spec_find_str :: [Word8] -> CString -> Maybe Node
spec_find_str buf s = snd $ foldl' (\(restb, found) _ -> spec_cmp_inc restb found s) (buf, Nothing) buf

spec_cmp_inc :: [Word8] -> Maybe Node -> CString -> ([Word8], Maybe Node)
spec_cmp_inc buf (Just n) _ = (buf, Just n)
spec_cmp_inc buf Nothing  s = 
  case spec_deserialise_Node buf of
    Success (n, buf') -> if s `spec_string_cmp` key n then (buf', Just n) else (buf', Nothing)
    Error   err       -> (buf, Nothing)

spec_string_cmp :: CString -> CString -> Bool
spec_string_cmp = (==)


instance Functor (V16 e) where
  fmap _ (Error   e) = Error e
  fmap f (Success a) = Success (f a)

instance Applicative (V16 e) where
  pure = Success
  Error   e <*> _ = Error e
  Success f <*> a = fmap f a

instance Monad (V16 e) where
  return = pure
  Error e   >>= _ = Error e
  Success a >>= f = f a


spec_deserialise_Node :: [Word8] -> R (Node, [Word8]) ErrCode
spec_deserialise_Node buf = do
  (l, buf) <- spec_deserialise_U32 buf
  (k, buf) <- spec_deserialise_CString buf l
  return (R9 l k, buf)

spec_deserialise_U32 :: [Word8] -> R (Word32, [Word8]) ErrCode
spec_deserialise_U32 (b0:b1:b2:b3:bs) = Success (buildWord32 b0 b1 b2 b3, bs)
spec_deserialise_U32 _ = Error 1

spec_deserialise_CString :: [Word8] -> Word32 -> R (CString, [Word8]) ErrCode
spec_deserialise_CString buf len = 
  if fromIntegral len > length buf
    then Error 1
    else return $ (first $ map (toEnum . fromIntegral)) $ splitAt (fromIntegral len) buf
