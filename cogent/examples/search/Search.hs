module Main where

import Data.Foldable (foldl')
import Data.Monoid
import Data.Word

import Search_Shallow_Desugar

main = return ()


spec_find_str :: [Word8] -> CString -> Maybe Node
spec_find_str buf s = snd $ foldl' (\(restb, found) _ -> spec_cmp_inc restb found s) (buf, Nothing) buf

spec_cmp_inc :: [Word8] -> Maybe Node -> CString -> ([Word8], Maybe Node)
spec_cmp_inc buf (Just n) _ = (buf, Just n)
spec_cmp_inc buf Nothing  s = 
  case spec_deserialise_Node buf of
    Success (n, buf') -> if s `spec_string_cmp` key n then (buf', Just n) else (buf', Nothing)
    Error   err       -> (buf, Nothing)

spec_string_cmp :: CString -> CString -> Bool
spec_string_cmp = undefined


instance Functor (V16 e) where
  fmap _ (Error   e) = Error e
  fmap f (Success a) = Success (f a)

instance Applicative (V16 e) where
  pure = Success
  Error e <*> _ = Error e
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

eBufferBound :: ErrCode
eBufferBound = 1

spec_deserialise_U32 :: [Word8] -> R (Word32, [Word8]) ErrCode
spec_deserialise_U32 (b1:b2:b3:b4:bs) = Success (undefined, bs)
spec_deserialise_U32 _ = Error eBufferBound

spec_deserialise_CString :: [Word8] -> Word32 -> R (CString, [Word8]) ErrCode
spec_deserialise_CString = undefined
