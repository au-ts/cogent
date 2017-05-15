module Main where

import Control.Arrow    (first)
import Data.Foldable    (foldl')
import Data.Monoid
import Data.Word
import Foreign
import Foreign.Marshal
import Foreign.Ptr
import Foreign.Storable (peek, pokeByteOff)
import System.IO.Unsafe

import Debug.Trace

import Search_Shallow_Desugar

-- the following two functions are copied from hsdns package:
-- http://hackage.haskell.org/package/hsdns-1.6.1/docs/src/ADNS-Endian.html#readWord32
-- note that later versions don't have these functions


data Endian
  = LittleEndian                -- ^ byte order: @1234@
  | BigEndian                   -- ^ byte order: @4321@
  | PDPEndian                   -- ^ byte order: @3412@
  deriving (Show, Eq)

{-# NOINLINE endian #-}
endian :: Endian
endian =
  System.IO.Unsafe.unsafePerformIO $
    allocaArray (sizeOf (undefined :: Word32)) $ \p -> do
      let val = 0x01020304 :: Word32
      poke p val
      let p' = castPtr p :: Ptr Word8
      val' <- peekArray 4 p'
      case val' of
        (0x01:0x02:0x03:0x04:[]) -> return BigEndian
        (0x04:0x03:0x02:0x01:[]) -> return LittleEndian
        (0x03:0x04:0x01:0x02:[]) -> return PDPEndian
        _                        -> error "unknown endian"

readWord32 :: Word32 -> (Word8, Word8, Word8, Word8)
readWord32 n =
  let (b1,n1) = (n  .&. 255, n  `shiftR` 8)
      (b2,n2) = (n1 .&. 255, n1 `shiftR` 8)
      (b3,n3) = (n2 .&. 255, n2 `shiftR` 8)
      b4      = n3 .&. 255
  in
  case endian of
    BigEndian    -> (fromIntegral b4, fromIntegral b3, fromIntegral b2, fromIntegral b1)
    LittleEndian -> (fromIntegral b1, fromIntegral b2, fromIntegral b3, fromIntegral b4)
    PDPEndian    -> (fromIntegral b2, fromIntegral b1, fromIntegral b4, fromIntegral b3)
main = case spec_find_str buffer "Cogent\NUL" of
         Nothing -> putStrLn "Not found!"
         Just nd -> putStrLn $ key nd
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
  trace ("l = " ++ show l ++ "; key = " ++ show k) $ return (R9 l k, buf)

eBufferBound :: ErrCode
eBufferBound = 1


-- copied from random-source package: http://hackage.haskell.org/package/random-source-0.3.0.6/docs/src/Data-Random-Internal-Words.html#buildWord32
-- there're more auxilliary functions which come handy

{-# INLINE buildWord32 #-}
-- |Build a word out of 4 bytes.  No promises are made regarding the order
-- in which the bytes are stuffed.  Note that this means that a 'RandomSource'
-- or 'MonadRandom' making use of the default definition of 'getRandomWord', etc.,
-- may return different random values on different platforms when started 
-- with the same seed, depending on the platform's endianness.
buildWord32 :: Word8 -> Word8 -> Word8 -> Word8 -> Word32
buildWord32 b0 b1 b2 b3
    = unsafePerformIO . allocaBytes 4 $ \p -> do
        pokeByteOff p 0 b0
        pokeByteOff p 1 b1
        pokeByteOff p 2 b2
        pokeByteOff p 3 b3
        peek (castPtr p)


spec_deserialise_U32 :: [Word8] -> R (Word32, [Word8]) ErrCode
spec_deserialise_U32 (b0:b1:b2:b3:bs) = Success (buildWord32 b0 b1 b2 b3, bs)
spec_deserialise_U32 _ = Error eBufferBound

spec_deserialise_CString :: [Word8] -> Word32 -> R (CString, [Word8]) ErrCode
spec_deserialise_CString buf len = 
  if fromIntegral len > length buf
    then Error eBufferBound
    else return $ (first $ map (toEnum . fromIntegral)) $ splitAt (fromIntegral len) buf
