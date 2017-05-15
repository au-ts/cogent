{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Arrow    (first)
import Data.Foldable    (foldl')
import Data.Monoid
import Data.Word
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Gen

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

keys :: [String]
keys = words "libpam-pwquality libpam-runtime libpam-sss libpam0g libpango-1.0-0 libpango1.0-0 libpangocairo-1.0-0 \
  \ libpangoft2-1.0-0 libpangox-1.0-0 libpangoxft-1.0-0 libparams-validationcompiler-perl \
  \ libparse-debianchangelog-perl libparted-fs-resize0 libparted2 libpath-tiny-perl libpci3 libpciaccess0 \
  \ libpcre16-3 libpcre2-8-0 libpcre3 libpcsclite1 libpeas-1.0-0 libperl5.24 libplist3 libplot2c2 libpng12-0 \
  \ libpng16-16 libpopt0 libpostproc54 libpotrace0 libprotobuf10 libproxy-tools libproxy1v5 libpst4 libptexenc1 \
  \ libpulse-mainloop-glib0 libpulse0 libpulsedsp libpwquality1 libpython-all-dev libpython-dev \
  \ libpython-stdlib libpython2.7 libpython2.7-dev libpython2.7-minimal libpython2.7-stdlib libpython3-stdlib \
  \ libpython3.5 libpython3.5-minimal libpython3.5-stdlib libqca2 libqca2-plugins libqt5dbus5 libqt5network5 \
  \ libqt5opengl5 libqt5printsupport5 libqt5svg5 libqt5xml5 libqtwebkit4 libquadmath0 libraptor2-0 librasqal3 \
  \ libraw1394-11 libraw15 librdf0 libreadline7 libroar2 librsvg2-2 librsvg2-common librtmp1 librubberband2 \
  \ libsamplerate0 libsane libsane-common libsane-extras libsane-extras-common libsasl2-2 libsasl2-modules \
  \ libsasl2-modules-db libsasl2-modules-gssapi-mit libscalar-list-utils-perl libsdl-image1.2 libsdl2-2.0-0 \
  \ libsecret-1-0 libsecret-common libselinux1 libsemanage-common libsemanage1 libsepol1 libsm6 libsmartcols1 \
  \ libsmbclient libsndfile1 libsodium18 libsombok3 libsoprano4 libsoup-gnome2.4-1 libsoup2.4-1 libsoxr0 \
  \ libspecio-perl libspeechd2 libspeex1 libspeexdsp1 libsqlite3-0 libss2 libssh-gcrypt-4 libssl1.0.0 \
  \ libssl1.0.2 libssl1.1 libsss-idmap0 libsss-nss-idmap0 libsss-sudo libstartup-notification0 libstdc++-6-dev"

bufGen :: [CString] -> Gen Buffer
bufGen ws = frequency [(1, badBufGen ws), (3, goodBufGen ws)]

goodBufGen ws = do
  ns <- elements [1..10] 
  ws' <- take ns <$> shuffle ws
  let ls = map ((\(b0,b1,b2,b3) -> b0:b1:b2:b3:[]) . readWord32 . fromIntegral . length) ws' :: [[Word8]]
      ks = map (map (fromIntegral . fromEnum)) ws' :: [[Word8]]
  return . concat $ zipWith (++) ls ks

badBufGen  ws = shuffle =<< goodBufGen ws

keyGen :: [CString] -> Gen CString
keyGen = elements

prop_find_str_refinement = forAll (bufGen keys) $ \buf ->
                           forAll (keyGen keys) $ \key ->
                             spec_find_str buf key `match_results` find_str (R13 () buf key)

match_results :: Maybe Node -> R12 SysState (V17 () (R9 Word32 CString)) -> Bool
match_results (Just n1) (R12 _ (Some n2)) = len n1 == len n2 && key n1 == key n2
match_results Nothing (R12 _ (None ())) = True
match_results _ _ = False


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
