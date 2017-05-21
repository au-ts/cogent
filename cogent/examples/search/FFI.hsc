{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module FFI where

import Foreign
import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types

#include "main_pp_inferred.c"

#enum Tag, Tag, TAG_ENUM_Break, TAG_ENUM_Error, TAG_ENUM_Iterate, TAG_ENUM_None, TAG_ENUM_Some, TAG_ENUM_Success

newtype CSysState = CSysState { dummy :: CChar } deriving Storable
type CBuffer = ()
type CCString = Ptr CChar
data Ct27 = Ct27 { p1 :: Ptr CSysState, p2 :: Ptr CBuffer, p3 :: CCString }

newtype Tag = Tag Int deriving (Enum)

{-
data Ctag = TAG_ENUM_Break
          | TAG_ENUM_Error
          | TAG_ENUM_Iterate
          | TAG_ENUM_None
          | TAG_ENUM_Some
          | TAG_ENUM_Success
          deriving (Enum)
-}

newtype Ctag_t = Ctag_t CInt deriving Storable
newtype Cunit_t = Cunit_t { dummy :: CInt } deriving Storable
data Ct4  = Ct4  { len :: Word32, key :: CCString }
data Ct28 = Ct28 { tag :: Ctag_t, none :: Cunit_t, some :: Ptr Ct4 }
data Ct29 = Ct29 { p1 :: Ptr CSysState, p2 :: Ct28 }

instance Storable Ct27 where
  sizeOf    _ = (#size t27)
  alignment _ = (#alignment t27)
  peek ptr = Ct27 <$> (#peek t27, p1) ptr <*> (#peek t27, p2) ptr <*> (#peek t27, p3) ptr
  poke ptr (Ct27 p1 p2 p3) = do
    (#poke t27, p1) ptr p1
    (#poke t27, p2) ptr p2
    (#poke t27, p3) ptr p3

instance Storable Ct4 where
  sizeOf    _ = (#size t4)
  alignment _ = (#alignment t4)
  peek ptr = Ct4 <$> (#peek t4, len) ptr <*> (#peek t4, key) ptr
  poke ptr (Ct4 len key) = (#poke t4, len) ptr len >> (#poke t4, key) ptr key

instance Storable Ct28 where
  sizeOf    _ = (#size t28)
  alignment _ = (#alignment t28)
  peek ptr = Ct28 <$> (#peek t28, tag) ptr <*> (#peek t28, None) ptr <*> (#peek t28, Some) ptr
  poke ptr (Ct28 tag none some) = do
    (#poke t28, tag ) ptr tag
    (#poke t28, None) ptr none
    (#poke t28, Some) ptr some

instance Storable Ct29 where
  sizeOf    _ = (#size t29)
  alignment _ = (#alignment t29)
  peek ptr = Ct29 <$> (#peek t29, p1) ptr <*> (#peek t29, p2) ptr
  poke ptr (Ct29 p1 p2) = do
    (#poke t29, p1) ptr p1
    (#poke t29, p2) ptr p2
