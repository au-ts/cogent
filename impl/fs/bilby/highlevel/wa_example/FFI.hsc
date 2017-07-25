{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module FFI where

import Foreign
import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types

#include "wa_wrapper_pp_inferred.c"

#enum Tag, Tag, TAG_ENUM_Break, TAG_ENUM_Error, TAG_ENUM_Iterate, TAG_ENUM_Success,

newtype CSysState = CSysState { dummy :: CChar } deriving Storable

newtype Tag = Tag Int deriving (Enum)
newtype Ctag_t = Ctag_t CInt deriving Storable
newtype Cunit_t = Cunit_t { dummy :: CInt } deriving Storable

instance Storable Ct27 where
  sizeOf    _ = (#size t27)
  alignment _ = (#alignment t27)
  peek ptr = Ct27 <$> (#peek t27, p1) ptr <*> (#peek t27, p2) ptr <*> (#peek t27, p3) ptr
  poke ptr (Ct27 p1 p2 p3) = do
    (#poke t27, p1) ptr p1
    (#poke t27, p2) ptr p2
    (#poke t27, p3) ptr p3
