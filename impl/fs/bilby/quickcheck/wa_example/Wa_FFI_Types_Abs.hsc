
module Wa_FFI_Types_Abs where

import Foreign
import Foreign.Ptr
import Foreign.C.String
import Foreign.C.Types
import Util

#include "wa_wrapper_pp_inferred.c"

data CWordArray_u8 = CWordArray_u8 { len :: CInt, values :: Ptr Cu8 }

instance Storable CWordArray_u8 where
  sizeOf _ = (#size WordArray_u8)
  alignment _ = (#alignment WordArray_u8)
  peek ptr = CWordArray_u8 <$> (#peek WordArray_u8, len) ptr <*> (#peek WordArray_u8, values) ptr
  poke ptr (CWordArray_u8 len values) = do
    (#poke WordArray_u8, len) ptr len
    (#poke WordArray_u8, values) ptr values

