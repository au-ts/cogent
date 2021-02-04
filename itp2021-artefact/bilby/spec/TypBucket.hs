module TypBucket (
  module TypBucket
, module BilbyFs_ShallowConsts_Desugar_Tuples  
) where

import BilbyFs_ShallowConsts_Desugar_Tuples

-- FIXME
type U8  = Int
type U16 = Int
type U32 = Int
type U64 = Int

type ErrCode = U32

type Ino   = U32
type Mode  = U32
type SizeT = U32
type TimeT = U32
type Addr  = U32


