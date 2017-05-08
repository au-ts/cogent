module BilbyFs_ShallowConsts_Desugar_Tuples where

-- hack! Should be a real `32 word' definition
type Word32 = Int

s_IFREG :: Word32
s_IFREG = 32768

s_IFDIR :: Word32
s_IFDIR = 16384

eRoFs :: Word32
eRoFs = 30

eNoMem :: Word32
eNoMem = 12

eBadF :: Word32
eBadF = 9

eInval :: Word32
eInval = 22

eIO :: Word32
eIO = 5
