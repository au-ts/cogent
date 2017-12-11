{-# LANGUAGE PatternGuards #-}

module Kinds where

import Syntax

data Kind = Atom Singleton
          | Arrow Kind Kind
          -- Error
          | BadK

infixr `Arrow`

-- parameteriseTo :: [k1, k2, ... kn] -> k0 -> (k1 -> k2 -> ... -> kn -> k0)
parameteriseTo :: [Kind] -> Kind -> Kind
parameteriseTo [] k0 = k0
parameteriseTo (k:ks) k0 = k `Arrow` (ks `parameteriseTo` k0)

toFull :: Kind -> Kind
toFull (k0 `Arrow` ks) = toFull ks
toFull k@(Atom _) = k

instance Eq Kind where
    (Atom s1) == (Atom s2) = (s1 == s2)
    (Arrow k1 k1') == (Arrow k2 k2') = (k1 == k2) && (k1' == k2')
    BadK     == BadK     = True
    _ == _ = False

type CtnInfo = Maybe Kind
type TagInfo = Maybe (Integer, Integer)

data Singleton =
        -- Base types
          KBool
        | KUInt Integer Physable
        -- Array
        | KArray Kind
        -- Enumeration
        | KEnum  Kind
        -- Composite types
        | KStruct   Ident
        | KTUnion   Ident
        | KBitfield Ident CtnInfo
        | KBUnion   Ident CtnInfo TagInfo
        -- Always OK
        | KAny

instance Eq Singleton where
    KBool   == KBool   = True
    (KUInt 8 (Phys _)) == (KUInt 8 (Phys _)) = True
    (KUInt is1 en1)    == (KUInt is2 en2)    = (is1 == is2) && (en1 == en2)
    (KArray k1)  == (KArray k2)  = (k1 == k2)
    (KEnum  k1)  == (KEnum  k2)  = (k1 == k2)
    (KStruct   id1  ) == (KStruct   id2  ) = (id1 == id2)
    (KTUnion   id1  ) == (KTUnion   id2  ) = (id1 == id2)
    (KBitfield id1 _) == (KBitfield id2 _) = (id1 == id2)
    (KBUnion   id1 _ _) == (KBUnion   id2 _ _) = (id1 == id2)
    KAny     == _        = True
    _        == KAny     = True
    _        == _        = False

isAK :: Kind -> Bool
isAK (Atom _) = True
isAK _        = False

isBK :: Kind -> Bool
isBK (Atom KBool) = True
isBK k = isIK k

isIK :: Kind -> Bool
isIK (Atom (KUInt _ _)) = True
isIK _ = False

isIVK :: Kind -> Bool
isIVK (Atom (KUInt _ View)) = True
isIVK _ = False

isIPK :: Kind -> Bool
isIPK (Atom (KUInt _ (Phys _))) = True
isIPK _ = False

isPK :: Kind -> Bool
isPK (Atom (KArray    k    )) = isPK k
isPK (Atom (KStruct   _    )) = True
isPK (Atom (KTUnion   _    )) = True
isPK (Atom (KBitfield _ _  )) = True
isPK (Atom (KBUnion   _ _ _)) = True
isPK k = isIPK k

isPrimK :: Kind -> Bool
isPrimK k | isBK k = True
          | Atom (KBitfield _ _  ) <- k = True
          | Atom (KBUnion   _ _ _) <- k = True
          | otherwise = False

-- CAUTION: We could have the trick here that if size of an Integral type is 
--          big enough, it means the kind class of integral types
integral = Atom $ KUInt (fromIntegral (maxBound :: Int)) View

-- ASSERTION: Input kinds are integral
kle :: Kind -> Kind -> Bool
kle (Atom (KUInt is1 _)) (Atom (KUInt is2 _)) = is1 <= is2
kle _ _ = False

-- ASSERTION: Input kinds are integral
klt :: Kind -> Kind -> Bool
klt (Atom (KUInt is1 _)) (Atom (KUInt is2 _)) = is1 < is2
klt _ _ = False

-- Kind compatibility
kcomp :: Kind -> Kind -> Bool
-- kcomp (k1 `Arrow` k1s) (k2 `Arrow` k2s) = (k1 `kcomp` k2) && (k1s `kcomp` k2s)  -- we are first-order
kcomp (Atom (KArray k1)) (Atom (KArray k2)) = k1 `kcomp` k2
kcomp (Atom (KEnum  k1)) (Atom (KEnum  k2)) = k1 `kcomp` k2
kcomp k1 k2 | k1 == k2 = True
            | k1 `kle` k2 = True
            | otherwise = False

-- Returns corresponding view type
toV :: Kind -> Kind
toV k | isIPK k = case k of
                    Atom (KUInt is _) -> Atom (KUInt is View)
                    _ -> k
toV (Atom (KArray k)) = Atom $ KArray (toV k)
toV k = k

-- ASSERTION: Input kind is integral
sizeInt :: Kind -> Integer
sizeInt (Atom (KUInt is _)) = is
sizeInt _ = 0  -- FIXME!!!

maxInt :: Kind -> Kind -> Kind
maxInt k1 k2 | k2 `kle` k1 = k1
             | k1 `kle` k2 = k2
             | otherwise = BadK

maxInt' :: [Kind] -> Kind
maxInt' [k1, k2] = maxInt k1 k2
maxInt' (k1:k2:ks) = maxInt' $ (maxInt k1 k2):ks
maxInt' _ = BadK 

decInt :: Integer -> Maybe Kind
decInt n 
  | n >= 0 && n < 2^8 = Just $ Atom (KUInt 8 View)
  | n >= 2^8  && n < 2^16 = Just $ Atom (KUInt 16 View) -- FIXME: does not work with 24 bit extension
  | n >= 2^16 && n < 2^32 = Just $ Atom (KUInt 32 View)
  | n >= 2^32 && n < 2^64 = Just $ Atom (KUInt 64 View)
  | otherwise = Nothing 

lowerKind :: Kind -> Type
lowerKind k@(Atom s) | isBK k = s2t s
  where s2t :: Singleton -> Type
        s2t KBool = Bool
        s2t (KUInt is _) = UInt is View
lowerKind _ = error "ERROR: Cannot `lowerKind' non-base kind"

