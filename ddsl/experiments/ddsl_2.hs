{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

import Control.Applicative hiding (empty)
import Control.Arrow (first, second)
import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import Data.List ((\\))

data Buf
data Index

type S = (Buf, Index)

newtype SM a = SM (ExceptT Buf (State S) a)
             deriving (Functor, Applicative, Monad, MonadError Buf, MonadState S)


type D = ([Obj], Index)

newtype DM a = DM (ExceptT () (State D) a)
             deriving (Functor, Applicative, Monad, MonadError (), MonadState D)

-- class Freeable a where
--   free :: a -> ()
--   free _ = ()

-- instance Freeable T2
-- instance Freeable T3

-- data Obj = forall a. Freeable a => Obj a 

data Obj = forall a. Obj a
-- deriving instance Eq  Obj
-- deriving instance Ord Obj

free :: Obj -> ()
free = const ()

type Pu8 = Int

type T1 = Pu8
data T2
data T3

deriving instance Eq T2
deriving instance Eq T3
deriving instance Ord T2
deriving instance Ord T3

data T = T { f1 :: T1, f2 :: T2, f3 :: T3 } deriving (Eq, Ord)
type T_taken = T

put_fields_T :: T_taken -> T1 -> T2 -> T3 -> DM T
put_fields_T v f1 f2 f3 = do 
  modify (first $ flip (\\) [Obj f1, Obj f2, Obj f3])
  return $ T f1 f2 f3

serialise_T1 :: T1 -> SM ()
serialise_T1 f1 = undefined

serialise_T2 :: T2 -> SM ()
serialise_T2 = undefined

serialise_T3 :: T3 -> SM ()
serialise_T3 = undefined

deserialise_T1 :: Buf -> DM T1
deserialise_T1 = undefined

deserialise_T2 :: Buf -> DM T2
deserialise_T2 = undefined

deserialise_T3 :: Buf -> DM T3
deserialise_T3 = undefined

assert :: Bool -> SM ()
assert b = if b then return ()
                else throwError =<< (fst <$> get)

check :: Bool -> DM ()
check b = if b then return () else throwError ()

serialise_T :: T -> SM ()
serialise_T v = assert (f1 v > 4) >>
                serialise_T1 (f1 v) >>
                serialise_T2 (f2 v) >>
                serialise_T3 (f3 v)

freeAll :: DM ()
freeAll = do
  (os, i) <- get
  case os of 
    [] -> return ()
    (x:xs) -> do return $ free x
                 put (xs, i)
                 freeAll

deserialise_T_into :: Buf -> T_taken -> DM T
deserialise_T_into b v = do
  f1 <- deserialise_T1 b
  f2 <- deserialise_T2 b
  f3 <- deserialise_T3 b
  v' <- put_fields_T v f1 f2 f3
  check (f1 > 4)
  return v'

mkT :: T
mkT = T undefined undefined undefined

malloc_T :: DM T
malloc_T = do t <- return mkT 
              modify (first $ (Obj t:))
              return t

deserialise_T :: Buf -> DM T
deserialise_T b = do
  v <- malloc_T
  deserialise_T_into b v



