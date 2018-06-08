--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

-- ALSO NOTE: This module contains code borrowed from varies packages. The copyright of the borrowed
-- code belongs to the original authors. URLs to the original source of code are included in the
-- comments.
-- Three majors reasons for not using the original packages:
--   1. modifications are necessary
--   2. the original package doesn't work
--   3. the original package is huge but we only need a tiny bit within it


{-# LANGUAGE DataKinds, FlexibleContexts, LambdaCase, PolyKinds, TupleSections, ViewPatterns #-}

module Cogent.Util where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
import Data.Monoid
#endif
import Control.Arrow ((&&&))
import Control.Lens
import Control.Monad
import Data.Char
import Data.Foldable (foldrM)
import qualified Data.Map as M
#if __GLASGOW_HASKELL__ < 803
import Data.Monoid ((<>))
#endif
import qualified Data.List as L
import Data.Version (showVersion)
import Generics.Pointless.MonadCombinators
import System.Environment
import System.FilePath.Posix

import Paths_cogent
import Version_cogent (gitHash)

--
-- functors

newtype Flip  f (a :: a') (b :: b') = Flip { unflip :: f b a }
newtype Flip2 f (a :: a') (b :: b') (c :: c') = Flip2 { unflip2 :: f c b a }
newtype Flip3 f (a :: a') (b :: b') (c :: c') (d :: d') = Flip3 { unflip3 :: f d c b a }

ffmap :: (Functor (Flip f a)) => (b -> b') -> f b a -> f b' a
ffmap f = unflip . fmap f . Flip

fffmap :: (Functor (Flip2 f a b)) => (c -> c') -> f c b a -> f c' b a
fffmap f = unflip2 . fmap f . Flip2

ffffmap :: (Functor (Flip3 f a b c)) => (d -> d') -> f d c b a -> f d' c b a
ffffmap f = unflip3 . fmap f . Flip3

mmapM :: (Traversable (Flip t a), Monad m) => (b -> m b') -> t b a -> m (t b' a)
mmapM f = return . unflip <=< mapM f . Flip

mmmapM :: (Traversable (Flip2 t a b), Monad m) => (c -> m c') -> t c b a -> m (t c' b a)
mmmapM f = return . unflip2 <=< mapM f . Flip2

mmmmapM :: (Traversable (Flip3 t a b c), Monad m) => (d -> m d') -> t d c b a -> m (t d' c b a)
mmmmapM f = return . unflip3 <=< mapM f . Flip3

ttraverse :: (Traversable (Flip f b), Applicative m) => (a -> m a') -> f a b -> m (f a' b)
ttraverse f = fmap unflip . traverse f . Flip

tttraverse :: (Traversable (Flip2 f c b), Applicative m) => (a -> m a') -> f a b c -> m (f a' b c)
tttraverse f = fmap unflip2 . traverse f . Flip2

ttttraverse :: (Traversable (Flip3 f d c b), Applicative m) => (a -> m a') -> f a b c d -> m (f a' b c d)
ttttraverse f = fmap unflip3 . traverse f . Flip3

--
-- name conversion

cap :: String -> String
cap [] = error "cap"
cap (h:t) = toUpper h : t

decap :: String -> String
decap [] = error "decap"
decap (h:t) = toLower h : t

toIsaName :: String -> String
toIsaName = cap . map (\c -> if c == '-' then '_' else c)

toCName :: String -> String
toCName = concatMap (\c -> if c == '\'' then "_prime" else [c])

--
-- file path

-- relDir src dst pwd: calculate path from dst to src (pwd must be absolute)
--   if src is absolute, then return absolute path of src
--   if src is relative (from pwd), then return relative path from dst
-- `makeRelative' doesn't behave exactly as I want
relDir :: FilePath -> FilePath -> FilePath -> FilePath
relDir src dst pwd
  | isAbsolute src = dropTrailingPathSeparator src
  | otherwise {- src is relative to pwd -} =
      if isAbsolute dst
        then dropTrailingPathSeparator $ pwd </> src
        else {- src' and dst' are both relative -}
          let src' = norm src
              dst' = norm dst
              pwd' = splitDirectories pwd
           in makeRel src' dst' pwd'
  where -- makeRelative ss ds ps: both ss and ds are normalised relative path segs, ps is absolute path segs
        makeRel ss ds ps = let (ss',ds') = dropCommonPrefix ss ds
                            in joinPath . norm $ (inverse ds' ps) </> (joinPath ss')

        -- It inherits preconditions from `makeRel' function
        -- Postconditions: neither path is empty
        dropCommonPrefix [] [] = (["."],["."])
        dropCommonPrefix [] ds = (["."],ds)
        dropCommonPrefix ss [] = (ss,["."])
        dropCommonPrefix (s:ss) (d:ds) = if s == d then dropCommonPrefix ss ds else (s:ss,d:ds)

        -- inverse ss ps: ss is normalised relative path segs, ps is current dir (absolute, at least ["/"])
        inverse ss ps = inverse' ss ps []

        inverse' [] _ is = is
        inverse' (s:ss) ps is  -- ss is not null
                  | "."  <- s, [] <- ss = "."
                  | "."  <- s = error "inverse: path must be norm'ed"
                  | ".." <- s = inverse' ss (init ps) $ last ps </> is
                  | otherwise = inverse' ss undefined $ ".." </> is  -- no ".." should ever appear in ss thus ps is useless

        -- norm: similar to System.FilePath.Posix.normalise, but also elimiate ".." as much as possible
        norm (splitDirectories . normalise -> ss) = case ss of
          []  -> error "norm: path cannot be empty"
          [_] -> ss
          ss  -> let (s1,s2) = break (== "..") ss
                  in case (s1,s2) of
                       (_,[]) -> ss  -- no ".." at all
                       ([],_) -> head s2 : norm (joinPath $ tail s2)  -- ".." is the leading segment
                       _  -> init s1 ++ norm (joinPath $ tail s2)

--
-- misc.

type Warning = String

firstM :: Functor f => (a -> f c) -> (a, b) -> f (c, b)
firstM f (x,y) = (,y) <$> f x

secondM :: Functor f => (b -> f c) -> (a, b) -> f (a, c)
secondM f (x,y) = (x,) <$> f y

fst3 :: (a,b,c) -> a
fst3 (a,b,c) = a

snd3 :: (a,b,c) -> b
snd3 (a,b,c) = b

thd3 :: (a,b,c) -> c
thd3 (a,b,c) = c

infixr 3 ***^^

(***^^) :: Applicative f => (a -> f a') -> (b -> f b') -> (a, b) -> f (a', b')
(***^^) fa fb (x,y) = (,) <$> fa x <*> fb y

first3 :: (a -> a') -> (a, b, c) -> (a', b, c)
first3 =  (_1 %~)

second3 :: (b -> b') -> (a, b, c) -> (a, b', c)
second3 = (_2 %~)

third3 :: (c -> c') -> (a, b, c) -> (a, b, c')
third3 = (_3 %~)

first4 :: (a -> a') -> (a, b, c, d) -> (a', b, c, d)
first4 = (_1 %~)

second4 :: (b -> b') -> (a, b, c, d) -> (a, b', c, d)
second4 = (_2 %~)

third4 :: (c -> c') -> (a, b, c, d) -> (a, b, c', d)
third4 = (_3 %~)

fourth4 :: (d -> d') -> (a, b, c, d) -> (a, b, c, d')
fourth4 = (_4 %~)

extTup3r :: d -> (a,b,c) -> (a,b,c,d)
extTup3r d (a,b,c) = (a,b,c,d)

extTup2l :: a -> (b,c) -> (a,b,c)
extTup2l a (b,c) = (a,b,c)

#if __GLASGOW_HASKELL__ < 803
concatTup2 :: Monoid a => (a, a) -> a
#else
concatTup2 :: Semigroup a => (a, a) -> a
#endif
concatTup2 (a1,a2) = a1 <> a2

whenM :: (Monad m, Monoid a) => Bool -> m a -> m a
whenM b ma = if b then ma else return mempty

whenMM :: (Monad m, Monoid a) => m Bool -> m a -> m a
whenMM mb ma = mb >>= flip whenM ma

-- modified version of `nubByM' stolen from 
-- <http://hackage.haskell.org/package/monadlist-0.0.2/docs/src/Control-Monad-ListM.html#nubByM>
nubByM :: (Monad m) => (a -> a -> m Bool) -> [a] -> m [a]
nubByM f [] = return []
nubByM f (x:xs) = liftM (x:) $ filterM (return . not <=< f x) xs >>= nubByM f

-- borrowed from The definitive-base package <http://hackage.haskell.org/package/definitive-base-2.3>
(<*=) :: Monad m => m a -> (a -> m b) -> m a
a <*= f = a >>= ((>>) <$> f <*> return)


fmapFold :: (Monoid m, Traversable t) => (a -> (m, b)) -> t a -> (m, t b)
fmapFold f = foldMap (fst . f) &&& fmap (snd . f)

fmapFoldM :: (Monoid m, Traversable t, Monad f) => (a -> f (m, b)) -> t a -> f (m, t b)
fmapFoldM f = foldMapM ((fst <$>) . f) /|\ traverse ((snd <$>) . f)

foldMapM :: (Monoid m, Foldable t, Monad f) => (a -> f m) -> t a -> f m
foldMapM f x = foldrM f' mempty x
  where f' a b = mappend <$> f a <*> return b

mapAccumLM :: (Monad m) => (a -> b -> m (a,c)) -> a -> [b] -> m (a, [c])
mapAccumLM f a (x:xs) = do 
    (a',c) <- f a x
    fmap (c:) <$> mapAccumLM f a' xs
mapAccumLM f a [] = pure (a, []) 

-- stdoutPath = "/dev/stdout"
-- nullPath = "/dev/null"

data Stage = STGParse | STGTypeCheck | STGDesugar | STGNormal | STGSimplify | STGMono | STGCodeGen
           deriving (Enum, Eq, Ord, Show)

type NameMod = String -> String


-- getCogentVersion - returns the version of Cogent
getCogentVersion = "Cogent development version: " ++ showVersion version ++ suffix
  where
    suffix = if gitHash == "" then "" else "-" ++ gitHash

-- getCogentVersionWithoutGit - return version of Cogent with git hash
getCogentVersionWithoutGit = "Cogent version: " ++ showVersion version

-- getStdGumDir
getHdrsDir :: IO FilePath
getHdrsDir = do dir <- getDataDir
                return (dir ++ "/" ++ "include")

overrideStdGumDirWith :: String -> IO FilePath
overrideStdGumDirWith envVar = do envValue <- lookupEnv envVar
                                  maybe getHdrsDir return envValue

getStdGumDir :: IO String
getStdGumDir = addTrailingPathSeparator <$> overrideStdGumDirWith "COGENT_STD_GUM_DIR"

getStdIncFullPath fp = do sdir <- getStdGumDir
                          return (sdir </> fp)

-- If the domain of some maps contains duplicate keys.
-- Returns Left ks for overlapping keys ks, Right ks for with the set of non-overlapping keys ks.
overlapping :: (Eq k) => [M.Map k v] -> Either [k] [k]
overlapping [] = Right []
overlapping (m:ms) = do
  vs <- overlapping ms
  let cap = vs `L.intersect` M.keys m
  if null cap then
    return (vs `L.union` M.keys m)
  else
    Left cap

u8MAX, u16MAX, u32MAX :: Integer
u8MAX  = 256
u16MAX = 65535
u32MAX = 4294967296

