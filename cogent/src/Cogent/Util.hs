--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE DataKinds, FlexibleContexts, LambdaCase, PolyKinds, TupleSections, ViewPatterns #-}

module Cogent.Util where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
import Data.Monoid
#endif
import Data.Char
import Data.Version (showVersion)
import System.Environment
import System.FilePath.Posix

import Version_cogent(gitHash)

import Paths_cogent

--
-- functors

newtype Flip  f (a :: a') (b :: b') = Flip { unflip :: f b a }
newtype Flip2 f (a :: a') (b :: b') (c :: c') = Flip2 { unflip2 :: f c b a }

ffmap :: (Functor (Flip f c)) => (a -> b) -> f a c -> f b c
ffmap f = unflip . fmap f . Flip

fffmap :: (Functor (Flip2 f a b)) => (c -> c') -> f c b a -> f c' b a
fffmap f = unflip2 . fmap f . Flip2

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
toCName = concat . map (\c -> if c == '\'' then "_prime" else [c])

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

infixr 3 ***^^

(***^^) :: Applicative f => (a -> f a') -> (b -> f b') -> (a, b) -> f (a', b')
(***^^) fa fb (x,y) = (,) <$> fa x <*> fb y

first3 :: (a -> a') -> (a, b, c) -> (a', b, c)
first3 f (a,b,c) = (f a,b,c)

second3 :: (b -> b') -> (a, b, c) -> (a, b', c)
second3  f (a,b,c) = (a,f b,c)

third3 :: (c -> c') -> (a, b, c) -> (a, b, c')
third3  f (a,b,c) = (a,b,f c)

first4 :: (a -> a') -> (a, b, c, d) -> (a', b, c, d)
first4 f (a,b,c,d) = (f a,b,c,d)

fst3 :: (a,b,c) -> a
fst3 (a,b,c) = a

snd3 :: (a,b,c) -> b
snd3 (a,b,c) = b

thd3 :: (a,b,c) -> c
thd3 (a,b,c) = c

extTup3 :: d -> (a,b,c) -> (a,b,c,d)
extTup3 d (a,b,c) = (a,b,c,d)

whenM :: (Monad m, Monoid a) => Bool -> m a -> m a
whenM b ma = if b then ma else return mempty

-- borrowed from The definitive-base package <http://hackage.haskell.org/package/definitive-base-2.3>
(<*=) :: Monad m => m a -> (a -> m b) -> m a
a <*= f = a >>= ((>>) <$> f <*> return)

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
