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


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cogent.Util where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>))
import Data.Monoid
#elif __GLASGOW_HASKELL__ < 803
import Data.Monoid ((<>))
#endif

import Control.Applicative (Alternative, empty)
import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.Writer
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Except (ExceptT(ExceptT))
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Char
import Data.Foldable (foldrM, toList)
import Data.IntMap as IM (IntMap, mapKeys, delete)
import qualified Data.Map as M
import Data.Version (showVersion)
import qualified Data.List as L
import GHC.Generics (Generic)
import System.Environment
import System.FilePath.Posix
import Lens.Micro
import Lens.Micro.Mtl

import Version_cogent (gitHash, configFlags)
import Paths_cogent

import Text.Parsec (SourcePos)

(<<+=) l n = l <<%= (+ n)

--
-- functors

newtype Flip  f (a :: a') (b :: b') = Flip { unflip :: f b a }
newtype Flip2 f (a :: a') (b :: b') (c :: c') = Flip2 { unflip2 :: f c b a }
newtype Flip3 f (a :: a') (b :: b') (c :: c') (d :: d') = Flip3 { unflip3 :: f d c b a }
newtype Flip4 f (a :: a') (b :: b') (c :: c') (d :: d') (e :: e') = Flip4 { unflip4 :: f e d c b a }

flip3 :: (a -> b -> c -> d) -> c -> b -> a -> d
flip3 f c b a = f a b c

ffmap :: (Functor (Flip f a)) => (b -> b') -> f b a -> f b' a
ffmap f = unflip . fmap f . Flip

fffmap :: (Functor (Flip2 f a b)) => (c -> c') -> f c b a -> f c' b a
fffmap f = unflip2 . fmap f . Flip2

ffffmap :: (Functor (Flip3 f a b c)) => (d -> d') -> f d c b a -> f d' c b a
ffffmap f = unflip3 . fmap f . Flip3

fffffmap :: (Functor (Flip4 f a b c d)) => (e -> e') -> f e d c b a -> f e' d c b a
fffffmap f = unflip4 . fmap f . Flip4

mmapM :: (Traversable (Flip t a), Monad m) => (b -> m b') -> t b a -> m (t b' a)
mmapM f = return . unflip <=< mapM f . Flip

mmmapM :: (Traversable (Flip2 t a b), Monad m) => (c -> m c') -> t c b a -> m (t c' b a)
mmmapM f = return . unflip2 <=< mapM f . Flip2

mmmmapM :: (Traversable (Flip3 t a b c), Monad m) => (d -> m d') -> t d c b a -> m (t d' c b a)
mmmmapM f = return . unflip3 <=< mapM f . Flip3

mmmmmapM :: (Traversable (Flip4 t a b c d), Monad m) => (e -> m e') -> t e d c b a -> m (t e' d c b a)
mmmmmapM f = return . unflip4 <=< mapM f . Flip4

ttraverse :: (Traversable (Flip f b), Applicative m) => (a -> m a') -> f a b -> m (f a' b)
ttraverse f = fmap unflip . traverse f . Flip

tttraverse :: (Traversable (Flip2 f c b), Applicative m) => (a -> m a') -> f a b c -> m (f a' b c)
tttraverse f = fmap unflip2 . traverse f . Flip2

ttttraverse :: (Traversable (Flip3 f d c b), Applicative m) => (a -> m a') -> f a b c d -> m (f a' b c d)
ttttraverse f = fmap unflip3 . traverse f . Flip3

tttttraverse :: (Traversable (Flip4 f e d c b), Applicative m) => (a -> m a') -> f a b c d e -> m (f a' b c d e)
tttttraverse f = fmap unflip4 . traverse f . Flip4

ffoldMap :: (Foldable (Flip f b), Monoid m) => (a -> m) -> f a b -> m
ffoldMap    f = foldMap f . Flip
fffoldMap   f = foldMap f . Flip2
ffffoldMap  f = foldMap f . Flip3
fffffoldMap f = foldMap f . Flip4

instance Functor (Flip Either b) where
  fmap f (Flip (Left  a)) = Flip $ Left  (f a)
  fmap f (Flip (Right b)) = Flip $ Right b


-- bifunctors

newtype Rotate3 f (a :: a') (b :: b') (c :: c') (d :: d') = Rotate3 { unrotate3 :: f d a b c }

instance Bifunctor (Rotate3 (,,,) b c) where
  bimap f g (Rotate3 (a,b,c,d)) = Rotate3 (g a, b, c, f d)
instance Bifoldable (Rotate3 (,,,) b c) where
  bifoldMap f g (Rotate3 (a,b,c,d)) = g a <> f d
instance Bitraversable (Rotate3 (,,,) b c) where
  bitraverse f g (Rotate3 (a,b,c,d)) = Rotate3 <$> ((,,,) <$> g a <*> pure b <*> pure c <*> f d)

class Tritraversable t where
  tritraverse :: Applicative f
              => (a -> f a')
              -> (b -> f b')
              -> (c -> f c')
              -> t a b c
              -> f (t a' b' c')

class Quadritraversable t where
  quadritraverse :: Applicative f
                 => (a -> f a')
                 -> (b -> f b')
                 -> (c -> f c')
                 -> (d -> f d')
                 -> t a b c d
                 -> f (t a' b' c' d')

class Pentatraversable t where
  pentatraverse :: Applicative f
                => (a -> f a')
                -> (b -> f b')
                -> (c -> f c')
                -> (d -> f d')
                -> (e -> f e')
                -> t a b c d e
                -> f (t a' b' c' d' e')

--
-- name conversion

cap :: String -> String -> String
cap pre [] = error "cap"
cap pre s@(h:t) = if not (isAlpha h) then pre ++ s
                    else toUpper h : t

decap :: String -> String
decap [] = error "decap"
decap (h:t) = toLower h : t

toIsaThyName :: String -> String
toIsaThyName = cap "Isa" . dehyphens

toHsModName  = cap "Hs" . dehyphens
toHsTypeName = cap "Hs" . dehyphens
toHsTermName = dehyphens

toCName :: String -> String
toCName = concatMap (\c -> if c == '\'' then "_prime" else [c])

dehyphens :: String -> String
dehyphens = map (\c -> if c == '-' then '_' else c)

tupleFieldNames = map (('p':) . show) [1 :: Integer ..]

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

(==>) :: Bool -> Bool -> Bool
(==>) = (<=)
infixr 2 ==>

type Warning = String

firstM :: Functor f => (a -> f c) -> (a, b) -> f (c, b)
firstM f (x,y) = (,y) <$> f x

secondM :: Functor f => (b -> f c) -> (a, b) -> f (a, c)
secondM f (x,y) = (x,) <$> f y

third3M :: Functor f => (c -> f d) -> (a, b, c) -> f (a, b, d)
third3M f (x,y,z) = (x,y,) <$> f z

fourth4M :: Functor f => (d -> f e) -> (a, b, c, d) -> f (a, b, c, e)
fourth4M f (x,y,z,w) = (x,y,z,) <$> f w

fst3 :: (a,b,c) -> a
fst3 (a,b,c) = a

snd3 :: (a,b,c) -> b
snd3 (a,b,c) = b

thd3 :: (a,b,c) -> c
thd3 (a,b,c) = c

fst4 :: (a,b,c,d) -> a
fst4 (a,b,c,d) = a

for :: [a] -> (a -> b) -> [b]
for = flip map


infixr 3 ***^^
(***^^) :: Applicative f => (a -> f a') -> (b -> f b') -> (a, b) -> f (a', b')
(***^^) fa fb (x,y) = (,) <$> fa x <*> fb y

both :: (a -> b) -> (a, a) -> (b, b)
both = (Lens.Micro.both %~)

bothM :: Applicative f => (a -> f a') -> (a, a) -> f (a', a')
bothM f = bitraverse f f

first3 :: (a -> a') -> (a, b, c) -> (a', b, c)
first3 = (_1 %~)

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

-- borrowed from the definitive-base package <http://hackage.haskell.org/package/definitive-base-2.3>
(<*=) :: Monad m => m a -> (a -> m b) -> m a
a <*= f = a >>= ((>>) <$> f <*> return)

-- largely borrowed from https://stackoverflow.com/questions/12119420/haskell-ghci-using-eof-character-on-stdin-with-getcontents
-- NOTE: this is slightly different---it stops after taking the pivoting element
-- @takeWhileM' c1 c2 ls@: the first condition is the terminating condition for the first line
--                         the second condition is the continuing condition for all lines
takeWhileM' :: Monad m => (a -> Bool) -> (a -> Bool) -> [m a] -> m [a]
takeWhileM' _ _ [] = return []
takeWhileM' c1 c2 (ma : mas) = do
  a <- ma
  if | c1 a -> return [a]
     | c2 a -> liftM (a :) $ takeWhileM' (const False) c2 mas
     | otherwise -> return [a]


fmapFold :: (Monoid m, Traversable t) => (a -> (m, b)) -> t a -> (m, t b)
fmapFold f = foldMap (fst . f) &&& fmap (snd . f)

-- NOTE: We need to first apply 'f' so that we are sure 'f' is only executed once;
-- If we follow the style of the above 'fmapFold' function, which has 'f' twice,
-- in this monadic function the computation will happen twice, which is undesirable. / zilinc
fmapFoldM :: (Monoid m, Traversable t, Monad f) => (a -> f (m, b)) -> t a -> f (m, t b)
fmapFoldM f x = do t <- traverse f x
                   return (foldMap fst t, snd <$> t)

foldMapM :: (Monoid m, Foldable t, Monad f) => (a -> f m) -> t a -> f m
foldMapM f x = foldrM f' mempty x
  where f' a b = mappend <$> f a <*> return b

mapAccumLM :: (Monad m) => (a -> b -> m (a,c)) -> a -> [b] -> m (a, [c])
mapAccumLM f a (x:xs) = do
    (a',c) <- f a x
    fmap (c:) <$> mapAccumLM f a' xs
mapAccumLM f a [] = pure (a, [])

-- adapted from <http://hackage.haskell.org/package/hydrogen-0.3.0.0/docs/src/H-Util.html#unionWithM>
unionWithKeyM :: (Ord k, Monad m) => (k -> a -> a -> m a) -> M.Map k a -> M.Map k a -> m (M.Map k a)
unionWithKeyM f m1 m2 =
  liftM M.fromList
    . sequence
    . fmap (\(k, v) -> liftM (k,) v)
    . M.toList
    $ M.unionWithKey f' (M.map return m1) (M.map return m2)
  where
    f' k mx my = mx >>= \x -> my >>= \y -> f k x y

--
-- useful monad things
--

-- Copied from https://hackage.haskell.org/package/errors-2.3.0/docs/src/Control.Error.Util.html
-- | Lift a 'Maybe' to the 'MaybeT' monad
hoistMaybe :: (Monad m) => Maybe b -> MaybeT m b
hoistMaybe = MaybeT . return


type WriterMaybe e a = MaybeT (Writer e) a

tellEmpty :: Monoid e => e -> WriterMaybe e a
tellEmpty e = lift (tell e) >> empty

mapTells :: forall e1 e2 a. (Monoid e1, Monoid e2) =>
  (e1 -> e2) ->
  WriterMaybe e1 a ->
  WriterMaybe e2 a
mapTells f = mapMaybeT (mapWriter (second f))

-- stdoutPath = "/dev/stdout"
-- nullPath = "/dev/null"

-- | Used for adding terminators to each line.
delimiter :: String -> String -> String
delimiter d = unlines . go d . lines
  where go d [] = []
        go _ [x] = [x]
        go d (x:xs) = (x++d) : go d xs


data Stage = STGParse | STGTypeCheck | STGDesugar | STGNormal | STGSimplify | STGMono | STGCodeGen
           deriving (Enum, Eq, Ord, Show)

type NameMod = String -> String


-- getCogentVersion - returns the version of Cogent
getCogentVersion = "Cogent development version: " ++ showVersion version ++ suffix ++
                   "\n" ++ "(" ++ configFlags ++ ")"
  where
    suffix = if gitHash == "" then "" else "-" ++ gitHash

-- getCogentVersionWithoutGit - return version of Cogent with git hash
getCogentVersionWithoutGit = "Cogent version: " ++ showVersion version

-- getStdGumDir
getHdrsDir :: IO FilePath
getHdrsDir = do dir <- getDataDir
                return (dir ++ "/" ++ "lib")

overrideLibgumDirWith :: String -> IO FilePath
overrideLibgumDirWith envVar = do envValue <- lookupEnv envVar
                                  maybe getHdrsDir return envValue

getLibgumDir :: IO String
getLibgumDir = addTrailingPathSeparator <$> overrideLibgumDirWith "COGENT_LIBGUM_DIR"

getStdIncFullPath fp = do sdir <- getLibgumDir
                          return (sdir </> fp)

-- reads a file, ignoring all lines starting with "--" and blank lines, eliminate spaces
simpleLineParser :: FilePath -> IO [String]
simpleLineParser = (return . filter (not . L.isPrefixOf "--") . filter (not . null) . map (dropWhile isSpace) . lines) <=< readFile


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


data Bound = GLB | LUB deriving (Eq, Ord)

instance Show Bound where
  show GLB = "lower bound"
  show LUB = "upper bound"

theOtherB GLB = LUB
theOtherB LUB = GLB


-- the following are taken from MissingH, BSD3 clause
-- http://hackage.haskell.org/package/MissingH-1.4.1.0
spanList :: ([a] -> Bool) -> [a] -> ([a], [a])
spanList _ [] = ([],[])
spanList func list@(x:xs) =
    if func list
       then (x:ys,zs)
       else ([],list)
    where (ys,zs) = spanList func xs

breakList :: ([a] -> Bool) -> [a] -> ([a], [a])
breakList func = spanList (not . func)

split :: Eq a => [a] -> [a] -> [[a]]
split _ [] = []
split delim str =
    let (firstline, remainder) = breakList (L.isPrefixOf delim) str
     in firstline : case remainder of
          [] -> []
          x -> if x == delim
                 then [] : []
                 else split delim (drop (length delim) x)

replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace old new l = L.intercalate new . split old $ l

elemBy :: Foldable t => (a -> a -> Bool) -> a -> t a -> Bool
elemBy f a as = go f a (toList as)
  where go f a [] = False
        go f a (b:bs) = if f a b then True else go f a bs

notElemBy :: Foldable t => (a -> a -> Bool) -> a -> t a -> Bool
notElemBy = ((not .) .) . elemBy

-- | A '\\-by' function
(\\-) :: (a -> a -> Bool) -> [a] -> [a] -> [a]
(\\-) f = foldl (flip (L.deleteBy f))

-- the following are from the extra library, BSD3
-- http://hackage.haskell.org/package/extra-1.6.13/docs/Control-Monad-Extra.html
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM op = foldr f (return [])
    where f x xs = do x <- op x; if null x then xs else do xs <- xs; return $ x++xs

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM p [] = return True
allM p (x:xs) = do v <- p x; if v then allM p xs else return False

andM :: Monad m => [m Bool] -> m Bool
andM = allM id

ifThenElse :: Bool -> t -> t -> t
ifThenElse c e1 e2 = if c then e1 else e2

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t f = do b <- b; if b then t else f

-- from the errors library, BSD3
-- http://hackage.haskell.org/package/errors-2.3.0
exceptT :: Monad m => (a -> m c) -> (b -> m c) -> ExceptT a m b -> m c
exceptT f g (ExceptT m) = m >>= \z -> case z of
    Left  a -> f a
    Right b -> g b

-- from composition, BSD3
-- https://hackage.haskell.org/package/composition-1.0.2.1
infixr 8 .*
infixr 8 .**

(.*) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(cd .* abc) a b = cd (abc a b)

(.**) :: (d -> e) -> (a -> b -> c -> d) -> a -> b -> c -> e
(de .** abcd) a b c = de (abcd a b c)

-- Drop the 0-indexed entry and shift everything down by 1.
behead :: IntMap a -> IntMap a
behead = IM.mapKeys ((-) 1) . IM.delete 1

infixl 9 .>
(.>) :: (a -> b) -> (b -> c) -> (a -> c)
(.>) = flip (.)

class Located a where
  getLoc :: a -> SourcePos

class Coercible a b where
  toA :: b -> a
  toB :: a -> b

-- type VarName = String
instance Coercible (a, Maybe a) a where
  toA varName = (varName, Nothing)
  toB = fst