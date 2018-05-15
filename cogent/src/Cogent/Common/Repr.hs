-- @LICENSE(NICTA_CORE)

{-# LANGUAGE CPP #-}

module Cogent.Common.Repr where

import qualified Cogent.Surface as S
import Cogent.Common.Syntax
import Text.Parsec.Pos
import qualified Data.Map as M

data RepData = Rep
               { originalDecl :: S.RepDecl
               , name :: RepName
               , representation :: Representation
               }
data Representation = Bits { allocSize :: Int, allocOffset :: Int} -- in bits 
                    | Variant { tagSize :: Int, tagOffset :: Int, alternatives :: M.Map TagName (Integer, Representation)  }
                    | Record { fields :: M.Map FieldName Representation}

type Allocation = [[Block]] -- disjunction of conjunctions
data Block = Block { blockSize :: Int, blockOffset :: Int, blockContext :: RepContext }
           deriving (Eq, Show, Ord)

data RepContext = InField FieldName SourcePos RepContext
                | InTag RepContext
                | InAlt TagName SourcePos RepContext
                | InDecl S.RepDecl
                deriving (Eq, Show, Ord)

data RepError = OverlappingBlocks Block Block
              | UnknownRepr RepName RepContext
              deriving (Eq, Show, Ord)

(\/) :: Allocation -> Allocation -> Either RepError Allocation 
a \/ b = Right (a ++ b)
(/\) :: Allocation -> Allocation -> Either RepError Allocation
(x:xs) /\ b = (++) <$> helper x b <*> (xs /\ b)
  where helper :: [Block] -> [[Block]] -> Either RepError Allocation
        helper bs (y:ys) = let os = [(b1,b2) | b1 <- bs, b2 <- y, overlaps b1 b2]
                            in case os of 
                                [] -> ((bs ++ y):) <$> helper bs ys 
                                (b1,b2):_ -> Left $ OverlappingBlocks b1 b2
        helper bs [] = Right []

        overlaps (Block s1 o1 _) (Block s2 o2 _) = o1 >= o2 && o1 < (o2 + s2)
                                                || o2 >= o1 && o2 < (o1 + s1)
[] /\ b = pure b



mapAccumLM :: (Monad m) => (a -> b -> m (a,c)) -> a -> [b] -> m (a, [c])
mapAccumLM f a (x:xs) = do 
    (a',c) <- f a x
    fmap (c:) <$> mapAccumLM f a' xs
mapAccumLM f a [] = pure (a, []) 

compile :: M.Map RepName (Allocation, RepData) -> S.RepDecl -> Either RepError (Allocation, RepData)
compile env d@(S.RepDecl p n a) = fmap (Rep d n) <$> evalAlloc (InDecl d) a
  where evalSize (S.Bytes b) = b * 8
        evalSize (S.Bits b) = b
        evalSize (S.Add a b) = evalSize a + evalSize b

        evalAlloc ctx (S.RepRef n) = do 
            case M.lookup n env of 
                Just (a,Rep _ _ r) -> Right (a,r)
                Nothing    -> Left $ UnknownRepr n ctx
        evalAlloc ctx (S.Prim s off) = Right ([[Block (evalSize s) (evalSize off) ctx]], Bits (evalSize s) (evalSize off))
        evalAlloc ctx (S.Record fs) = do
            let step alloc (f,pos,r) = do
                  (a, r') <- evalAlloc (InField f pos ctx) r 
                  a' <- a /\ alloc 
                  return (a', (f, r'))
            (a, fs') <- mapAccumLM step [[]] fs 
            pure (a, Record $ M.fromList fs')
        evalAlloc ctx (S.Variant (s,off) vs) = do
            let step alloc (f,pos,i,r) = do 
                  (a,r') <- evalAlloc (InAlt f pos ctx) r
                  a' <- a \/ alloc
                  return (a', (f,(i,r')))
            (a, vs') <- mapAccumLM step [] vs
            pure (a, Variant (evalSize s) (evalSize off) $ M.fromList vs')

