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

{-# LANGUAGE DataKinds, PackageImports #-}
module CogentTests.Core (genLayoutableType) where
import Cogent.Core
import Test.QuickCheck
import "cogent" Data.Nat (Nat(..))
import Cogent.Common.Syntax (FieldName, TagName, RepName, Size)
import Cogent.Common.Types (Sigil (..), PrimInt (..), RecursiveParameter (..))
import Cogent.Compiler (__fixme)

genConName :: Gen TagName
genConName = (:) <$> elements ['A'..'Z'] <*> listOf (elements (['A'..'Z'] ++ ['a'..'z'] ++ ['0'..'9']))

genLayoutableType :: Int -> Gen (Type 'Zero b)
genLayoutableType size = 
  oneof
  [ TCon            <$> genConName <*> pure [] <*> (Boxed <$> arbitrary <*> pure ())
  , TPrim           <$> arbitrary
  , TSum            <$> resize size (listOf (genLayoutableAlternative size))
  , TRecord NonRec  <$> resize size (listOf (genLayoutableField size)) <*> pure (__fixme Unboxed)
    -- ^ If size == 0, no recursive call will happen as it generates an empty list
    -- ^ FIXME: Need to sometimes generate Boxed TProducts with DataLayout coming from Cogent.Desugar (constructLayout) /mdimgelio
    -- ^ FIXME: Needs to generate recursive types properly and generate recursive parameters only if inside a recursive record. /emmet-m
  , pure TUnit
  ]
  where
    genLayoutableAlternative :: Int -> Gen (TagName, (Type 'Zero b, Bool))
    genLayoutableAlternative size = do
      altSize <- choose (0, size - 1)
      (,) <$> arbitrary <*> ((,) <$> genLayoutableType altSize <*> arbitrary)

    genLayoutableField :: Int -> Gen (FieldName, (Type 'Zero b, Bool))
    genLayoutableField size = do
      fieldSize <- choose (0, size - 1)
      (,) <$> arbitrary <*> ((,) <$> genLayoutableType fieldSize <*> arbitrary)

instance Arbitrary PrimInt where
  arbitrary = elements $ Boolean : [UInt x | x <- [1..64]]
