{-# LANGUAGE DataKinds #-}
module CogentTests.Core (genLayoutableType) where
import Cogent.Core
import Test.QuickCheck
import Cogent.Vec (Nat(..))
import Cogent.Common.Syntax (FieldName, TagName, RepName, Size)
import Cogent.Common.Types (Sigil (..), PrimInt (..))
import Cogent.Compiler (__fixme)

genLayoutableType :: Int -> Gen (Type 'Zero)
genLayoutableType size = 
	oneof
	[ TCon     <$> arbitrary <*> pure [] <*> (Boxed <$> arbitrary <*> pure ())
	, TPrim    <$> arbitrary
	, TSum     <$> resize size (listOf (genLayoutableAlternative size))
	, TRecord  <$> resize size (listOf (genLayoutableField size)) <*> pure (__fixme Unboxed)
		-- ^ If size == 0, no recursive call will happen as it generates an empty list
		-- ^ FIXME: Need to sometimes generate Boxed TProducts with DataLayout coming from Cogent.Desugar (constructLayout) /mdimgelio
	, pure TUnit
	]
	where
		genLayoutableAlternative :: Int -> Gen (TagName, (Type 'Zero, Bool))
		genLayoutableAlternative size = do
			altSize <- choose (0, size - 1)
			(,) <$> arbitrary <*> ((,) <$> genLayoutableType altSize <*> arbitrary)

		genLayoutableField :: Int -> Gen (FieldName, (Type 'Zero, Bool))
		genLayoutableField size = do
			fieldSize <- choose (0, size - 1)
			(,) <$> arbitrary <*> ((,) <$> genLayoutableType fieldSize <*> arbitrary)

instance Arbitrary PrimInt where
	arbitrary = elements [U8, U16, U32, U64, Boolean]
