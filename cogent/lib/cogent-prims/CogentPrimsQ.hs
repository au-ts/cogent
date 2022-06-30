module CogentPrimsQ where

import Data.Word (Word8, Word16, Word32, Word64)
import Language.Haskell.TH

genWordTypes :: Int -> Int -> Q [Dec]
genWordTypes lo hi = mapM (flip mkWordDecl (hi + 1)) [lo..hi]
  where
    mkWordDecl sz rep =
      let tyName  = mkName $ "Word" ++ show sz
          repName = mkName $ "Word" ++ show rep
          fldName = mkName $ "uint" ++ show sz
          noBang  = Bang NoSourceUnpackedness NoSourceStrictness
          ctx     = [ ConT $ mkName "Eq"
                    , ConT $ mkName "Ord"
                    , ConT $ mkName "Show"
                    , ConT $ mkName "Real"
                    , ConT $ mkName "Enum"
                    , ConT $ mkName "Bits"
                    , ConT $ mkName "Num"
                    , ConT $ mkName "Integral"]
       in return $ NewtypeD [] tyName [] Nothing
                     (RecC tyName [(fldName, noBang, ConT repName)])
                     [DerivClause (Just NewtypeStrategy) ctx]

