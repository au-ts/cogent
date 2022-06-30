{-# LANGUAGE DerivingStrategies, GeneralizedNewtypeDeriving, TemplateHaskell #-}

module CogentPrims where

import Data.Bits
import Data.Word
import CogentPrimsQ

$(genWordTypes 1  7 ) 
$(genWordTypes 9  15)
$(genWordTypes 17 31)
$(genWordTypes 33 63)
