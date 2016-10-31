{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{- LANGUAGE TypeFamilies #-}

module COGENT.TypeCheck.Util where

import COGENT.Compiler
-- import COGENT.TypeCheck.Base
import COGENT.PrettyPrint

import Control.Monad.IO.Class
-- import Control.Monad.State.Class
-- import Data.Function ((&))
-- import System.IO
import Text.PrettyPrint.ANSI.Leijen as L hiding (indent)

traceTC :: MonadIO m => String -> Doc -> m ()
traceTC s = liftIO . dumpMsg . (\d -> indent (text ("[dump-tc/" ++ s ++ "]") <+> d) L.<$> line)

traceTC' :: MonadIO m => String -> String -> m ()
traceTC' s = traceTC s . text
