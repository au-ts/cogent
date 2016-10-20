{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{- LANGUAGE TypeFamilies #-}

module COGENT.TypeCheck.Util where

import COGENT.Compiler
-- import COGENT.TypeCheck.Base
import COGENT.PrettyPrint

import Control.Monad.IO.Class
-- import Control.Monad.State.Class
import System.IO
import Text.PrettyPrint.ANSI.Leijen as L hiding (indent)

-- FIXME: use flags to determine where to dump / zilinc
dumpMsg :: MonadIO m => Handle -> SimpleDoc -> m ()
dumpMsg a b | __cogent_ddump_tc = __fixme . liftIO $ displayIO a b
            | otherwise = return ()

traceTC :: MonadIO m => String -> Doc -> m ()
traceTC s = dumpMsg stdout . renderPretty 1.0 80 . (\d -> indent (text ("[dump-tc/" ++ s ++ "]") <+> d) L.<$> line)

traceTC' :: MonadIO m => String -> String -> m ()
traceTC' s = traceTC s . text
