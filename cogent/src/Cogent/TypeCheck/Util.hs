{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{- LANGUAGE TypeFamilies #-}

module Cogent.TypeCheck.Util where

import Cogent.Compiler
-- import Cogent.TypeCheck.Base
import Cogent.PrettyPrint

import Control.Monad.Except
-- import Control.Monad.IO.Class
-- import Control.Monad.State.Class
import Control.Monad.Writer
-- import Data.Function ((&))
-- import System.IO
import Text.PrettyPrint.ANSI.Leijen as L hiding (indent)

traceTC :: MonadIO m => String -> Doc -> m ()
traceTC s | Just ws <- __cogent_ddump_tc_filter, s `notElem` ws = const $ return ()
          | otherwise = liftIO . dumpMsg . (\d -> indent (text ("[dump-tc/" ++ s ++ "]") <+> d) L.<$> line)

traceTC' :: MonadIO m => String -> String -> m ()
traceTC' s = traceTC s . text

-- NOTE: The `ExceptT` on `WriterT` monad stack works in a way which,
-- if an error has been thrown, then later operations like `tell` or
-- `censor` will not fire. Although that is the right definition for
-- Monad, it doesn't serve our purposes here. Thus this `censor` function,
-- which sort of work around the problem. Still, it doesn't change the
-- way `>>=` works in general. As a consequence, if an error has been
-- thrown, it still doesn't contiune logging more errors. / zilinc
censor :: (Monad m) => (w -> w) -> ExceptT e (WriterT w m) a -> ExceptT e (WriterT w m) a
censor f m = ExceptT . WriterT $ do (a, w) <- runWriterT $ runExceptT m; return (a, f w)


