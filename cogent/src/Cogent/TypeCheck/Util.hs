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

traceTc :: MonadIO m => String -> Doc -> m ()
traceTc s d = traceTcBracket s d (return ()) (const empty)

traceTc' :: MonadIO m => String -> String -> m ()
traceTc' s = traceTc s . text

traceTcBracket :: MonadIO m => String -> Doc -> m a -> (a -> Doc) -> m a
traceTcBracket s d1 m f
  | Just ws <- __cogent_ddump_tc_filter, s `notElem` ws = m
  | otherwise = do
      liftIO . dumpMsg $ indent (text ("[dump-tc/" ++ s ++ "]") <+> d1)
      a <- m
      d2 <- return $ f a
      liftIO . dumpMsg $ indent d2 L.<$> line
      return a


-- NOTE: The `ExceptT` on `WriterT` monad stack works in a way which,
-- if an error has been thrown, then later operations like `tell` or
-- `censor` will not fire. Although that is the right definition for
-- Monad, it doesn't serve our purposes here. We need `censor' to add
-- error contexts to existing errors in the writer, which happens after
-- some errors have been throw. We define this `censor` function,
-- which sort of works around the problem. Still, it doesn't change the
-- way `>>=` works in general. As a consequence, if an error has been
-- thrown, it still doesn't contiune logging more errors. But this
-- `censor' function updates the log. / zilinc
censor :: (Monad m) => (w -> w) -> ExceptT e (WriterT w m) a -> ExceptT e (WriterT w m) a
censor f m = ExceptT . WriterT $ do (a, w) <- runWriterT $ runExceptT m; return (a, f w)


