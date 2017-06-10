--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

-- FIXME: this module should be subsumed by Util or be deleted / zilinc
module Cogent.PrettyCore where

import System.Console.ANSI (hSetSGR)
import System.IO (Handle, hPutChar, hPutStr)
import Text.PrettyPrint.ANSI.Leijen hiding

-- FIXME: where is this code from? why do we need it? / zilinc
displayOneLine :: Handle -> SimpleDoc -> IO ()
displayOneLine handle simpleDoc = display simpleDoc >> hPutChar handle '\n'
  where
    display SFail         = error $ "@SFail@ can not appear uncaught in a " ++ "rendered @SimpleDoc@"
    display SEmpty         = return ()
    display (SChar c x)    = do{ hPutChar handle c; display x}
    display (SText l s x)  = do{ hPutStr handle s; display x}
    display (SLine i x)    = do{ hPutChar handle ' '; display x}
    display (SSGR s x)     = do{ hSetSGR handle s; display x}
