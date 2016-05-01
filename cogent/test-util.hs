--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

import COGENT.Util
import Prelude hiding (fail)
import System.Directory
import System.Exit
import System.FilePath
import System.IO

main = tests

tests = sequence [test1, test2, test3, test4, test5, test6,  -- tests listed in #91
                  test7, test8, test9,
                  test10]

test1 = do let s = "../.."
               d = "a/b/c"
               c = "../../../../.."
           p <- getCurrentDirectory
           let r = relDir s d p
           check r c "1"

test2 = do let s = "a/b/c/"
               d = "d/e/f"
               c = "../../../a/b/c"
           p <- getCurrentDirectory
           let r = relDir s d p
           check r c "2"

test3 = do let s = "../../"
               d = "../../"
               c = "."
           p <- getCurrentDirectory
           let r = relDir s d p
           check r c "3"

test4 = do let s = "../../.."
               d = "../../"
               c = ".."
           p <- getCurrentDirectory
           let r = relDir s d p
           check r c "4"

test5 = do let s = "../../"
               d = "../../../"
           p <- getCurrentDirectory
           let c = last $ splitDirectories p
               r = relDir s d p
           check r c "5"

test6 = do let s = "a/b/c"
               d = "../.."
           p <- getCurrentDirectory
           let ls = splitDirectories p
               c = joinPath (drop (length ls - 2) ls) </> "a/b/c"
               r = relDir s d p
           check r c "6"

-- both absolute
test7 = do let s = "/a/b/c/d/"
               d = "/a/b/c/e"
               c = "/a/b/c/d"
           p <- getCurrentDirectory
           let r = relDir s d p
           check r c "7"

-- s is absolute, d relative
test8 = do let s = "/a/b/c/d/"
               d = "../b/e/f"
               c = "/a/b/c/d"
           p <- getCurrentDirectory
           let r = relDir s d p
           check r c "8"

-- s is relative, d absolute
test9 = do let s = "a/b/c/d/"
               d = "/usr/local/bin"
           p <- getCurrentDirectory
           let c = p </> "a/b/c/d"
               r = relDir s d p
           check r c "9"

-- failed in regression test on 28/10/2015
test10 = do let s = "../../"
                d = "./build"
            p <- getCurrentDirectory
            let c = "../../.."
                r = relDir s d p
            check r c "10"

check :: (Eq a, Show a) => a -> a -> String -> IO ()
check r c m = if r == c then pass ("test" ++ m) else fail ("test" ++ m ++ " (r = " ++ show r ++ " )") 

pass m = hPutStrLn stderr ("Passed! " ++ m)
fail m = hPutStrLn stderr ("Failed! " ++ m) >> exitFailure
