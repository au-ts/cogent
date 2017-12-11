--
-- Copyright 2017, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--
import Prelude as P hiding (mapM_)
import Control.Applicative ((<$>))
import Control.Monad hiding (mapM_)
import Data.Foldable (mapM_)
import Data.IORef
import Data.List as L
import Data.Map as M
import Data.Maybe
import Data.Tuple.Select
import Data.Ord
import Text.Parsec.Pos (Line)
import Text.Parsec (SourceName)
import Text.Show.Pretty
import Text.Printf
import System.Directory
import System.Environment
import System.FilePath
import System.IO
import System.IO.Unsafe

import Syntax
import qualified Dep     as DD
import qualified Parse   as DP
import qualified Check   as DC
import qualified Rewrite as DR
import qualified CodeGen as DG
import Pretty
import Util

import COGENT.Syntax
import COGENT.PrettyPrint


main = hSetBuffering stdout NoBuffering >>
       getArgs >>= \a -> case a of
         [] -> putStrLn usage
         (a:[]) -> putStrLn usage
         (a:as) -> do
           writeIORef show_parse_ref         $ "--show-parse"         `elem` init as
           writeIORef show_check_ref         $ "--show-check"         `elem` init as
           writeIORef show_rewrite_ref       $ "--show-rewrite"       `elem` init as
           writeIORef show_rewrite_del_ref   $ "--show-rewrite-del"   `elem` init as
           writeIORef show_gen_ref           $ "--show-gen"           `elem` init as
           writeIORef allow_u24_ref          $ "--allow-u24"          `elem` init as
           writeIORef allow_empty_struct_ref $ "--allow-empty-struct" `elem` init as 
           writeIORef no_gen_file_ref        $ "--no-gen-file"        `elem` init as
           let (c1_f, c2_f, c3_f, c4_f) = case a of 
                 "-p" -> (True, False, False, False)
                 "-c" -> (True, True , False, False)
                 "-r" -> (True, True , True , False)
                 "-g" -> (True, True , True , True )
                 otherwise -> (False, False, False, False)
               c0 = last as
           if "-" `isPrefixOf` c0
             then putStrLn usage
             else do o <- case "-o" `L.elemIndex` init as of
                            Just idx | idx == length (init as) - 1 -> return False
                                     | otherwise -> do writeIORef output_ref $ as !! (idx + 1)
                                                       return True
                            Nothing -> do writeIORef output_ref $ replaceExtension c0 "cogent"
                                          return True
                     if o then if not c1_f
                                 then putStrLn usage
                                 else do 
                                   c1 <- parse c0
                                   flip mapM_ c1 $ \c1' -> 
                                     when c2_f $ do
                                       c2 <- check c1'
                                       flip mapM_ c2 $ \c2' ->
                                         when c3_f $ do
                                           c3 <- rewrite c1' (fst c2', snd c2') 
                                           when c4_f $ do
                                             gen (fst c3) (snd c3, snd c2')
                                             return ()
                          else putStrLn usage
  where usage = "Usage: ddsl -<pcrg> [OPTIONS] [-o FILENAME] FILENAME\n" ++
                "OPTIONS: --show-parse, --show-check, --show-rewrite, --show-rewrite-del, --show-gen" ++
                " --allow-u24, --allow-empty-struct, --no-gen-file"
        
parse :: FilePath -> IO (Maybe [Module])
parse c0 = do
  c0' <- DD.parse c0
  case c0' of
    Left err -> putStrLn (show err) >> return Nothing
    Right c1 -> do putStrLn ">> Parsing... ok."
                   when show_parse_internal $ (prettyMods c1)
                   return (Just c1)

{-
parse1 :: FilePath -> IO (Maybe Module)
parse1 file = do
  hdl <- openFile file ReadMode
  c0  <- hGetContents hdl
  DPP.prep c0
  let c0' = DP.parse file c0
  c1 <- case c0' of
          Left err  -> putStrLn (show err) >> return Nothing
          Right c1' -> do putStrLn ">> Parsing... ok."
                          when show_parse_internal $ (prettyMod c1')
                          return (Just c1')
  hClose hdl
  return c1
-}

check :: [Module] -> IO (Maybe (Delta, Pi))
check c1 = case DD.check c1 of
  Left err  -> do putStrLn $ ">> Checking... fail.\n" ++ err
                  return Nothing
  Right c1' -> case c1' of
    Left err -> prettyErr err >> return Nothing
    Right c2 -> do putStrLn ">> Checking... ok." 
                   when show_check_internal $ prettyCheck c2
                   return $ Just (sel2 c2, sel3 c2)

-- assert: c2 in any order, because cogent will toposort
rewrite :: [Module] -> (Delta, Pi) -> IO ([Module], Delta)
rewrite c2 (del, pii) = do
  putStrLn ">> AST rewriting... ok."
  when show_rewrite_internal $ prettyMods $ fst c3
  when show_rewrite_del_internal $ prettyDelta $ snd c3
  return c3
  where c3 = DR.rewrite c2 (del, pii)

-- assert: [DataDesc] in c3 in any order
gen :: [Module] -> (Delta, Pi) -> IO [Definition RawStmt RawExpr]
gen c3 envs = do 
  putStrLn ">> COGENT code generating... ok."
  when show_gen_internal $ prettyCogent c4
  when (not no_gen_file_internal) $ do
    let outok = do prettyCogent_ output_internal c4 
                   putStrLn $ ">> COGENT code writing to file `" ++ output_internal ++ "'... ok."
        outno = putStrLn ">> Writing to file... skip."
    doesFileExist output_internal >>= \e -> 
      if e then do putStr $ ">> File `" ++ output_internal ++ "' exists, overwrite?[y/N]"
                   input <- getLine
                   case input of
                     ""        -> outno
                     otherwise -> 
                       if head input `elem` "yY" 
                         then outok
                         else outno
           else outok
  return c4
  where c4 = DG.gen (concat $ L.map modDesc c3) envs

-- sortDs :: [(DataDesc, Level)] -> [DataDesc]
-- sortDs = L.map fst  -- FIXME: no sorting: cogent will sort!
{-
sortDs ds = L.map fst $ sortBy ordDef ds
  where ordDef :: (DataDesc, Level) -> (DataDesc, Level) -> Ordering
        ordDef (d1, l1) (d2, l2) = compare l1 l2
-}

