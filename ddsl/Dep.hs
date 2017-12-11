{-# LANGUAGE PatternGuards #-}

module Dep (Dep.parse, Dep.check) where

import Control.Monad.State
-- import Control.Monad.IO.Class (liftIO)
import qualified Data.Graph.Wrapper as W
import Data.List as L 
import Data.Map as M hiding (null)
import System.IO
import System.Directory
import System.FilePath

-- import DSyntax as S
import Parse   as DP
import Prep    as DPP
import Check   as DC 
import Util
import Pretty

-- State transformer

type Processed = Bool
-- Imports :: only file name -> (path relative to compiler, is processed?)
type Imports = Map ModName (FilePath, Processed)
type DStateT = StateT Imports IO

getDStateT :: DStateT Imports
getDStateT = gets id

putDStateT :: Imports -> DStateT ()
putDStateT s = modify (const s)

-- Returns false if same mod is already in state
addDStateT :: FilePath -> DStateT Bool
addDStateT p = do
  s <- getDStateT
  let f = takeFileName p
  case M.lookup (ModName f) s of
    Just (p', _) -> do
      pc  <- liftIO $ canonicalizePath p
      pc' <- liftIO $ canonicalizePath p'
      if equalFilePath pc pc'
        then return False
        else do liftIO $ putStrLn $ "File name `" ++ p ++ "' same as `" ++ p' ++ "'. Ignore the former one."
                return False
    Nothing -> do 
      putDStateT $ M.insert (ModName f) (p, False) s
      return True

-- ASSERTION: The input ModName is already in the state
procDStateT :: ModName -> DStateT ()
procDStateT f = do
  s <- getDStateT
  case M.lookup f s of
    Just _  -> putDStateT $ M.adjust (\(p, _) -> (p, True)) f s
    Nothing -> error $ progErr "procDStateT"

findUnproc :: DStateT (Maybe FilePath)
findUnproc = do
  s <- getDStateT
  case L.find (not . snd . snd) (toList s) of
    Nothing -> return Nothing
    Just f  -> return $ Just $ fst $ snd f

findMod :: ModName -> DStateT Bool
findMod f = getDStateT >>= return . M.member f

-------------------------------------------------------------------------------
-- parse

parse :: FilePath -> IO (Either ParseError [Module])
parse p0 = do
  liftIO $ DPP.prep p0  -- IMPORTANT: Flags are all global and must appear in the entry file
  evalStateT (parse1 p0 []) M.empty

-- parse1 :: modName relative to compiler 
--        -> parsed modules 
--        -> ret
parse1 :: FilePath -> [Module] -> DStateT (Either ParseError [Module])
parse1 p0 ms = do
  let f0 = takeFileName p0  -- only filename
  s0 <- liftIO $ readFile p0
  addDStateT p0
  case DP.parse f0 s0 of
    Left  err -> return $ Left err
    Right m@(Module n (ModHead imps) _) -> do  -- n == f0
      procDStateT $ ModName f0
      addImports $ ModHead $ L.map (\(ModName n) -> ModName $ (dropFileName p0) </> n) imps
      findUnproc >>= \u -> case u of
        Nothing -> return $ Right (m:ms)
        Just p  -> parse1 p (m:ms)

addImports :: ModHead -> DStateT ()
addImports (ModHead []) = return ()
addImports (ModHead (ModName p : imps)) = do
  addDStateT p
  addImports (ModHead imps)

-------------------------------------------------------------------------------
-- check

check :: [Module] -> Either String (Either [Err] (Def, Delta, Pi))
check ms = sortMods ms >>= Right . DC.check

-- Precondition: all imported files exist
-- Postcondition: each module only depends on prior ones or itself
sortMods :: [Module] -> Either String [Module]
sortMods ms = 
  let l = L.map mkVertex ms
      g = W.transpose $ W.fromList l 
      sccs = W.stronglyConnectedComponents g
  in case checkCycle sccs of
       Nothing -> Right $ L.map (W.vertex g) (W.topologicalSort g)
       Just is -> Left  $ "Cyclic imports: " ++ pShow is  -- FIXME: better error message
  where mkVertex m@(Module n (ModHead imps) _) = 
          (n, m, L.map (\(ModName n) -> ModName $ takeFileName n) imps)
        checkCycle :: [W.SCC i] -> Maybe [i]
        checkCycle [] = Nothing
        checkCycle (W.AcyclicSCC _ : ss) = checkCycle ss
        checkCycle (W.CyclicSCC is : ss) = Just is 
 
