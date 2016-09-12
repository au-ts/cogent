--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Cogent.Hangman where

#if __GLASGOW_HASKELL__ <709
import Control.Applicative ((<$>))
#endif
import Control.Concurrent
-- import Control.Lens ((&))
import Control.Monad (unless, zipWithM_)
import Data.Char
import Data.List (intersperse)
-- import Data.Time.Clock
import System.IO
import System.Random
import UI.HSCurses.Curses

onesec = 1000000

-- main = do
hangman :: IO ()
hangman = do
  win <- initScr
  (h,w) <- scrSize
  if w < 60 || h < 20
    then endWin >> hPutStrLn stderr "Terminal has to be larger than 60*15"
    else do cBreak True
            echo True
            _ <- cursSet CursorVisible
            -- hmw <- newWin 11 w 0 0
            -- cogentw <- newWin (h - 11) w 11 0
            keypad win False
            -- drawBg (hmw,cogentw)
            drawHmBg win
            threadDelay (onesec `div` 2)
            noRound <- runGame 1 win
            -- drawBg (hmw,cogentw)
            drawHmBg win
            mvWAddStr win 3 1 "Bye and enjoy Cogent!"
            wRefresh win
            threadDelay onesec
            endWin
            -- update

-- drawBg :: (Window, Window) -> IO ()
-- drawBg (hmw, cogentw) = drawHmBg hmw >> drawCogentBg cogentw

drawHmBg :: Window -> IO ()
drawHmBg win = do
  werase win
  let border = Border '|' '|' '-' '-' '+' '+' '+' '+'
  wBorder win border
  mvWAddStr win 1 1 "Welcome to Hangman! (made by zilinc)"
  (_, col) <- scrSize
  mvWAddStr win 1 (col - 20) "Press ESC to quit"
  wRefresh win

drawCogentBg :: Window -> IO ()
drawCogentBg win = do
  werase win
  let border = Border '|' '|' '-' '-' '+' '+' '+' '+'
  wBorder win border

runGame :: Int -> Window -> IO Int
runGame round win = do
  word <- getAWord
  draw win (Playing initLives) (mkDisp word []) NoInput []
  engine win word []
  mvWAddStr win (9 + length graphic) 1 "Try again? (Y/n)"
  (y,x) <- getYX win
  move y (x + 1)
  wRefresh win
  getCh >>= \case
    KeyChar 'n' -> return round
    _ -> runGame (round + 1) win

-- each round takes a char and proceed to the next round, unless initially it's Win status
engine :: Window -> String -> [Char] -> IO ()
engine win ans guess = getCh >>= \case
  KeyChar ch | ord ch == 27 -> return ()  -- ESC
  KeyChar ch -> do
    let input = if isEngLower ch
                  then if ch `elem` guess then Duplicate else Valid ch
                  else Invalid
        guess' = case input of
                   Valid ch -> ch:guess
                   _ -> guess
        misses = filter (`notElem` ans) $ reverse guess'
        lives = initLives - length misses
        st = if | all (`elem` guess') ans -> Win
                | length misses >= initLives -> Lose ans
                | otherwise -> Playing lives
    draw win st (mkDisp ans guess') input misses
    threadDelay (onesec `div` 2)
    draw win st (mkDisp ans guess') NoInput misses
    unless (endEngine st) $ engine win ans guess'
  _ -> engine win ans guess

mkDisp :: String -> [Char] -> String
mkDisp ans guess = intersperse ' ' $ map (\c -> if c `elem` guess then c else '_') ans

data Status = Win | Playing Int | Lose String deriving (Eq)

endEngine :: Status -> Bool
endEngine (Playing _) = False
endEngine _ = True

data Input = Valid Char | Invalid | Duplicate | NoInput deriving (Eq)

initLives = 7

draw :: Window -> Status -> [Char] -> Input -> [Char] -> IO ()
draw win st disp input misses = do
  drawHmBg win
  -- draw the window
  mvWAddStr win 3 3 $ "Word: " ++ disp
  mvWAddStr win 4 3 $ "Guess: " ++ (case input of Valid c -> [c]
                                                  Invalid -> "Invalid input!"
                                                  Duplicate -> "Duplicate input!"
                                                  NoInput -> "")
  mvWAddStr win 5 3 $ "Misses: " ++ intersperse ',' misses
  let status = case st of Win -> "YOU WIN :)"
                          --Playing lives -> "Lives: " ++ replicate lives '$'  -- '♥'
                          Playing lives -> makeGraphic lives
                          Lose ans -> makeGraphic 0 ++ "\nYOU LOSE :( Answer is: " ++ ans
  zipWithM_ (\i -> mvWAddStr win (7+i) 3) [0..] $ lines status
  move 4 10
  wRefresh win

graphic =
  [ "/==----+"
  , "||     |"
  , "||     o"
  , "||     -"
  , "||    /|\\"
  , "||     ^"
  , "||    / \\"
  , "||  -------"
  , "||  $$$$$$$"
  , "============="
  ]

gameover =
  [ "/==----+"
  , "||     |"
  , "||     X"
  , "||    <->"
  , "||     |"
  , "||     ^"
  , "||    / \\"
  , "||"
  , "||  -------"
  , "============="
  ]

makeGraphic 0 = unlines gameover
makeGraphic lives = subst ls s
  where s = unlines graphic
        maxlives = length $ filter (=='$') s
        ls = replicate ((maxlives - lives) `div` 2) ' ' ++ replicate lives '|' ++ replicate ((maxlives - lives + 1) `div` 2) ' '
        subst _ "" = ""
        subst [] s = s
        subst (c:cs) s = let (a, b) = break (=='$') s in a ++ [c] ++ subst cs (drop 1 b)

getAWord :: IO String
getAWord = do
  words <- lines <$> readFile "/usr/share/dict/words"
  -- UTCTime dat time <- getCurrentTime
  -- s <- fromEnum time
  -- let g = mkStdGen s
  g <- getStdGen
  no <- randomRIO (0, length words - 1)
  let word = words !! no
  if all isEngLower word && length word > 3  -- lowercase a-z are in [97, 122]
     then return word
     else getAWord

isEngLower :: Char -> Bool
isEngLower c = ord c >= 97 && ord c <= 122

