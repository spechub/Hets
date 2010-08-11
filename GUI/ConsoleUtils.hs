{- |
Module      :  $Header$
Description :  simple command line dialogs
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2005
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

gui utilities that work via the console instead of using HTk

   The interface should remain compatible with GUI.HTkUtils
   so that GUI.Utils can reexport functions of both modules
   based on the presence of UNI_PACKAGE.

-}

module GUI.ConsoleUtils where

import Data.Char
import Data.List
import Control.Monad ( unless )

-- | present a list of choices and return the selection
listBox :: String -> [String] -> IO (Maybe Int)
listBox prompt choices = do
   putStrLn prompt
   mapM_ putStrLn $ zipWith (\ n -> (shows n ": " ++)) [0::Int ..] choices
   putStrLn "Please enter a number on the next line"
   s <- getLine
   if all isDigit s then
          let n = foldl ( \ r a -> r * 10 + digitToInt a) 0 s in
              if n >= length choices then
                 putStrLn "number to large, try again"
                 >> listBox prompt choices
              else putStrLn ("you have chosen entry \"" ++ choices!!n)
                   >> return (Just n)
      else putStrLn ("illegal input \"" ++ s ++ "\" try again")
           >> listBox prompt choices

-- | show text and ask to save it
createTextSaveDisplay :: String -- ^ title of the window
                      -> String -- ^ default filename for saving the text
                      -> String -- ^ text to be displayed
                      -> IO()
createTextSaveDisplay t f txt = do
    putStrLn t
    putStrLn $ replicate (length t) '='
    putStrLn ""
    putStrLn txt
    putStrLn ""
    askFileNameAndSave f txt


-- | ask for a file name
askFileNameAndSave :: String -- ^ default filename for saving the text
                   -> String -- ^ text to be saved
                   -> IO ()
askFileNameAndSave f txt = do
    putStrLn $ "save text in file \"" ++ f ++ "\"? (y/n)"
    s <- getLine
    if "y" `isPrefixOf` map toLower s then writeFile f txt
      else do
      putStrLn "enter new file name (or abort with return):"
      n <- getLine
      unless (null n) $ askFileNameAndSave n txt
