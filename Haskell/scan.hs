{- |
Module      :  $Id$
Description :  a standalone Haskell scanner
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

test the haskell scanner
-}

import Control.Monad

import Data.Char
import Data.List

import System.Environment

import Haskell.Scanner
import Text.ParserCombinators.Parsec

main :: IO ()
main = do
  args <- getArgs
  let (opts, files) = span (isPrefixOf "-") args
  mapM_ (process $ null opts) files

process :: Bool -> String -> IO ()
process b f = do
  str <- readFile f
  let nls = zip [1 ..] $ lines str
      bls = checkBlankLines f 1 nls
  when b $ mapM_ (checkLine f) nls
  when (b && not (isSuffixOf "\n" str))
    $ diag f (length nls) "missing final newline"
  when b $ mapM_ putStrLn bls
  case parse scan f str of
    Right ts -> let x = splitLines ts in
      if b then let o = showScan x in unless (null o) $ putStrLn o else
      writeFile f $ processScan x
    Left err -> fail $ show err

checkBlankLines :: FilePath -> Int -> [(Int, String)] -> [String]
checkBlankLines f c l = case l of
  [] -> []
  (n, s) : r ->
    if null $ filter (not . isSpace) s then
      if c >= 2 then
        diagStr f n "too many consecutive blank lines"
        : checkBlankLines f (- 100) r
      else checkBlankLines f (c + 1) r
    else checkBlankLines f 0 r

diagStr :: FilePath -> Int -> String -> String
diagStr f n str = "\"" ++ f ++ "\" (line " ++  show n ++ ") " ++ str

diag :: FilePath -> Int -> String -> IO ()
diag f n = putStrLn . diagStr f n

checkLine :: FilePath -> (Int, String) -> IO ()
checkLine f (n, s) = do
  let r = reverse s
      rt = dropWhile isSpace r
      l = length rt
      trailBSlash = takeWhile (== '\\') rt
      badChars = filter (\ c -> not $ isAscii c && isPrint c) s
  when (l > 80) $
    diag f n $ "too long line (" ++ show l ++ " chars)"
  unless (null badChars) $
    diag f n $ "contains undesirable characters: " ++ show badChars
  unless (null trailBSlash) $
    diag f n $ "back slash at line end (may disturb cpp)"
