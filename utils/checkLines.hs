import System.Environment

import Data.Char
import Data.List

import Control.Monad

main :: IO ()
main = do
  fs <- getArgs
  case fs of
    [] -> getContents >>= processContent ""
    _ -> mapM_ processFile fs

processFile :: FilePath -> IO ()
processFile f =
  readFile f >>= processContent f

processContent :: FilePath -> String -> IO ()
processContent f str = do
  let l = zip [1 ..] $ lines str
      n = length l
      nls = takeWhile (== '\n') $ reverse str
  mapM_ (checkLine f) l
  checkBlankLines f 1 l
  case nls of
    [] -> diag f n "missing final newline"
    [_] -> return ()
    _ -> diag f n "trailing empty lines"

diag :: FilePath -> Int -> String -> IO ()
diag f n str =
  putStrLn $ (if null f then "Line " else f ++ " at ") ++  show n ++ ": " ++ str

checkBlankLines :: FilePath -> Int -> [(Int, String)] -> IO ()
checkBlankLines f c l = case l of
  [] -> return ()
  (n, s) : r ->
    if null $ filter (not . isSpace) s then
      if c >= 2 then do
        diag f n "too many consecutive blank lines"
        checkBlankLines f 0 r
      else checkBlankLines f (c + 1) r
    else checkBlankLines f 0 r

checkPrefix :: String -> String -> String -> Maybe String
checkPrefix p n s = let ps = map (\ c -> p ++ [c]) n in
  if any (flip isPrefixOf s) ps then Nothing else case stripPrefix p s of
  Nothing -> Nothing
  Just r -> case startsWithSpace r of
    Nothing -> Nothing
    Just c -> Just $ p ++ [c]

-- | checks comment starts
checkPrefixes :: String -> Maybe String
checkPrefixes s = case checkPrefix "{-#" "" s of
  Nothing -> case checkPrefix "{-!" "" s of
    Nothing -> case checkPrefix "{-" "#!" s of
      Nothing -> checkPrefix "--" "" s
      r -> r
    r -> r
  r -> r

startsWithSpace :: String -> Maybe Char
startsWithSpace s = case s of
  [] -> Nothing
  ' ' : c : _ -> if c /= ' ' then Nothing else Just c
  c : _ -> Just c

checkLine :: FilePath -> (Int, String) -> IO ()
checkLine f (n, s) = do
  let r = reverse s
      (bs, rt) = span isSpace r
      l = length rt
      trailBSlash = takeWhile (== '\\') rt
      badChars = filter (\c -> not $ isAscii c && isPrint c) s
  unless (null bs) $
    diag f n "trailing white space (use: perl -i -ple 's/ +$//g')"
  when (l > 80) $
    diag f n $ "too long line (" ++ show l ++ " chars)"
  unless (null badChars) $
    diag f n $ "contains undesirable characters: " ++ show badChars
  unless (null trailBSlash) $
    diag f n $ "back slash at line end (may disturb cpp)"
  case checkPrefixes $ dropWhile isSpace s of
    Just p -> diag f n $ "insert a single space in" ++ show p
    Nothing -> return ()
