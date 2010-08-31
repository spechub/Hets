{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
import Common.XPath
import Text.ParserCombinators.Parsec
import Common.Parsec

main :: IO ()
main = do
  str <- getContents
  mapM_ process $ zip [1 ..] $ lines str

process :: (Int, String) -> IO ()
process (n, str) = case parse (spaces >> expr << eof) "" str of
  Left err -> fail $ "line " ++ show n ++ ": " ++ show err
  Right e -> print e
