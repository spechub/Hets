import System.Environment

import OWL2.Parse
import OWL2.Print ()

import Common.DocUtils

import Text.ParserCombinators.Parsec

processFile :: String -> IO ()
processFile file = do
  str <- readFile file
  case runParser basicSpec () file str of
    Right o -> putStrLn $ showDoc o "\n"
    Left err -> print err

main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
