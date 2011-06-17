import System.Environment

import OWL2.ManchesterParser
import OWL2.Print ()
import OWL2.ManchesterPrint()

import Common.DocUtils
import Common.Parsec

import Text.ParserCombinators.Parsec

processFile :: String -> IO ()
processFile file = do
  str <- readFile file
  case runParser (basicSpec << eof) () file str of
    Right o -> putStrLn $ showDoc o "\n"
    Left err -> print err

main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
