import System.Environment

import qualified OWL2.AS as AS
import RDF.AS
import RDF.Parse
import RDF.Print

import Common.DocUtils
import Common.Parsec

import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

processFile :: String -> IO ()
processFile file = do
  str <- readFile file
  case runParser (basicSpec Map.empty << eof) () file str of
    Right o -> putStrLn $ showDoc o "\n"
    Left err -> print err

main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
