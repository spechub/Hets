import System.Environment

import OWL2.AS
import RDF.AS
import RDF.Parse

import Common.DocUtils
import Common.Parsec

import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

processFile :: String -> IO ()
processFile file = do
  str <- readFile file
  case runParser (parseTriples (BaseIRI dummyQName) Map.empty "." << eof) () file str of
    Right o -> putStrLn $ show o
    Left err -> print err

main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
