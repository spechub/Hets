import System.Environment

import OWL2.XML
import Text.XML.Light
import OWL2.Print ()
import OWL2.ManchesterPrint ()
import Common.DocUtils

processFile :: String -> IO ()
processFile file = do
  s <- readFile file
  case parseXMLDoc s of 
    Nothing -> fail "error"
    Just elems -> putStrLn $ showDoc (xmlBasicSpec elems) "\n"

main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
