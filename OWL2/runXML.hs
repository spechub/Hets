import System.Environment

import OWL2.XML
import Text.XML.Light
import OWL2.Print ()
import OWL2.ManchesterPrint ()
import Common.DocUtils

processFile :: String -> IO ()
processFile file = do
  s <- readFile file
  case parseXML s of 
    elems -> putStrLn $ showDoc (map xmlBasicSpec $ concatMap (filterElementsName $ isSmth "Ontology") $ onlyElems elems) "\n"

main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
