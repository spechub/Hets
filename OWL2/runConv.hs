import System.Environment

import OWL2.XML
import OWL2.XMLConversion
import Text.XML.Light
import OWL2.Print()
import OWL2.ManchesterPrint()
import Common.DocUtils
processFile :: String -> IO ()
processFile file = do
    s <- readFile file
    let elems = map xmlBasicSpec $ concatMap (filterElementsName $ isSmth "Ontology") $ onlyElems $ parseXML s
    putStrLn $ show (map ppElement $ map xmlOntologyDoc elems)

main :: IO ()
main = do
    args <- getArgs
    mapM_ processFile args
