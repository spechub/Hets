module OWL2.TestXML where

import System.Process
import System.Environment
import System.IO
import System.Directory
import Data.List (sort,isSuffixOf, isPrefixOf, (\\), sortOn)
import Data.Foldable (find)
import Data.Maybe (fromJust)


-- import OWL2.PrintMS
import OWL2.AS
import Text.XML.Light
import OWL2.XML
import OWL2.XMLConversion
import OWL2.Sign(emptySign)
import OWL2.Pretty
import qualified Data.ByteString.Lazy as L

main :: IO ()
main = do
    args <- getArgs
    let files = filter (not . isPrefixOf "--") args
    o <- mapM (\f -> do 
      str <- readFile f
      -- putStrLn $ take 500 $ show $ onlyElems $ parseXML str
      let rootElem = fromJust $ find (\e -> "Ontology" == qName (elName e))  $ onlyElems $ parseXML str
      -- putStrLn $ show $ rootElem
      let parsed1 = (xmlBasicSpec mempty) rootElem
      writeFile (f ++ ".parsed1.out") $ show ( parsed1) 
      let printed = (xmlOntologyDoc emptySign parsed1)
      writeFile (f ++ ".printed.out") $ ppTopElement printed
      let parsed2 = xmlBasicSpec mempty printed
      writeFile (f ++ ".parsed2.out") $ show ( parsed2)
      let r = ontology parsed1 == ontology parsed2
      if r then return () else putStrLn $ "Error in " ++ f
      putStrLn ""
      return r) files
    putStrLn $ show (length $ filter id o) ++ "/" ++ show (length o)
    if (length $ filter not o) > 0 then fail "Failed!" else return ()
