
module OWL2.TestXML where

import System.Process
import System.Environment
import System.IO
import System.Directory
import Data.List (sort,isSuffixOf, isPrefixOf, (\\), sortOn)
import Data.Foldable (find)
import Data.Maybe (fromJust)

-- import OWL2.PrintMS
import Text.XML.Light
import OWL2.XML
import OWL2.ParseOWL
import qualified Data.ByteString.Lazy as L



main :: IO ()
main = do
    args <- getArgs
    let files = filter (not . isPrefixOf "--") args
    o <- mapM (\f -> do 
      str <- readFile f
      putStrLn $ show $ (!! 1) . onlyElems $ parseXML str
      let r = (xmlBasicSpec mempty) (head . findChildren (unqual "Ontology") . (!! 1) . onlyElems $ parseXML str)
      putStrLn $ show r
      return r) files
    putStrLn $ show $ length o

