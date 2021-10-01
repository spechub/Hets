
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
      -- putStrLn $ show $ (!! 0) . onlyElems $ parseXML str
      let parsed1 = (xmlBasicSpec mempty) ((!! 0) . onlyElems $ parseXML str)
      let printed = (xmlOntologyDoc emptySign parsed1)
      let parsed2 = xmlBasicSpec mempty printed
      let r = parsed1 == parsed2
      if r then return () else do
        putStrLn $ "Error in " ++ f
        putStrLn $ "parsed1: " ++ show (toDocAsAS parsed1)
        putStrLn $ "parsed2: " ++ show (toDocAsAS parsed2)
        putStrLn ""
      return r) files
    putStrLn $ show (length $ filter id o) ++ "/" ++ show (length o)

