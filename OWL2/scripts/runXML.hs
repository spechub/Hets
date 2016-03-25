{- |
Module      :  ./OWL2/scripts/runXML.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

script for running the parsing of XML
-}

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
    elems -> print (map xmlBasicSpec
                        $ concatMap (filterElementsName $ isSmth "Ontology")
                        $ onlyElems elems)
main :: IO ()
main = do
  args <- getArgs
  mapM_ processFile args
