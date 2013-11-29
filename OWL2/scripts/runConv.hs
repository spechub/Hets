{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

script for running the conversion to XML
-}

import System.Environment

import OWL2.Sign
import OWL2.XML
import OWL2.XMLConversion
import Text.XML.Light
import OWL2.Print ()
import OWL2.ManchesterPrint ()

processFile :: String -> IO ()
processFile file = do
    s <- readFile file
    let elems = map xmlBasicSpec
                $ concatMap (filterElementsName $ isSmth "Ontology")
                $ onlyElems $ parseXML s
    mapM_ (putStrLn . ppElement . xmlOntologyDoc emptySign) elems

main :: IO ()
main = do
    args <- getArgs
    mapM_ processFile args
