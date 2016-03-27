{- |
Module      :  ./CSMOF/tests/Test_Logic.hs
Description :  Test case for CSMOF parsing, parses a file and shows the resulting CSMOF metamodel
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

-- From the CSMOF folder run: ghc -i.. -o main Test_Parser.hs


import CSMOF.ParseXmiAsLibDefn
import CSMOF.Print
import CSMOF.Parser

import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.AS_Structured
import Common.AS_Annotation
import Common.IRI
import Common.Id
import Common.LibName

import Text.XML.Light
import System.IO

import Common.Doc
import Common.DocUtils


main :: IO ()
main =
  let fp = "MetamodelWMult.xmi"
  in
  do
    handle <- openFile fp ReadMode
    contents <- hGetContents handle
    case parseXMLDoc contents of
      Nothing -> print $ Lib_defn (emptyLibName (convertFileToLibStr fp)) [] nullRange []
      Just el -> print $ parseCSMOFXmi fp el
    hClose handle
