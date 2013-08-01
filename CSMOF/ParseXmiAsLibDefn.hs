{- |
Module      :  $Header$
Description :  CSMOF XMI parser
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module CSMOF.ParseXmiAsLibDefn where

import CSMOF.As
import CSMOF.Parser
import CSMOF.Logic_CSMOF

import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.AS_Structured
import Common.AS_Annotation
import Common.IRI
import Common.Id
import Common.LibName

import Text.XML.Light
import System.IO


parseXmi :: FilePath -> IO LIB_DEFN
parseXmi fp = 
  do
    handle <- openFile fp ReadMode  
    contents <- hGetContents handle 
    case parseXMLDoc contents of
      Nothing -> return (Lib_defn (emptyLibName (convertFileToLibStr fp)) [] nullRange [])
      Just el -> return (parseCSMOFXmi fp el)


parseCSMOFXmi :: FilePath -> Element -> LIB_DEFN
parseCSMOFXmi filename contentOfFile = convertToLibDefN filename (parseCSMOF contentOfFile)


convertToLibDefN :: FilePath -> Metamodel -> LIB_DEFN
convertToLibDefN filename el = Lib_defn
                               (emptyLibName $ convertFileToLibStr filename)
                               (makeLogicItem CSMOF : [convertoItem el])
                               nullRange []


convertoItem :: Metamodel -> Annoted LIB_ITEM
convertoItem el = makeSpecItem (simpleIdToIRI $ mkSimpleId $ metamodelName el) $ createSpec el


createSpec :: Metamodel -> Annoted SPEC
createSpec el = makeSpec $ G_basic_spec CSMOF el

