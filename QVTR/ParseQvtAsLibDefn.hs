{- |
Module      :  $Header$
Description :  QVTR .qvt parser
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

module QVTR.ParseQvtAsLibDefn where

import CSMOF.As
import CSMOF.Parser

import QVTR.As
import QVTR.Parser
import QVTR.Logic_QVTR

import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.AS_Structured
import Common.AS_Annotation
import Common.IRI
import Common.Id
import Common.LibName

import Text.XML.Light

import System.IO
import System.FilePath (replaceBaseName, replaceExtension, takeBaseName)


parseQvt :: FilePath -> IO LIB_DEFN
parseQvt fp = 
  do
    handle <- openFile fp ReadMode  
    input <- hGetContents handle 
    sourceMetam <- parseXmiMetamodel (replaceName fp input Source)
    targetMetam <- parseXmiMetamodel (replaceName fp input Target)
    return (convertToLibDefN fp (parseQVTR input sourceMetam targetMetam))


replaceName :: FilePath -> String -> Side -> String
replaceName fp input side = replaceBaseName (replaceExtension fp "xmi") (getMetamodelName input fp side) 


parseXmiMetamodel :: FilePath -> IO Metamodel
parseXmiMetamodel fp = 
  do
    handle <- openFile fp ReadMode  
    contents <- hGetContents handle 
    case parseXMLDoc contents of
      Nothing -> return (Metamodel { metamodelName = takeBaseName fp
                           , element = []
                           , model = []
                           })
      Just el -> return (parseCSMOF el)


convertToLibDefN :: FilePath -> Transformation -> LIB_DEFN
convertToLibDefN filename el = Lib_defn
                               (emptyLibName $ convertFileToLibStr filename)
                               (makeLogicItem QVTR : [convertoItem el])
                               nullRange []

convertoItem :: Transformation -> Annoted LIB_ITEM
convertoItem el = makeSpecItem (simpleIdToIRI $ mkSimpleId $ transfName el) $ createSpec el

createSpec :: Transformation -> Annoted SPEC
createSpec el = makeSpec $ G_basic_spec QVTR el


