{- |
Module      :  ./QVTR/ParseQvtAsLibDefn.hs
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

import Data.List (stripPrefix)
import Data.Maybe

import Text.XML.Light

import System.IO
import System.FilePath (replaceBaseName, replaceExtension, takeBaseName)

import Text.ParserCombinators.Parsec

parseQvt :: FilePath -> String -> IO LIB_DEFN
parseQvt fp input =
  case runParser pTransformation () fp input of  -- Either ParseError String
      Left erro -> do
                  print erro
                  return (Lib_defn (emptyLibName (convertFileToLibStr fp)) [] nullRange [])
      Right trans -> let (_, sMet, _) = sourceMetamodel trans
                         (_, tMet, _) = targetMetamodel trans
                     in
                       do
                         sourceMetam <- parseXmiMetamodel (replaceName fp sMet)
                         targetMetam <- parseXmiMetamodel (replaceName fp tMet)
                         return (convertToLibDefN fp (createTransfWithMeta trans sourceMetam targetMetam))


replaceName :: FilePath -> String -> String
replaceName fp = replaceBaseName (replaceExtension fp "xmi")


parseXmiMetamodel :: FilePath -> IO Metamodel
parseXmiMetamodel fullFileName =
  do
    let fp = fromMaybe fullFileName $ stripPrefix "file://" fullFileName
    handle <- openFile fp ReadMode
    contents <- hGetContents handle
    case parseXMLDoc contents of
      Nothing -> return Metamodel { metamodelName = takeBaseName fp
                           , element = []
                           , model = []
                           }
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


createTransfWithMeta :: Transformation -> Metamodel -> Metamodel -> Transformation
createTransfWithMeta trans souMeta tarMeta =
  let (sVar, sMet, _) = sourceMetamodel trans
      (tVar, tMet, _) = targetMetamodel trans
  in
    Transformation (transfName trans) (sVar, sMet, souMeta) (tVar, tMet, tarMeta) (keys trans) (relations trans)
