{-# LANGUAGE CPP #-}
{- |
Module      :  ./Driver/ReadLibDefn.hs
Description :  reading Lib-Defns
Copyright   :  (c) C. Maeder, DFKI 2014
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

reading Lib-Defns for various logics, OWL and CL return several Lib-Defns
-}

module Driver.ReadLibDefn (readLibDefn) where

import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.Parse_AS_Library

import ATC.Sml_cats
import ATC.LibName ()

import CommonLogic.ParseCLAsLibDefn
#ifndef NOOWLLOGIC
import OWL2.ParseOWLAsLibDefn
#endif
#ifdef RDFLOGIC
-- import RDF.ParseRDFAsLibDefn -- MODULE RDF IS BROKEN AT THE MOMENT
#endif
import CSMOF.ParseXmiAsLibDefn
import QVTR.ParseQvtAsLibDefn
import SoftFOL.ParseTPTPAsLibDefn
import FreeCAD.Logic_FreeCAD

import Driver.Options
import Driver.ReadFn

import Common.AnnoState
import Common.Result
import Common.ResultT

import Text.ParserCombinators.Parsec

import Control.Monad.Trans (MonadIO (..))
import Data.List

mimeTypeMap :: [(String, InType)]
mimeTypeMap =
  [ ("xml", DgXml)
  , ("html", HtmlIn)
  , ("rdf", OWLIn RdfXml)
  , ("owl", OWLIn OwlXml)
  , ("obo", OWLIn OBO)
  , ("ttl", OWLIn Turtle)
  , ("turtle", OWLIn Turtle)
  , ("omn", OWLIn Manchester)
  , ("dol", DOLIn)
  , ("clif", CommonLogicIn True)
  , ("het", HetCASLIn)
  , ("casl", CASLIn)
  , ("tptp", TPTPIn)
  , ("p", TPTPIn) ]

owlXmlTypes :: [InType]
owlXmlTypes = map OWLIn [OwlXml, RdfXml, Turtle]

joinFileTypes :: InType -> InType -> InType
joinFileTypes ext magic = case (ext, magic) of
  (GuessIn, _) -> magic
  (_, GuessIn) -> ext
  (DgXml, _) | elem magic owlXmlTypes -> magic
  (_, DgXml) | elem ext owlXmlTypes -> ext
  (_, HtmlIn) -> magic
  _ -> ext -- ignore contradictions

findFiletype :: String -> InType
findFiletype s =
  maybe GuessIn snd $ find (\ (r, _) -> isInfixOf ('/' : r) s) mimeTypeMap

guessInput :: MonadIO m => HetcatsOpts -> Maybe String -> FilePath -> String
  -> m InType
guessInput opts mr file input =
  let fty1 = guess file (intype opts)
      fty2 = maybe GuessIn findFiletype mr
      fty = joinFileTypes fty1 fty2
  in if elem fty $ GuessIn : DgXml : owlXmlTypes then
    case guessXmlContent (fty == DgXml) input of
    Left ty -> fail ty
    Right ty -> case ty of
      DgXml -> fail "unexpected DGraph xml"
      _ -> return $ joinFileTypes fty ty
  else return fty

readLibDefn :: LogicGraph -> HetcatsOpts -> Maybe String
  -> FilePath -> FilePath -> String -> ResultT IO [LIB_DEFN]
readLibDefn lgraph opts mr file fileForPos input =
    if null input then fail ("empty input file: " ++ file) else
    case intype opts of
    ATermIn _ -> return [from_sml_ATermString input]
    FreeCADIn ->
      liftIO $ fmap (: []) . readFreeCADLib file $ fileToLibName opts file
    _ -> do
     ty <- guessInput opts mr file input
     case ty of
      HtmlIn -> fail "unexpected html input"
      CommonLogicIn _ -> parseCL_CLIF file opts
#ifdef RDFLOGIC
     -- RDFIn -> liftIO $ parseRDF file
#endif
      Xmi -> liftIO $ fmap (: []) $ parseXmi file
      Qvt -> liftIO $ fmap (: []) $ parseQvt file
      TPTPIn -> liftIO $ fmap (: []) $ parseTPTP input file
#ifndef NOOWLLOGIC
      OWLIn _ -> parseOWLAsLibDefn (isStructured opts) file
#endif
      _ -> case runParser (library lgraph { dolOnly = ty == DOLIn })
           (emptyAnnos ()) fileForPos input of
         Left err -> fail (showErr err)
         Right ast -> return [ast]
