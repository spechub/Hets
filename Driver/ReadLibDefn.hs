{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  reading Lib-Defns
Copyright   :  (c) C. Maeder, DFKI 2014
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

reading Lib-Defns for various logics, OWL and CL return several Lib-Defns
-}

module Driver.ReadLibDefn where

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
-- import RDF.ParseRDFAsLibDefn
#endif
import CSMOF.ParseXmiAsLibDefn
import QVTR.ParseQvtAsLibDefn
import SoftFOL.ParseTPTPAsLibDefn
import FreeCAD.Logic_FreeCAD

import Driver.Options
import Driver.ReadFn

import Common.AnnoState
import Common.Result

import Text.ParserCombinators.Parsec

import Control.Monad.Trans (MonadIO (..))

guessInput :: MonadIO m => HetcatsOpts -> FilePath -> String -> m InType
guessInput opts file input = let fty = guess file (intype opts) in
  if elem fty [GuessIn, DgXml, RDFIn] then
    case guessXmlContent (fty == DgXml) input of
    Left ty -> fail ty
    Right ty -> case ty of
      DgXml -> fail "unexpected DGraph xml"
      _ -> return ty
  else return fty

readLibDefn :: MonadIO m => LogicGraph -> HetcatsOpts -> FilePath
  -> FilePath -> String -> m [LIB_DEFN]
readLibDefn lgraph opts file fileForPos input =
    if null input then fail ("empty input file: " ++ file) else
    case intype opts of
    ATermIn _ -> return [from_sml_ATermString input]
    FreeCADIn ->
      liftIO $ fmap (: []) . readFreeCADLib file $ fileToLibName opts file
    _ -> do
     ty <- guessInput opts file input
     case ty of
      CommonLogicIn _ -> liftIO $ parseCL_CLIF file opts
#ifdef RDFLOGIC
 -- - RDFIn -> liftIO $ parseRDF file
#endif
      Xmi -> liftIO $ fmap (: []) $ parseXmi file
      Qvt -> liftIO $ fmap (: []) $ parseQvt file
      TPTPIn -> liftIO $ fmap (: []) $ parseTPTP file
#ifndef NOOWLLOGIC
      _ | elem ty [OWLIn, OwlXmlIn, OBOIn] -> liftIO
        $ parseOWL (isStructured opts) file
#endif
      _ -> case runParser (library lgraph) (emptyAnnos ()) fileForPos input of
         Left err -> fail (showErr err)
         Right ast -> return [ast]
