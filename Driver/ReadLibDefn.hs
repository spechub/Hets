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

import Control.Monad.Trans (MonadIO (..), lift)
import Control.Monad (liftM)
import Data.List

mimeTypeMap :: [(String, InType)]
mimeTypeMap =
  [ ("xml", DgXml)
  , ("html", HtmlIn)
  ] ++ map (\tp -> (show tp, tp)) listOwlInTypes ++
  [ ("clif", CommonLogicIn True)
  , ("het", HetCASLIn)
  , ("casl", CASLIn) ]

joinFileTypes :: InType -> InType -> InType
joinFileTypes ext magic = case (ext, magic) of
  (GuessIn, _) -> magic
  (_, GuessIn) -> ext
  (DgXml, _) | elem magic $ DgXml : map OWLIn [RdfXml, OwlXml] -> magic
  (_, HtmlIn) -> magic
  -- (_, DgXml) | elem ext [DgXml, RDFIn, OWLIn, OwlXmlIn, OBOIn, Xmi] -> ext
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
  in if elem fty $ GuessIn : DgXml : map OWLIn [RdfXml, OwlXml] then
    case guessXmlContent (fty == DgXml) input of
    Left ty -> fail ty
    Right ty -> case ty of
      DgXml -> fail "unexpected DGraph xml"
      _ -> return ty
  else return fty

readLibDefn :: MonadIO m => LogicGraph -> HetcatsOpts -> Maybe String
  -> FilePath -> FilePath -> String -> m [LIB_DEFN]
readLibDefn lgraph opts mr file fileForPos input =
    if null input then fail ("empty input file: " ++ file) else
    case intype opts of
    ATermIn _ -> return [from_sml_ATermString input]
    FreeCADIn ->
      liftIO $ fmap (: []) . readFreeCADLib file $ fileToLibName opts file
    _ -> do
     ty <- guessInput opts mr file input
     liftIO $ putIfVerbose opts 2 $ "parsing " ++ show ty ++ " file"
     case ty of
      HtmlIn -> fail "unexpected html input"
      CommonLogicIn _ -> liftIO $ parseCL_CLIF file opts
#ifdef RDFLOGIC
 -- - RDFIn -> liftIO $ parseRDF file
#endif
      Xmi -> liftIO $ fmap (: []) $ parseXmi file
      Qvt -> liftIO $ fmap (: []) $ parseQvt file
      TPTPIn -> liftIO $ fmap (: []) $ parseTPTP file
#ifndef NOOWLLOGIC
      OWLIn _ -> liftIO $ do
        putIfVerbose opts 2 $ "parsing " ++ show ty ++ " file"
        parseOWL (isStructured opts) (show ty) file
#endif
      _ -> case runParser (library lgraph) (emptyAnnos ()) fileForPos input of
         Left err -> fail (showErr err)
         Right ast -> return [ast]
