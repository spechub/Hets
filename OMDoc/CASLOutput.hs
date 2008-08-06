{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

Output-methods for writing OMDoc
Toplevel module providing the composition of all translations CASL -> OMDoc
Recurses over imported CASL libraries
-}
module OMDoc.CASLOutput where

import qualified OMDoc.HetsDefs as Hets
import qualified CASL.Morphism as Morphism
import qualified Syntax.AS_Library as ASL

import qualified Data.Graph.Inductive.Graph as Graph

import qualified Data.Map as Map

import Debug.Trace (trace)

import Data.Char (toLower)

import OMDoc.Util

import qualified Network.URI as URI

-- | Retrieve the XML-names for the sort meaning
mappedsorts :: [(Hets.WithOrigin Hets.Identifier Graph.Node, String)]
            -> [Char]
            -> [(Hets.WithOrigin Hets.Identifier Graph.Node, String)]
            -> ASL.LIB_NAME
            -> Hets.CollectionMap
            -> [Hets.IdNameMapping]
            -> Graph.Node
            -> Graph.Node
            -> Morphism.Morphism f e m
            -> [((String, (Maybe URI.URI, String)),
                 (String, (Maybe URI.URI, String)))]

mappedsorts fromSortIds e_fname toSortIds ln collectionMap uniqueNames from to
  caslmorph =
      Map.foldWithKey
        (\origsort newsort ms ->
          let
            oname =
              case
                filter
                  (\(oid', _) -> Hets.getIdId (Hets.woItem oid') == origsort)
                  fromSortIds
              of
               [] -> error (e_fname ++ "Sort not in From-Set!")
               s:_ -> snd s
            nname =
              case
                filter
                  (\(nid', _) -> Hets.getIdId (Hets.woItem nid') == newsort)
                  toSortIds
              {-  Set.toList
                  $
                  Set.filter
                    (\(nid', _) -> nid' == newsort)
                    (Hets.inmGetIdNameSortSet toIdNameMapping)
              -}
              of
               [] -> error (e_fname ++ "Sort not in To-Set!")
               s:_ -> snd s
            oorigin =
              getNodeNameBaseForXml
                ln
                $
                findOrigin
                  collectionMap
                  uniqueNames
                  Hets.findIdIdsForName
                  (ln, from)
                  oname
                  id -- adjustStringForXmlName
                  " (sorts, from)"
            norigin =
              getNodeNameBaseForXml
                ln
                $
                findOrigin
                  collectionMap
                  uniqueNames
                  Hets.findIdIdsForName
                  (ln, to)
                  nname
                  id -- adjustStringForXmlName
                  " (sorts, to)"
         in
          ms ++ [ ((oname, oorigin), (nname, norigin)) ]
        )
        []
        (Morphism.sort_map caslmorph)

findOrigin
  ::Hets.CollectionMap
  ->[Hets.IdNameMapping]
  ->(
      Hets.CollectionMap
      ->(Hets.LIB_NAME, Graph.Node)
      ->String
      ->(String->String)
      ->[(Hets.LIB_NAME, Hets.IdentifierWON)]
    )
  ->(Hets.LIB_NAME, Graph.Node)
  ->String
  ->(String->String)
  ->String
  ->Hets.IdNameMapping
findOrigin
  collMap
  mappings
  searchFun
  loc
  sName
  stringproc
  debugMsg
  =
    case searchFun collMap loc sName stringproc of
      [] ->
        error
          (
            "No Origin for \"" ++ sName ++ "\""
            ++ debugMsg ++ " "
            ++ (show (Map.findWithDefault (Debug.Trace.trace "Empty!" Map.empty) loc collMap))
          )
      ((iln, idwo):r) ->
        (\x ->
          if null r
            then
              x
            else
              Debug.Trace.trace
                (
                  "More than one origin for \"" ++ sName ++ "\""
                  ++ debugMsg
                )
                x
        )
        $
        case Hets.getLNGN mappings iln (Hets.woOrigin idwo) of
          Nothing ->
            error
              (
                "Non-existant origin for \""
                ++ sName ++ "\" " ++ show (iln, Hets.woOrigin idwo)
                ++ debugMsg
              )
          (Just o) -> o

getNodeNameBaseForXml
  ::Hets.LIB_NAME
  ->Hets.IdNameMapping
  ->(Maybe URI.URI, String)
getNodeNameBaseForXml
  currentLib
  inm
  =
  let
    libName = Hets.inmGetLibName inm
    libURIS = asOMDocFile $ unwrapLinkSource libName
    asUri = URI.parseURIReference libURIS
    uriRes = if currentLib /= libName then asUri else Nothing
  in
    (uriRes, Hets.inmGetNodeId inm)

-- | returns an 'omdoc-version' of a filename (e.g. test.env -> test.omdoc)
asOMDocFile::String->String
asOMDocFile file =
  let
    parts = splitFile' file
    fullfilename = last parts
    filenameparts = explode "." fullfilename
    (filename, mfileext) =
      case (length filenameparts) of
        0 -> ("", Nothing)
        1 -> (head filenameparts, Nothing)
        2 -> case head filenameparts of
          "" -> ("."++(last filenameparts), Nothing)
          fn -> (fn, Just (last filenameparts))
        _ -> ( implode "." $ init filenameparts, Just (last filenameparts))
  in
    case mfileext of
      Nothing -> joinFile $ (init parts) ++ [filename ++ ".omdoc"]
      (Just fileext) ->
        case map toLower fileext of
          "omdoc" -> file
          _ -> joinFile $ (init parts) ++ [filename ++ ".omdoc"]
  where
  splitFile' ::String->[String]
  splitFile' = explode "/"
  joinFile::[String]->String
  joinFile = implode "/"

-- | extract the source-component from a library name
unwrapLinkSource::ASL.LIB_NAME->String
unwrapLinkSource
  (ASL.Lib_id lid) = unwrapLID lid
unwrapLinkSource
  (ASL.Lib_version lid _) = unwrapLID lid

-- | extract the source from a library ID
unwrapLID::ASL.LIB_ID->String
unwrapLID (ASL.Indirect_link path _ _ _) = path
unwrapLID (ASL.Direct_link url _) = url
