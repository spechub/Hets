{- |
Module      :  $Header$
Description :  Hets-to-OMDoc morphism conversion
Copyright   :  (c) Elena Digor, Jacobs University Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  edigor@jacobs-university.de
Stability   :  provisional
Portability :  non-portable(Logic)

Output-methods used by OMDoc.CASLOutput for writing OMDoc morphism
elementary methods to retrieve XML-names for sorts, opperators, and predicates
module called by createOMMorphism
-}
module OMDoc.CASLOutput where

import qualified OMDoc.HetsDefs as Hets

import qualified CASL.Morphism as Morphism
import CASL.Sign
import CASL.AS_Basic_CASL

import qualified Common.LibName as ASL
import qualified Common.Lib.Rel as Rel
import Common.Utils (splitOn)

import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import Data.List (intercalate)
import Data.Char (toLower)

import qualified Network.URI as URI

import Debug.Trace (trace)

-- | Retrieve the XML-names for the sort meaning
mappedsorts :: [(Hets.WithOrigin Hets.Identifier Graph.Node, String)]
            -> [Char]
            -> [(Hets.WithOrigin Hets.Identifier Graph.Node, String)]
            -> ASL.LibName
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

-- | retrieve the XML-names for the predicate mapping
mappedpreds::(Show b1) =>
                         [((Hets.WithOrigin Hets.Identifier b1, PredType),
                                             String)]
             -> [Char]
                         -> Morphism.Morphism f e m
             -> [((Hets.WithOrigin Hets.Identifier b, PredType),
                                        String)]
                         -> ASL.LibName
             -> Hets.CollectionMap
                         -> [Hets.IdNameMapping]
                         -> Rel.Rel SORT
             -> Graph.Node
             -> Rel.Rel SORT
             -> Graph.Node
                     -> [((String, (Maybe URI.URI, String)),
                  (String, (Maybe URI.URI, String)))]
mappedpreds fromPredIds e_fname caslmorph toPredIds ln collectionMap uniqueNames
        fromRel from toRel to=
      Map.foldWithKey
        (\(origpred, optype) newpred mp ->
          let
            oname =
              case
                filter
                  (\((oid', opt'), _) ->
                    Hets.getIdId (Hets.woItem oid') == origpred
                    && opt' == optype
                  )
                  fromPredIds
                {-
                Set.toList
                  $
                  Set.filter
                    (\((oid', opt'), _) -> oid' == origpred && opt' == optype)
                    (Hets.inmGetIdNamePredSet fromIdNameMapping)
                -}
              of
               [] ->
                error
                  (
                    e_fname
                    ++ "Pred not in From-Set! " ++ show origpred
                    ++ " not in "
                    ++ show fromPredIds
                    -- ++ show (Hets.inmGetIdNamePredSet fromIdNameMapping)
                  )
               s:_ -> snd s
            nptype = Morphism.mapPredType (Morphism.sort_map caslmorph) optype
            nname =
              case
                filter
                  (\((nid', npt'), _) ->
                    Hets.getIdId (Hets.woItem nid') == newpred
                    && npt' == nptype
                  )
                  toPredIds
                {-
                Set.toList
                  $
                  Set.filter
                    (\((nid', npt'), _) -> nid' == newpred && npt' == nptype)
                    (Hets.inmGetIdNamePredSet toIdNameMapping)
                -}
              of
               [] -> error (e_fname ++ "Pred not in To-Set!")
               s:_ -> snd s
            oorigin =
              getNodeNameBaseForXml
                ln
                $
                findOrigin
                  collectionMap
                  uniqueNames
                  (Hets.findIdPredsForName fromRel optype)
                  (ln, from)
                  oname
                  id -- adjustStringForXmlName
                  " (preds, from)"
            norigin =
              getNodeNameBaseForXml
                ln
                $
                findOrigin
                  collectionMap
                  uniqueNames
                  (Hets.findIdPredsForName toRel nptype)
                  (ln, to)
                  nname
                  id -- adjustStringForXmlName
                  " (preds, to)"
         in
          mp ++ [ ((oname, oorigin), (nname, norigin)) ]
        )
        []
        (Morphism.pred_map caslmorph)

-- | retrieve the XML-names for the operator mapping
mappedops::[((Hets.WithOrigin Hets.Identifier b1, OpType), String)]
                        -> [Char]
                        -> Morphism.Morphism f e m
                        -> [((Hets.WithOrigin Hets.Identifier b, OpType), String)]
                        -> ASL.LibName
                        -> Hets.CollectionMap
                        -> [Hets.IdNameMapping]
                        -> Rel.Rel SORT
                        -> Graph.Node
                        -> Rel.Rel SORT
                        -> Graph.Node
                        -> [((String, (Maybe URI.URI, String)),
                                 (String, (Maybe URI.URI, String)))]
mappedops fromOpIds e_fname caslmorph toOpIds ln collectionMap uniqueNames
                  fromRel from toRel to =
      Map.foldWithKey
        (\(origop, ootype) (newop, nfk) mo ->
          let
            oname =
              case
                filter
                  (\((oid', oot'), _) ->
                    Hets.getIdId (Hets.woItem oid') == origop
                    && oot' { opKind = opKind ootype } == ootype
                  )
                  fromOpIds
                {-
                Set.toList
                  $
                  Set.filter
                    (\((oid', oot'), _) ->
                      oid' == origop
                      && oot' { opKind = opKind ootype } == ootype
                    )
                    (Hets.inmGetIdNameOpSet fromIdNameMapping)
                -}
              of
               [] -> error (e_fname ++ "Op not in From-Set!")
               s:_ -> snd s
            notype = Morphism.mapOpTypeK (Morphism.sort_map caslmorph) nfk ootype
            nname =
              case
                filter
                  (\((nid', not'), _) ->
                    Hets.getIdId (Hets.woItem nid') == newop
                    && not' { opKind = opKind notype } == notype
                  )
                  toOpIds
                {-
                Set.toList
                  $
                  Set.filter
                    (\((nid', not'), _) ->
                      nid' == newop
                      && not' { opKind = opKind notype } == notype
                    )
                    (Hets.inmGetIdNameOpSet toIdNameMapping)
                -}
              of
               [] -> error (e_fname ++ "Op not in To-Set!")
               s:_ -> snd s
            oorigin =
              getNodeNameBaseForXml
                ln
                $
                findOrigin
                  collectionMap
                  uniqueNames
                  (Hets.findIdOpsForName fromRel ootype)
                  (ln, from)
                  oname
                  id -- adjustStringForXmlName
                  (" (ops, from) " ++ show (origop, ootype))
            norigin =
              getNodeNameBaseForXml
                ln
                $
                findOrigin
                  collectionMap
                  uniqueNames
                  (Hets.findIdOpsForName toRel notype)
                  (ln, to)
                  nname
                  id -- adjustStringForXmlName
                  " (ops, to)"
         in
          mo ++ [ ((oname, oorigin), (nname, norigin)) ]
        )
        []
        (Morphism.op_map caslmorph)

findOrigin
  ::Hets.CollectionMap
  ->[Hets.IdNameMapping]
  ->(
      Hets.CollectionMap
      ->(ASL.LibName, Graph.Node)
      ->String
      ->(String->String)
      ->[(ASL.LibName, Hets.IdentifierWON)]
    )
  ->(ASL.LibName, Graph.Node)
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
  ::ASL.LibName
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
    filenameparts = splitOn '.' fullfilename
    (filename, mfileext) =
      case (length filenameparts) of
        0 -> ("", Nothing)
        1 -> (head filenameparts, Nothing)
        2 -> case head filenameparts of
          "" -> ("."++(last filenameparts), Nothing)
          fn -> (fn, Just (last filenameparts))
        _ -> ( intercalate "." $ init filenameparts, Just (last filenameparts))
  in
    case mfileext of
      Nothing -> joinFile $ (init parts) ++ [filename ++ ".omdoc"]
      (Just fileext) ->
        case map toLower fileext of
          "omdoc" -> file
          _ -> joinFile $ (init parts) ++ [filename ++ ".omdoc"]
  where
  splitFile' ::String->[String]
  splitFile' = splitOn '/'
  joinFile::[String]->String
  joinFile = intercalate "/"

-- | extract the source-component from a library name
unwrapLinkSource :: ASL.LibName -> String
unwrapLinkSource (ASL.LibName lid _) = unwrapLID lid

-- | extract the source from a library ID
unwrapLID :: ASL.LibId -> String
unwrapLID (ASL.IndirectLink path _ _ _) = path
unwrapLID (ASL.DirectLink url _) = url
