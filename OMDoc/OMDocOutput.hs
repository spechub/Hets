{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

  Output-methods for writing OMDoc

  BUGS/TODO:
    - better interpretation of imports
    - existings files should not be overwritten everytime...
    - there is a problem with finding constructors that use tricky names,
      currently working on debuggin this
    - DevGraph->OMDoc conversion should be done on LibEnv-Level (for names) (done)
-}
module OMDoc.OMDocOutput
  (
    hetsToOMDoc
  ) 
{- -- debug 
  (
    writeOMDocDTD
    -- ,showOMDoc
    -- ,showOMDocDTD
    -- ,writeOMDoc
    ,hetsToOMDoc
    ,defaultDTDURI
    ,createXmlNameMapping
  )
 -}
  where

import qualified OMDoc.HetsDefs as Hets
import CASL.Sign
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import qualified CASL.Morphism as Morphism
import qualified Common.Id as Id
import qualified Syntax.AS_Library as ASL
import qualified CASL.AS_Basic_CASL as ABC

import Driver.Options

import Common.Utils (joinWith)

import Static.DevGraph
import qualified Data.Graph.Inductive.Graph as Graph

-- Often used symbols from HXT
import Text.XML.HXT.Parser
  ( 
      a_name, k_public, k_system, emptyRoot
    , v_1, a_indent, a_output_file
  )
        
import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)
import qualified Text.XML.HXT.DOM.XmlTreeTypes as HXTT hiding (when)

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import qualified Common.AS_Annotation as Ann

import Data.Maybe (fromMaybe)
import Data.List (find)

import Debug.Trace (trace)

import qualified System.Directory as System.Directory

import Control.Monad

import Char (toLower)

import OMDoc.Util
import OMDoc.XmlHandling
import OMDoc.OMDocDefs

import qualified OMDoc.OMDocInterface as OMDoc
import qualified OMDoc.OMDocXml as OMDocXML

import qualified Network.URI as URI

-- | generate a DOCTYPE-Element for output
mkOMDocTypeElem::
  String -- ^ URI for DTD
  ->HXTT.XNode -- ^ DOCTYPE-Element
mkOMDocTypeElem system =
  HXTT.XDTD
    HXTT.DOCTYPE
      [
         (a_name, "omdoc")
        ,(k_public, "-//OMDoc//DTD OMDoc V1.2//EN")
        ,(k_system, system)
      ]

{- |
        default OMDoc-DTD-URI
        www.mathweb.org does not provide the dtd anymore (or it is hidden..)
        defaultDTDURI = <http://www.mathweb.org/src/mathweb/omdoc/dtd/omdoc.dtd>
        the svn-server does provide the dtd but all my validating software refuses to load it...
        defaultDTDURI = <https://svn.mathweb.org/repos/mathweb.org/trunk/omdoc/dtd/omdoc.dtd>
        my private copy of the modular omdoc 1.2 dtd...
        defaultDTDURI = </home/hendrik/Dokumente/Studium/Hets/cvs/HetCATScopy/utils/Omdoc/dtd/omdoc.dtd>
        until dtd-retrieving issues are solved I put the dtd online...
-}
defaultDTDURI::String
defaultDTDURI = "http://www.tzi.de/~hiben/omdoc/dtd/omdoc.dtd"

envDTDURI::IO String
envDTDURI = getEnvDef "OMDOC_DTD_URI" defaultDTDURI

-- | this function wraps trees into a form that can be written by HXT
writeableTreesDTD::String->HXT.XmlTrees->HXT.XmlTree
writeableTreesDTD dtd' t =
  (HXT.NTree
    ((\(HXT.NTree a _) -> a) emptyRoot)
    ((HXT.NTree (mkOMDocTypeElem dtd' ) [])
      :(HXT.NTree (HXT.XText "\n")[])
      :t)
  )

{- -- debug
-- | this function shows Xml with indention
showOMDoc::HXT.XmlTrees->IO HXT.XmlTrees
showOMDoc t = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_issue_errors, v_1)] $
    writeableTrees t
-}              

{- -- debug
-- | this function shows Xml with indention
showOMDocDTD::String->HXT.XmlTrees->IO HXT.XmlTrees
showOMDocDTD dtd' t = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_issue_errors, v_1)] $
    writeableTreesDTD dtd' t
-}

{- -- debug
-- | this function writes Xml with indention to a file
writeOMDoc::HXT.XmlTrees->String->IO HXT.XmlTrees
writeOMDoc t f = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_output_file, f)] $
    writeableTrees t
-}

-- | this function writes Xml with indention to a file
writeOMDocDTD::String->HXT.XmlTrees->String->IO HXT.XmlTrees
writeOMDocDTD dtd' t f = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_output_file, f)] $
    writeableTreesDTD dtd' t

-- | Hets interface for writing OMDoc files
hetsToOMDoc::HetcatsOpts->(ASL.LIB_NAME, LibEnv)->FilePath->IO ()
hetsToOMDoc hco lnle file =
  do
    --libToOMDocIdNameMapping hco lnle file
    libToOMDoc hco lnle file

libToOMDoc::
  HetcatsOpts
  ->(ASL.LIB_NAME, LibEnv)
  ->FilePath
  ->IO ()
libToOMDoc
  hco
  (ln, lenv)
  fp
  =
    let
      flatNames = Hets.getFlatNames lenv
      identMap = Hets.identifyFlatNames lenv flatNames
      remMap = Hets.removeReferencedIdentifiers flatNames identMap
      useMap = Hets.getIdUseNumber remMap
      unnMap = Hets.makeUniqueNames useMap
      uniqueNames = Hets.makeUniqueIdNameMapping lenv unnMap
      fullNames = Hets.makeFullNames lenv unnMap identMap
      uniqueNamesXml = id $! (createXmlNameMapping uniqueNames)
      fullNamesXml = id $! (createXmlNameMapping fullNames)
      outputio =
        if recurse hco
          then
            do
              dtduri <- envDTDURI
              mapM
                (\libname ->
                  let
                    filename = unwrapLinkSource libname
                    outfile = fileSandbox (outdir hco) $ asOMDocFile filename
                  in
                    do
                      omdoc <-
                        libEnvLibNameIdNameMappingToOMDoc
                          (emptyGlobalOptions { hetsOpts = hco })
                          lenv
                          libname
                          (createLibName libname)
                          uniqueNamesXml
                          fullNamesXml
                      omdocxml <- return $ (OMDocXML.toXml omdoc) HXT.emptyRoot
                      putStrLn ("Writing " ++ filename ++ " to " ++ outfile)
                      System.Directory.createDirectoryIfMissing True (snd $ splitPath outfile)
                      writeOMDocDTD dtduri omdocxml outfile >> return ()
                )
                (Map.keys lenv)
              return ()
          else
            do
              dtduri <- envDTDURI
              omdoc <-
                libEnvLibNameIdNameMappingToOMDoc
                  (emptyGlobalOptions { hetsOpts = hco })
                  lenv
                  ln
                  (createLibName ln)
                  uniqueNamesXml
                  fullNamesXml
              omdocxml <- return $ (OMDocXML.toXml omdoc) HXT.emptyRoot
              writeOMDocDTD dtduri omdocxml fp >> return ()
    in
        outputio

-- | creates a xml structure describing a Hets-presentation for a symbol 
makePresentationForOM::XmlName->String->OMDoc.Presentation
makePresentationForOM xname presstring =
  OMDoc.mkPresentation xname [OMDoc.mkUse "Hets" presstring]  

{-
 assuming unique names in a list of 'IdNameMapping'S each id (String) is
 converted to an xml:id-conform string by replacing invalid characters
-}
{- |
  create xml ids from unique names
-}
createXmlNameMapping::[Hets.IdNameMapping]->[Hets.IdNameMapping]
createXmlNameMapping =
  map
    (\(
        libName
      , nodeName
      , uniqueNodeName
      , nodeNum
      , idNameSortSet
      , idNamePredSet
      , idNameOpSet
      , idNameSensSet
      , idNameConsSet
      ) ->
      (
          libName
        , nodeName
        , adjustStringForXmlName uniqueNodeName
        , nodeNum
        , Set.map (\(id', uN) -> (id', adjustStringForXmlName uN)) idNameSortSet
        , Set.map (\(a, uN) -> (a, adjustStringForXmlName uN)) idNamePredSet
        , Set.map (\(a, uN) -> (a, adjustStringForXmlName uN)) idNameOpSet
        , Set.map (\(a, uN) -> (a, adjustStringForXmlName uN)) idNameSensSet
        , Set.map (\(a, uN) -> (a, adjustStringForXmlName uN)) idNameConsSet
      )
    )

createOMDefLink::
  Static.DevGraph.LibEnv
  ->Hets.LIB_NAME
  ->Graph.LEdge Static.DevGraph.DGLinkLab
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->OMDoc.Imports
createOMDefLink lenv ln (from, to, ll) uniqueNames names =
  let
    dg = devGraph $ Map.findWithDefault (error "!") ln lenv
    fromnode = Data.Maybe.fromMaybe (error "!") $ Graph.lab dg from
    fromname =
      case
        find
          (\ inm ->
            Hets.inmGetLibName inm == ln && Hets.inmGetNodeNum inm == from
          )
          names
      of
        Nothing -> error "No such node in names!"
        (Just inm) -> Hets.inmGetNodeId inm
    liburl =
      if isDGRef fromnode
        then
          asOMDocFile $ unwrapLinkSource $ dgn_libname fromnode
        else
          ""
    linktype =
      case dgl_type ll of
        (LocalDef {}) ->
            OMDoc.ITLocal
        _ -> OMDoc.ITGlobal
    mommorph = createOMMorphism lenv ln (from, to, ll) uniqueNames names
    fromuri = case URI.parseURIReference (liburl ++ "#" ++ fromname) of
      Nothing -> error "!"
      (Just u) -> u
  in
    OMDoc.Imports fromuri [] mommorph Nothing linktype

createXmlThmLinkOM::
  Static.DevGraph.LibEnv
  ->Hets.LIB_NAME
  ->Graph.LEdge Static.DevGraph.DGLinkLab
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->OMDoc.Inclusion
createXmlThmLinkOM lenv ln (edge@(from, to, ll)) uniqueNames names =
  let
    dg = devGraph $ Map.findWithDefault (error "!") ln lenv
    fromnode = Data.Maybe.fromMaybe (error "!") $ Graph.lab dg from
    tonode = Data.Maybe.fromMaybe (error "!") $ Graph.lab dg to
    fromname =
      case
        find
          (\inm ->
            Hets.inmGetLibName inm == ln && Hets.inmGetNodeNum inm == from
          )
          names
      of
        Nothing -> error "No such node in names!"
        (Just inm) -> Hets.inmGetNodeId inm
    toname =
      case
        find
          (\inm ->
            Hets.inmGetLibName inm == ln && Hets.inmGetNodeNum inm == to
          )
          names
      of
        Nothing -> error "No such node in names!"
        (Just inm) -> Hets.inmGetNodeId inm
    liburl =
      if isDGRef fromnode
        then
          asOMDocFile $ unwrapLinkSource $ dgn_libname fromnode
        else
          ""
    toliburl =
      if isDGRef tonode
        then
          asOMDocFile $ unwrapLinkSource $ dgn_libname tonode
        else
          ""
    isaxinc =
      case dgl_type ll of
        (Static.DevGraph.GlobalThm {}) -> False
        (Static.DevGraph.LocalThm {}) -> True
        _ -> error "corrupt data"
    cons =
      case dgl_type ll of
        (Static.DevGraph.GlobalThm _ c _) -> consConv c
        (Static.DevGraph.LocalThm _ c _) -> consConv c
        _ -> error "corrupt data"
    touri = case URI.parseURIReference (toliburl ++ "#" ++ toname) of
      Nothing -> error "!"
      (Just u) -> u
    fromuri = case URI.parseURIReference (liburl ++ "#" ++ fromname) of
      Nothing -> error "!"
      (Just u) -> u
    iid =
      (if isaxinc then "ai" else "ti")
        ++ "." ++ toname ++ "." ++ fromname
    mommorph = createOMMorphism lenv ln edge uniqueNames names
  in
    if isaxinc
      then
        OMDoc.AxiomInclusion fromuri touri mommorph (Just iid) cons
      else
        OMDoc.TheoryInclusion fromuri touri mommorph (Just iid) cons
  where
  consConv::Static.DevGraph.Conservativity->OMDoc.Conservativity
  consConv Static.DevGraph.None = OMDoc.CNone
  consConv Static.DevGraph.Mono = OMDoc.CMonomorphism
  consConv Static.DevGraph.Cons = OMDoc.CConservative
  consConv Static.DevGraph.Def = OMDoc.CDefinitional

{- |
  create a xml-representation of a (CASL-)morphism
-}
createOMMorphism::
  Static.DevGraph.LibEnv
  ->Hets.LIB_NAME
  ->Graph.LEdge Static.DevGraph.DGLinkLab
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->Maybe OMDoc.Morphism
createOMMorphism
  _
  ln
  (from, to, ll)
  {-uniqueNames-}_
  names
  =
  let
    caslmorph = Hets.getCASLMorphLL ll
    fromIdNameMapping =
      Data.Maybe.fromMaybe
        (error "!")
        $
        Hets.inmFindLNNN (ln, from) names
    toIdNameMapping =
      Data.Maybe.fromMaybe
        (error "!")
        $
        Hets.inmFindLNNN (ln, to) names
    mappedsorts =
      Map.foldWithKey
        (\origsort newsort ms ->
          let
            oname =
              case
                Set.toList
                  $
                  Set.filter
                    (\(oid', _) -> oid' == origsort)
                    (Hets.inmGetIdNameSortSet fromIdNameMapping)
              of
               [] -> error "Sort not in From-Set!" 
               s:_ -> snd s
            nname =
              case
                Set.toList 
                  $
                  Set.filter
                    (\(nid', _) -> nid' == newsort)
                    (Hets.inmGetIdNameSortSet toIdNameMapping)
              of
               [] -> error "Sort not in To-Set!" 
               s:_ -> snd s
            oorigin =
              case
                Hets.getNameOrigin names ln from oname
              of
                [] -> error "!"
                o:[] -> o
                o:_ ->
                  Debug.Trace.trace
                    ("more than one origin for Sort \""
                      ++ show oname ++ "\"...")
                    o
            norigin =
              case
                Hets.getNameOrigin names ln to nname
              of
                [] -> error "!"
                n:[] -> n
                n:_ ->
                  Debug.Trace.trace
                    ("more than one origin for Sort \""
                      ++ show nname ++ "\"...")
                    n
         in
          ms ++ [ ((oname, oorigin), (nname, norigin)) ]
        )
        []
        (Morphism.sort_map caslmorph)
    mappedpreds =
      Map.foldWithKey
        (\(origpred, _) newpred mp ->
          let
            oname =
              case
                Set.toList
                  $
                  Set.filter
                    (\((oid', _), _) -> oid' == origpred)
                    (Hets.inmGetIdNamePredSet fromIdNameMapping)
              of
               [] -> error ("Pred not in From-Set! " ++ show origpred ++ " not in " ++ show (Hets.inmGetIdNamePredSet fromIdNameMapping))
               s:_ -> snd s
            nname =
              case
                Set.toList 
                  $
                  Set.filter
                    (\((nid', _), _) -> nid' == newpred)
                    (Hets.inmGetIdNamePredSet toIdNameMapping)
              of
               [] -> error "Pred not in To-Set!" 
               s:_ -> snd s
            oorigin =
              case
                Hets.getNameOrigin names ln from oname
              of
                [] -> error "!"
                o:[] -> o
                o:_ ->
                  Debug.Trace.trace
                    ("more than one origin for Pred \""
                      ++ show oname ++ "\"...")
                    o
            norigin =
              case
                Hets.getNameOrigin names ln to nname
              of
                [] -> error "!"
                n:[] -> n
                n:_ ->
                  Debug.Trace.trace
                    ("more than one origin for Pred \""
                      ++ show nname ++ "\"...")
                    n
         in
          mp ++ [ ((oname, oorigin), (nname, norigin)) ]
        )
        []
        (Morphism.pred_map caslmorph)
    mappedops =
      Map.foldWithKey
        (\(origop, _) (newop, _) mo ->
          let
            oname =
              case
                Set.toList
                  $
                  Set.filter
                    (\((oid', _), _) -> oid' == origop)
                    (Hets.inmGetIdNameOpSet fromIdNameMapping)
              of
               [] -> error "Op not in From-Set!" 
               s:_ -> snd s
            nname =
              case
                Set.toList 
                  $
                  Set.filter
                    (\((nid', _), _) -> nid' == newop)
                    (Hets.inmGetIdNameOpSet toIdNameMapping)
              of
               [] -> error "Op not in To-Set!" 
               s:_ -> snd s
            oorigin =
              case
                Hets.getNameOrigin names ln from oname
              of
                [] -> error "!"
                o:[] -> o
                o:_ ->
                  Debug.Trace.trace
                    ("more than one origin for Op \""
                      ++ show oname ++ "\"...")
                    o
            norigin =
              case
                Hets.getNameOrigin names ln to nname
              of
                [] -> error "!"
                n:[] -> n
                n:_ ->
                  Debug.Trace.trace
                    ("more than one origin for Op \""
                      ++ show nname ++ "\"...")
                    n
         in
          mo ++ [ ((oname, oorigin), (nname, norigin)) ]
        )
        []
        (Morphism.fun_map caslmorph)
    allmapped = mappedsorts ++ mappedpreds ++ mappedops
    hidden =
      case dgl_type ll of
        (HidingDef {}) ->
          mkHiding fromIdNameMapping toIdNameMapping allmapped
        (HidingThm {}) ->
          mkHiding fromIdNameMapping toIdNameMapping allmapped
        _ -> []
    reqs =
      foldl
        (\r ((f,fo), (t,to')) ->
          r
          ++
          [
            (
                OMDoc.MTextOM $ OMDoc.mkOMOBJ $ OMDoc.mkOMS (Hets.inmGetNodeId fo) f
              , OMDoc.MTextOM $ OMDoc.mkOMOBJ $ OMDoc.mkOMS (Hets.inmGetNodeId to') t
            )
          ]
        )
        []
        allmapped
  in
    if Hets.isEmptyMorphism caslmorph && null hidden
      then
        Nothing
      else
        Just $ OMDoc.Morphism hidden reqs
  where
  mkHiding::Hets.IdNameMapping->Hets.IdNameMapping->[((String,a),b)]->[String]
  mkHiding fromIdNameMapping toIdNameMapping mappedIds =
    let
      idsInFrom = Hets.inmGetIdNameAllSet fromIdNameMapping
      idsInTo = Hets.inmGetIdNameAllSet toIdNameMapping
    in
      Set.fold
        (\(_, fname) h ->
          case
            find
              (\( (fname', _)  , _ ) -> fname == fname')
              mappedIds
          of
            Nothing ->
              if
                Set.null
                  $
                  Set.filter
                    (\(_, tname) -> tname == fname)
                    idsInTo
                then
                  h ++ [fname]
                else
                  h
            _ -> h
        )
        []
        idsInFrom

{- |
  filter definitional links (LocalDef, GlobalDef, HidingDef, FreeDef, CofreeDef)
-}
filterDefLinks::
  [Graph.LEdge Static.DevGraph.DGLinkLab]
  ->[Graph.LEdge Static.DevGraph.DGLinkLab]
filterDefLinks =
  filter
    (\(_, _, ll) ->
      case dgl_type ll of
        (LocalDef {}) -> True
        (GlobalDef {}) -> True
        (HidingDef {}) -> True
        (FreeDef {}) -> True
        (CofreeDef {}) -> True
        _ -> False
    )

{- |
  filter theorem links (LocalThm, GlobalThm, HidingThm)
-}
filterThmLinks::
  [Graph.LEdge Static.DevGraph.DGLinkLab]
  ->[Graph.LEdge Static.DevGraph.DGLinkLab]
filterThmLinks =
  filter
    (\(_, _, ll) ->
      case dgl_type ll of
        (LocalThm {}) -> True
        (GlobalThm {}) -> True
        (HidingThm {}) -> True
        _ -> False
    )

{- |
  filter sort generating constructors (from a list of sort constructors) 
-}
filterSORTConstructors::Set.Set (OpType, String)->SORT->Set.Set (OpType, String)
filterSORTConstructors
  conset
  s
  =
  Set.filter
    (\(ot, _) -> opRes ot == s )
    conset

createConstructorsOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->Set.Set (OpType, String)
  ->[OMDoc.Constructor]
createConstructorsOM
  ln
  nn
  uniqueNames
  fullNames
  conset
  =
    Set.fold
      (\c cs ->
        cs
        ++
        [
          createConstructorOM 
            ln
            nn
            uniqueNames
            fullNames
            c
        ]
      )
      []
      conset

createConstructorOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(OpType, String)
  ->OMDoc.Constructor
createConstructorOM
  ln
  nn
  uniqueNames
  fullNames
  (ot, oxmlid)
  =
  OMDoc.mkConstructor
    oxmlid
    (
      foldl
        (\args arg ->
          args
          ++
          [
            OMDoc.mkType
              Nothing
              (
              OMDoc.OMOMOBJ
                $
                OMDoc.mkOMOBJ
                  $
                  createSymbolForSortOM
                    ln
                    nn
                    uniqueNames
                    fullNames
                    arg
              )
          ]
        )
        []
        (opArgs ot)
    )
    
{- | 
  check if a relation contains information about a certain sort
-}
emptyRelForSort::Rel.Rel SORT->SORT->Bool
emptyRelForSort rel s =
  null $ filter (\(s', _) -> s' == s) $ Rel.toList rel

createADTFor::
  Rel.Rel SORT
  ->SORT
  ->Hets.IdNameMapping
  ->[OMDoc.Constructor]
  ->OMDoc.ADT
createADTFor rel s idNameMapping constructors =
  let
    insorts =
      foldl
        (\is (s'', s') ->
          if s'' == s
            then
              is
              ++
              [
                OMDoc.mkInsort (OMDoc.mkSymbolRef (getNameE s'))
              ]
            else
              is
        )
        []
        (Rel.toList rel)
  in
    OMDoc.mkADT
      $
      [
        OMDoc.mkSortDef
          (getNameE s)
          constructors
          insorts
      ]
  where
  lookupName::Set.Set (Id.Id, String) -> Id.Id -> Maybe String
  lookupName ss sid =
    case
      find
        (\(sid', _) -> sid' == sid)
        (Set.toList ss)
    of
      Nothing -> Nothing
      (Just x) -> Just (snd x)
  getNameE::Id.Id->String
  getNameE sid =
    Data.Maybe.fromMaybe
      (error "!")
      $
      lookupName (Hets.inmGetIdNameSortSet idNameMapping) sid

libEnvLibNameIdNameMappingToOMDoc::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->OMDoc.XmlId
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->IO OMDoc.OMDoc
libEnvLibNameIdNameMappingToOMDoc
  go
  lenv
  ln
  omdocId
  uniqueNames
  fullNames
  =
    let
      dg = devGraph $ Map.findWithDefault (error "!") ln lenv
      thmLinksToRefs =
        filter
          (\(_, to, _) ->
            case Graph.lab dg to of
              Nothing -> False
              (Just n) -> isDGRef n
          )
          (filterThmLinks $ Graph.labEdges dg)
      thmLinksToRefsOM =
        map
          (\edge ->
            createXmlThmLinkOM
              lenv
              ln
              edge
              uniqueNames
              fullNames
          )
          thmLinksToRefs
      initialOMDoc =
        OMDoc.OMDoc omdocId [] thmLinksToRefsOM  
    in
      foldl
        (\xio (nn, node) ->
          let
            dgnodename = dgn_name node
            caslsign = (\(Just a) -> a) $ Hets.getCASLSign (dgn_sign node)
            idnamemapping =
              case
                find
                  (\inm ->
                    (Hets.inmGetLibName inm) == ln
                    && (Hets.inmGetNodeName inm) == dgnodename
                    && (Hets.inmGetNodeNum inm) == nn
                  )
                  fullNames
              of
                Nothing -> error "No such name..."
                (Just a) -> a
            uniqueidnamemapping =
              case
                find
                  (\inm ->
                    (Hets.inmGetLibName inm) == ln
                    && (Hets.inmGetNodeName inm) == dgnodename
                    && (Hets.inmGetNodeNum inm) == nn
                  )
                  uniqueNames
              of
                Nothing -> error "No such name..."
                (Just a) -> a
            theoryXmlId = (Hets.inmGetNodeId idnamemapping)
            theoryPresentation =
              makePresentationForOM
                theoryXmlId
                (Hets.idToString $ Hets.nodeNameToId dgnodename)
            theoryDefLinks =
              map
                (\edge ->
                  createOMDefLink
                    lenv
                    ln
                    edge
                    uniqueNames
                    fullNames
                )
                (filterDefLinks (Graph.inn dg nn))
            (theoryADTs, theorySorts, theoryPresentations) =
              Set.fold
               (\s (tadts, tsorts, tpres) ->
                let
                  consremap =
                    Set.map
                      (\( (_, _, ot), uname ) -> (ot, uname))
                      (Hets.inmGetIdNameConsSet uniqueidnamemapping)
                  sortcons = filterSORTConstructors consremap s
                  constructors = 
                    createConstructorsOM
                      ln
                      nn
                      uniqueNames
                      fullNames
                      sortcons
                in
                  case
                    find
                      (\(uid, _) -> uid == s)
                      (Set.toList (Hets.inmGetIdNameAllSet uniqueidnamemapping))
                  of
                    Nothing ->
                      if (Set.size sortcons) > 0
                        then
                          let
                            newadt =
                              createADTFor
                                Rel.empty
                                s
                                idnamemapping
                                constructors
                          in
                            (tadts ++ [newadt], tsorts, tpres)
                        else
                          (tadts, tsorts, tpres)
                    (Just (uid, uname)) ->
                      let
                        newsort = sortToXmlOM (XmlNamed s uname)
                        newadt =
                          createADTFor
                            (sortRel caslsign)
                            uid
                            idnamemapping
                            constructors
                        newpre =
                          makePresentationForOM
                            uname
                            (Hets.idToString s)
                        newsorts = tsorts ++ [newsort]
                        newpres = tpres ++ [newpre]
                        newadts =
                          if (not $ emptyRelForSort (sortRel caslsign) uid)
                            || ( (Set.size sortcons) > 0 )
                            then
                              tadts++[newadt]
                            else
                              tadts
                      in
                        (newadts, newsorts, newpres)
               )
               ([],[],[])
               (sortSet caslsign)
            (theoryPreds, pPres) =
              Map.foldWithKey
                (\pid pts (tPr, pP) ->
                  Set.fold
                    (\pt (tPr', pP') ->
                      case 
                        find
                          (\( (uid, upt), _) -> uid == pid && upt == pt)
                          (Set.toList (Hets.inmGetIdNamePredSet uniqueidnamemapping))
                      of
                        Nothing -> (tPr', pP')
                        (Just (_, uname )) ->
                          let
                            newpred = 
                              predicationToXmlOM
                                ln
                                nn
                                idnamemapping
                                uniqueNames
                                fullNames
                                (pid, pt)
                            newpres =
                              makePresentationForOM
                                uname
                                (Hets.idToString pid)
                          in
                            (tPr' ++ [newpred], pP' ++ [newpres])
                    )
                    (tPr, pP)
                    pts
                )
                ([],[])
                (predMap caslsign)
            (theoryOps, oPres) =
              Map.foldWithKey
                (\oid ots (tOp, oP) ->
                  Set.fold
                    (\ot (tOp', oP') ->
                      case 
                        find
                          (\( (uid, uot), _) -> uid == oid && uot == ot)
                          (Set.toList (Hets.inmGetIdNameOpSet uniqueidnamemapping))
                      of
                        Nothing -> (tOp', oP')
                        (Just (_, uname )) ->
                          let
                            newop =
                              operatorToXmlOM
                                ln
                                nn
                                idnamemapping
                                uniqueNames
                                fullNames
                                (oid, ot)
                            newpres =
                              makePresentationForOM
                                uname
                                (Hets.idToString oid)
                          in
                            (tOp' ++ [newop], oP' ++ [newpres])
                    )
                    (tOp, oP)
                    ots
                )
                ([],[])
                (opMap caslsign)
            theoryThmLinks =
              map
                (\edge ->
                  createXmlThmLinkOM
                    lenv
                    ln
                    edge
                    uniqueNames
                    fullNames
                )
                (filterThmLinks $ Graph.inn dg nn)
          in
            do
              omdoc <- xio
              (omAxs, omDefs, omPres) <-
                wrapFormulasCMPIOOM
                  go
                  lenv
                  ln
                  nn
                  idnamemapping
                  uniqueNames
                  fullNames
                  (Hets.getNodeSentences node)
              if isDGRef node
                then
                  return omdoc
                else
                  let
                    newtheory =
                      OMDoc.Theory
                        theoryXmlId
                        (
                          (map OMDoc.mkCSy theorySorts)
                          ++
                          (map OMDoc.mkCSy theoryOps)
                          ++
                          (map OMDoc.mkCSy theoryPreds)
                          ++
                          (map OMDoc.mkCAd theoryADTs)
                          ++
                          (map OMDoc.mkCAx omAxs)
                          ++
                          (map OMDoc.mkCDe omDefs)
                          ++
                          (map OMDoc.mkCIm theoryDefLinks)
                        )
                        (
                          [theoryPresentation]
                          ++
                          theoryPresentations
                          ++
                          omPres
                          ++
                          pPres
                          ++
                          oPres
                        )
                  in
                    return
                      $
                      (
                        OMDoc.addInclusions
                          (
                            OMDoc.addTheories
                              omdoc
                              [newtheory]
                          )
                          theoryThmLinks
                      )
        )
        (return initialOMDoc)
        (Graph.labNodes dg)

{- |
  alias for inmGetNodeId
-}
getNodeNameForXml::Hets.IdNameMapping->String
getNodeNameForXml = Hets.inmGetNodeId
  
predicationToXmlOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(Id.Id, PredType)
  ->OMDoc.Symbol
predicationToXmlOM 
  ln
  nn
  currentmapping
  {-uniqueNames-}_
  {-fullNames-}_
  (pid, pt)
  =
    let
      pidxmlid =
        Data.Maybe.fromMaybe
          (error ("No name for \"" ++ show pid ++ "\""))
          (Hets.getNameForPred [currentmapping] (pid, pt))
      argnames =
        map
          (\args ->
            Data.Maybe.fromMaybe
              (error ("No name for \"" ++ show args ++ "\""))
              (Hets.getNameForSort [currentmapping] args)
          )
          (predArgs pt)
      argorigins =
        map
          (\argxmlid ->
            case Hets.getNameOrigin [currentmapping] ln nn argxmlid of
              [] -> error ("No origin for Sort " ++ show argxmlid)
              [o] -> getNodeNameForXml o
              (o:_) ->
                Debug.Trace.trace
                  ("More than one origin for \"" ++ show argxmlid ++ "\"")
                  $ 
                  getNodeNameForXml o 
          )
          argnames
      argzip =
        zip
          argnames
          argorigins
      typeobj =
        OMDoc.mkType
          (OMDoc.mkOMDocRef "casl")
          $
          OMDoc.OMOMOBJ
            $
            OMDoc.mkOMOBJ
              $
              OMDoc.mkOMA
                (
                  [
                    OMDoc.mkOMSE "casl" "predication"
                  ]
                  ++
                  (
                    map
                      (\(an, ao) ->
                        OMDoc.mkOMSE ao an
                      )
                      argzip
                  )
                )
    in
      OMDoc.mkSymbolE
        pidxmlid
        OMDoc.SRObject
        (Just typeobj)

operatorToXmlOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(Id.Id, OpType)
  ->OMDoc.Symbol
operatorToXmlOM
  ln
  nn
  currentmapping
  {-uniqueNames-}_
  {-fullNames-}_
  (oid, ot)
  =
    let
      oidxmlid =
        Data.Maybe.fromMaybe
          (error ("No name for \"" ++ show oid ++ "\""))
          (Hets.getNameForOp [currentmapping] (oid, ot))
      argnames =
        map
          (\args ->
            Data.Maybe.fromMaybe
              (error ("No name for \"" ++ show args ++ "\""))
              (Hets.getNameForSort [currentmapping] args)
          )
          (opArgs ot)
      argorigins =
        map
          (\argxmlid ->
            case Hets.getNameOrigin [currentmapping] ln nn argxmlid of
              [] -> error ("No origin for Sort " ++ show argxmlid)
              [o] -> getNodeNameForXml o
              (o:_) ->
                Debug.Trace.trace
                  ("More than one origin for \"" ++ show argxmlid ++ "\"")
                  $ 
                  getNodeNameForXml o
          )
          argnames
      argzip =
        zip
          argnames
          argorigins
      resxmlid =
        Data.Maybe.fromMaybe
          (error ("No name for \"" ++ show (opRes ot) ++ "\""))
          (Hets.getNameForSort [currentmapping] (opRes ot))
      resorigin =
        case Hets.getNameOrigin [currentmapping] ln nn resxmlid of
          [] -> error ("No origin for Sort " ++ show resxmlid)
          [o] -> getNodeNameForXml o
          (o:_) ->
            Debug.Trace.trace
              ("More than one origin for \"" ++ show resxmlid ++ "\"")
              $ 
              getNodeNameForXml o
      typeobj =
        OMDoc.mkType
          (OMDoc.mkOMDocRef "casl")
          $
          OMDoc.OMOMOBJ
            $
            OMDoc.mkOMOBJ
              $
              OMDoc.mkOMA
                (
                  [
                    OMDoc.mkOMSE
                      "casl"
                      (if (opKind ot) == Total
                        then
                          "function"
                        else
                          "partial-function"
                      )
                  ]
                  ++
                  (
                    map
                      (\(an, ao) ->
                        OMDoc.mkOMSE ao an
                      )
                      argzip
                  )
                  ++
                  [
                    OMDoc.mkOMSE
                      resorigin
                      resxmlid
                  ]
                )
    in
      OMDoc.mkSymbolE
        oidxmlid
        OMDoc.SRObject
        (Just typeobj)

sortToXmlOM::XmlNamed SORT->OMDoc.Symbol
sortToXmlOM xnSort =
  OMDoc.mkSymbol (xnName xnSort) OMDoc.SRSort

-- | theory name, theory source (local)
data TheoryImport = TI (String, String)

instance Show TheoryImport where
  show (TI (tn, ts)) = ("Import of \"" ++ tn ++ "\" from \"" ++ ts ++ "\".")

-- | source name, source (absolute)
--data Source a = S { nameAndURI::(String, String), sContent::a } 
data Source a = S (String, String) a

instance Show (Source a) where
  show (S (sn, sf) _) = ("Source \"" ++ sn ++ "\" File : \"" ++ sf ++ "\".");

createLibName::ASL.LIB_NAME->String
createLibName libname = splitFile . fst . splitPath $ unwrapLinkSource libname

unwrapLinkSource::ASL.LIB_NAME->String
unwrapLinkSource
  (ASL.Lib_id lid) = unwrapLID lid
unwrapLinkSource
  (ASL.Lib_version lid _) = unwrapLID lid

unwrapLID::ASL.LIB_ID->String
unwrapLID (ASL.Indirect_link url _) = url
unwrapLID (ASL.Direct_link path _) = path

-- | separates the path and filename part from a filename, first element is the
-- name, second the path (without last delimiter)
splitPath::String->(String, String)
splitPath f = case explode "/" f of
  [x] -> (x,"")
  l -> (last l, joinWith '/' $ init l)

-- | returns the name of a file without extension
splitFile::String->String
splitFile file =
  let
    filenameparts = explode "." file
  in
    case (length filenameparts) of
            1 -> file
            2 -> case head filenameparts of
                            "" -> "."++(last filenameparts)
                            fn -> fn
            _ -> implode "." $ init filenameparts 
        
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

fileSandbox::String->String->String
fileSandbox [] file = file
fileSandbox sb file =
  sb ++ "/" ++ case head file of
    '/' -> tail file
    _ -> file
                
posLines::[Id.Pos]->IO (Map.Map Id.Pos String)
posLines posl =
  do
    (psm, _) <- foldl (\iomaps pos@(Id.SourcePos name' line _) ->
      do
      (strmap, linemap) <- iomaps
      case Map.lookup name' linemap of
        (Just flines) ->
          return (Map.insert pos (headorempty (drop (line-1) flines)) strmap,
           linemap)
        Nothing ->
          do
            fe <- System.Directory.doesFileExist name'
            f <- if fe then readFile name' else (return "")
            flines <- return (lines f)
            return (Map.insert pos (headorempty (drop (line-1) flines)) strmap,
              Map.insert name' flines linemap)
        ) (return (Map.empty, Map.empty)) posl
    return psm

--data QUANTIFIER = Universal | Existential | Unique_existential
-- Quantifier as CASL Symbol
quantName :: QUANTIFIER->String
quantName Universal = caslSymbolQuantUniversalS
quantName Existential = caslSymbolQuantExistentialS
quantName Unique_existential = caslSymbolQuantUnique_existentialS

-- check if a type t1 is a subtype of a type t2
isTypeOrSubType::Rel.Rel SORT->SORT->SORT->Bool
isTypeOrSubType sortrel givensort neededsort =
  (givensort == neededsort)
    || (Rel.path givensort neededsort sortrel)

-- check for type compatibility
-- a type t1 is compatible to a type t2 if
-- a) t1 == t2 or b) t1 is a subtype of t2
compatibleTypes::Rel.Rel SORT->[SORT]->[SORT]->Bool
compatibleTypes _ [] [] = True
compatibleTypes _ [] _ = False
compatibleTypes _ _ [] = False
compatibleTypes sortrel (s1:r1) (s2:r2) =
  (isTypeOrSubType sortrel s1 s2) && (compatibleTypes sortrel r1 r2)

-- check type compatibility for two predicates
compatiblePredicate::Rel.Rel SORT->PredType->PredType->Bool
compatiblePredicate sortrel pt1 pt2 =
  compatibleTypes sortrel (predArgs pt1) (predArgs pt2)

-- check type compatibility for two operators
compatibleOperator::Rel.Rel SORT->OpType->OpType->Bool
compatibleOperator sortrel ot1 ot2 =
--  (\x -> Debug.Trace.trace ("Comparing " ++ show ot1 ++ " to " ++ show ot2 ++ " -> " ++ show x) x)
--  $
  (isTypeOrSubType sortrel (opRes ot1) (opRes ot2))
  &&
  (compatibleTypes sortrel (opArgs ot1) (opArgs ot2))

-- first newline needs pulling up because we have a list of lists...
processVarDeclOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->[VAR_DECL]
  ->OMDoc.OMBindingVariables
processVarDeclOM ln nn uN fN vdl =
  OMDoc.mkOMBVAR
    (processVarDecls vdl)
  
  where
  processVarDecls::
    [VAR_DECL]
    ->[OMDoc.OMVariable]
  processVarDecls [] = []
  processVarDecls ( (Var_decl vl s _):vdl' ) =
    -- <ombattr><omatp><oms>+</omatp><omv></ombattr>
    (
      foldl
        (\decls vd ->
          decls
          ++
          [ OMDoc.toVariable $ createTypedVarOM ln nn uN fN s (show vd) ]
        )
        []
        vl
    )
    ++ (processVarDecls vdl')

createATPOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->SORT
  ->OMDoc.OMAttributionPart
createATPOM ln nn uniqueNames fullNames sort =
  OMDoc.mkOMATP
    [
      (
          OMDoc.mkOMS caslS typeS
        , createSymbolForSortOM ln nn uniqueNames fullNames sort
      )
    ]

createTypedVarOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->SORT
  ->String
  ->OMDoc.OMAttribution
createTypedVarOM ln nn uniqueNames fullNames sort varname =
  OMDoc.mkOMATTR
    (createATPOM ln nn uniqueNames fullNames sort)
    (OMDoc.mkOMSimpleVar varname)


findSortOriginCL::
  Hets.LIB_NAME
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->SORT
  ->Maybe (XmlName, Hets.IdNameMapping)
findSortOriginCL
  ln
  uniqueNames
  fullNames
  s
  =
    Hets.findOriginInCurrentLib
      ln
      uniqueNames
      fullNames
      (\cm ->
        case
          find
            (\( (uid), _ ) -> uid == s)
            (Set.toList (Hets.inmGetIdNameSortSet cm))
        of
          Nothing -> Nothing
          Just (_, uname) -> (Just (uname, cm))
      )

createSymbolForSortOM::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->SORT
  ->OMDoc.OMSymbol
createSymbolForSortOM
  ln
  _ -- nn
  uniqueNames
  fullNames
  s
  =
    let
      (sortxmlid, sortorigin) =
        case
          findSortOriginCL
            ln
            uniqueNames
            fullNames
            s
        of
          Nothing -> error "!"
          (Just (sx, so)) ->
            (
                sx
              , getNodeNameForXml so
            )
    in
      OMDoc.mkOMS sortorigin sortxmlid

findPredicateOriginCL::
  Hets.LIB_NAME
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->Rel.Rel SORT
  ->PRED_SYMB
  ->Maybe (XmlName, Hets.IdNameMapping)
findPredicateOriginCL
  ln
  uniqueNames
  fullNames
  _
  (Pred_name pr)
  =
    Hets.findOriginInCurrentLib
      ln
      uniqueNames
      fullNames
      (\cm ->
        case
          find
            (\( (uid, _), _ ) -> uid == pr)
            (Set.toList (Hets.inmGetIdNamePredSet cm))
        of
          Nothing -> Nothing
          Just (_, uname) -> (Just (uname, cm))
      )
findPredicateOriginCL
  ln
  uniqueNames
  fullNames
  sortrel
  (Qual_pred_name pr pt _)
  =
    Hets.findOriginInCurrentLib
      ln
      uniqueNames
      fullNames
      (\cm ->
        case 
          preferEqualFindCompatible
            (Set.toList (Hets.inmGetIdNamePredSet cm))
            (\( (uid, upt), _) ->
              uid == pr && upt == (Hets.cv_Pred_typeToPredType pt)
            )
            (\( (uid, upt), _) ->
              uid == pr &&
                compatiblePredicate
                  sortrel
                  upt
                  (Hets.cv_Pred_typeToPredType pt)
            )
        of
          Nothing -> Nothing
          (Just (_, uname)) -> Just (uname, cm)
      )

-- | create an xml-representation for a predication
createSymbolForPredicationOM::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  -> PRED_SYMB -- ^ the predication to process
  ->OMDoc.OMSymbol
createSymbolForPredicationOM _ lenv ln nn uniqueNames fullNames ps =
    let
      currentNode =
        fromMaybe
          (error "!!!")
          $
          (flip Graph.lab)
            nn
            $
            devGraph
              $
              Map.findWithDefault
                (error "!!")
                ln
                lenv
      currentSign = Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign currentNode)
      currentRel = sortRel currentSign
      (predxmlid, predorigin) =
        case
          findPredicateOriginCL
            ln
            uniqueNames
            fullNames
            currentRel
            ps
        of
          Nothing ->
            error "!"   
          (Just (predx, predo)) ->
            (   
                predx
              , getNodeNameForXml predo
            )
    in
      OMDoc.mkOMS predorigin predxmlid

findOperatorOriginCL::
  Hets.LIB_NAME
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->Rel.Rel SORT
  ->OP_SYMB
  ->Maybe (XmlName, Hets.IdNameMapping)
findOperatorOriginCL
  ln
  uniqueNames
  fullNames
  _
  (Op_name op)
  =
    Hets.findOriginInCurrentLib
      ln
      uniqueNames
      fullNames
      (\cm ->
        case
          find
            (\( (uid, _), _ ) -> uid == op)
              (
              (Set.toList (Hets.inmGetIdNameOpSet cm))
              ++
              (Set.toList (Hets.inmGetIdNameConsSetLikeOps cm))
              )
        of
          Nothing -> Nothing
          Just (_, uname) -> (Just (uname, cm))
      )
findOperatorOriginCL
  ln
  uniqueNames
  fullNames
  sortrel
  (Qual_op_name op ot _)
  =
    Hets.findOriginInCurrentLib
      ln
      uniqueNames
      fullNames
      (\cm ->
        case 
          preferEqualFindCompatible
            (
              (Set.toList (Hets.inmGetIdNameOpSet cm))
              ++
              (Set.toList (Hets.inmGetIdNameConsSetLikeOps cm))
            )
            (\( (uid, uot), _) ->
              uid == op && uot == (Hets.cv_Op_typeToOpType ot)
            )
            (\( (uid, uot), _) ->
              uid == op
              && compatibleOperator sortrel uot (Hets.cv_Op_typeToOpType ot)
            )
        of
          Nothing -> Nothing
          (Just (_, uname)) -> Just (uname, cm)
      )

-- | create a xml-representation of an operator
processOperatorOM::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->OP_SYMB -- ^ the operator to process
  ->OMDoc.OMSymbol
      -- ^ the xml-representation of the operator
processOperatorOM _ lenv ln nn uniqueNames fullNames
    os =
    let
      currentNode =
        fromMaybe
          (error "!!!")
          $
          (flip Graph.lab)
            nn
            $
            devGraph
              $
              Map.findWithDefault
                (error "!!")
                ln
                lenv
      currentSign =
        Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign currentNode)
      currentRel = sortRel currentSign
      (opxmlid, oporigin) =
        case
          findOperatorOriginCL
            ln
            uniqueNames
            fullNames
            currentRel
            os
        of
          Nothing ->
            error "!"   
          (Just (opx, opo)) ->
            (   
                opx
              , getNodeNameForXml opo
            )

    in
      OMDoc.mkOMS oporigin opxmlid

preferEqualFindCompatible::[a]->(a->Bool)->(a->Bool)->Maybe a
preferEqualFindCompatible l isEqual isCompatible =
  case find isEqual l of
    Nothing ->
      find isCompatible l
    x -> x

-- | create a xml-representation from a term (in context of a theory)
processTermOM::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  -> TERM f -- ^ the term to process
  ->OMDoc.OMElement
-- Simple_id
processTermOM _ _ _ _ _ _
  (Simple_id id' ) =
  OMDoc.toElement
    $
    (OMDoc.mkOMSimpleVar (show id'))
-- Qual_var
processTermOM _ _ ln nn uniqueNames fullNames
  (Qual_var v s _) =
    OMDoc.toElement
      $
      (createTypedVarOM ln nn uniqueNames fullNames s (show v) )
-- Application
processTermOM go lenv ln nn uniqueNames fullNames
  (Application op termlist _) =
    let
      omterms = 
        foldl
          (\ts t ->
            ts ++
              [
                OMDoc.toElement
                  $
                  processTermOM go lenv ln nn uniqueNames fullNames t
              ]
          )
          []
          termlist
    in
      if null omterms
        then
          OMDoc.toElement
            $
            (processOperatorOM go lenv ln nn uniqueNames fullNames op)
        else
          OMDoc.toElement
            $
            OMDoc.mkOMA
              (
                [
                  OMDoc.toElement
                    $
                    processOperatorOM go lenv ln nn uniqueNames fullNames op
                ] ++ omterms
              )
-- Cast
processTermOM go lenv ln nn uniqueNames fullNames
  (Cast t s _) =
    processTermOM go lenv ln nn uniqueNames fullNames
      (Application
        (Op_name $ Hets.stringToId "PROJ")
        [t, (Simple_id $ Id.mkSimpleId (show s))]
        Id.nullRange
      )
-- Conditional
processTermOM go lenv ln nn uniqueNames fullNames
  (Conditional t1 f t2 _) =
    OMDoc.toElement
      $
      OMDoc.mkOMA
        [
            OMDoc.toElement $ OMDoc.mkOMS caslS "IfThenElse"
          , OMDoc.toElement $ processFormulaOM go lenv ln nn uniqueNames fullNames f
          , OMDoc.toElement $ processTermOM go lenv ln nn uniqueNames fullNames t1
          , OMDoc.toElement $ processTermOM go lenv ln nn uniqueNames fullNames t2
        ]
-- Sorted_term is to be ignored in OMDoc (but could be modelled...) (Sample/Simple.casl uses it...)
processTermOM go lenv ln nn uniqueNames fullNames
  (Sorted_term t _ _) =
    processTermOM go lenv ln nn uniqueNames fullNames t
-- Unsupported Terms...
processTermOM _ _ _ _ _ _ _ = error "Unsupported Term encountered..." 

processFormulaOM::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->FORMULA f 
  ->OMDoc.OMElement
-- Quantification
processFormulaOM go lenv ln nn uN fN
  (Quantification q vl f _) =
    OMDoc.mkOMBINDE
      (OMDoc.mkOMS caslS (quantName q))
      (processVarDeclOM ln nn uN fN vl)
      (processFormulaOM go lenv ln nn uN fN f)

-- Conjunction
processFormulaOM go lenv ln nn uN fN
  (Conjunction fl _) =
    OMDoc.mkOMAE
      (
        [ OMDoc.mkOMSE caslS caslConjunctionS ]
        ++
        (
          foldl
            (\fs f ->
              fs ++ [ processFormulaOM go lenv ln nn uN fN f ]
            )
            []
            fl
        )
      )

-- Disjunction
processFormulaOM go lenv ln nn uN fN
  (Disjunction fl _) =
    OMDoc.mkOMAE
      (
        [ OMDoc.mkOMSE caslS caslDisjunctionS ]
        ++
        (
          foldl
            (\fs f ->
              fs ++ [ processFormulaOM go lenv ln nn uN fN f ]
            )
            []
            fl
        )
      )
-- Implication
processFormulaOM go lenv ln nn uN fN
  (Implication f1 f2 b _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE caslS caslImplicationS
        , processFormulaOM go lenv ln nn uN fN f1
        , processFormulaOM go lenv ln nn uN fN f2
        , processFormulaOM go lenv ln nn uN fN 
            (if b then True_atom Id.nullRange else False_atom Id.nullRange)
      ]

-- Equivalence
processFormulaOM go lenv ln nn uN fN
  (Equivalence f1 f2 _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE caslS caslEquivalenceS
        , processFormulaOM go lenv ln nn uN fN f1
        , processFormulaOM go lenv ln nn uN fN f2
      ]
-- Negation
processFormulaOM go lenv ln nn uN fN
  (Negation f _) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE caslS caslNegationS
        , processFormulaOM go lenv ln nn uN fN f
      ]
-- Predication
processFormulaOM go lenv ln nn uN fN
  (Predication p tl _) =
    OMDoc.mkOMAE
      (
        [
            OMDoc.mkOMSE caslS caslPredicationS
          , OMDoc.toElement $ createSymbolForPredicationOM go lenv ln nn uN fN p
        ]
        ++
        (
          foldl
            (\ts t ->
              ts ++ [ processTermOM go lenv ln nn uN fN t ]
            )
            []
            tl
        )
      )
-- Definedness
processFormulaOM go lenv ln nn uN fN
  (Definedness t _ ) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE caslS caslDefinednessS
        , processTermOM go lenv ln nn uN fN t
      ]
-- Existl_equation
processFormulaOM go lenv ln nn uN fN
  (Existl_equation t1 t2 _) = 
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE caslS caslExistl_equationS
        , processTermOM go lenv ln nn uN fN t1
        , processTermOM go lenv ln nn uN fN t2
      ]
-- Strong_equation
processFormulaOM go lenv ln nn uN fN
  (Strong_equation t1 t2 _) = 
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE caslS caslStrong_equationS
        , processTermOM go lenv ln nn uN fN t1
        , processTermOM go lenv ln nn uN fN t2
      ]
-- Membership
processFormulaOM go lenv ln nn uN fN
  (Membership t s _) = 
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE caslS caslMembershipS
        , processTermOM go lenv ln nn uN fN t
        , OMDoc.toElement $ createSymbolForSortOM ln nn uN fN s
      ]
-- False_atom
processFormulaOM _ _ _ _ _ _
  (False_atom _) =
    OMDoc.mkOMSE caslS caslSymbolAtomFalseS
-- True_atom
processFormulaOM _ _ _ _ _ _
  (True_atom _) =
    OMDoc.mkOMSE caslS caslSymbolAtomTrueS
-- Sort_gen_ax
processFormulaOM go lenv ln nn uN fN
  (Sort_gen_ax constraints freetype) =
    OMDoc.mkOMAE
      [
          OMDoc.mkOMSE
            caslS
            caslSort_gen_axS
        , processConstraintsOM
            go
            lenv
            ln
            nn
            uN
            fN
            constraints
        , OMDoc.mkOMSE
            caslS
            (if freetype then caslSymbolAtomTrueS else caslSymbolAtomFalseS)
      ]
-- unsupported formulas
-- Mixfix_formula
processFormulaOM _ _ _ _ _ _
  (Mixfix_formula {}) =
    OMDoc.mkOMComment "unsupported : Mixfix_formula"
-- Unparsed_formula
processFormulaOM _ _ _ _ _ _
  (Unparsed_formula {}) =
    OMDoc.mkOMComment "unsupported : Unparsed_formula"
-- ExtFORMULA
processFormulaOM _ _ _ _ _ _
  (ExtFORMULA {}) =
    OMDoc.mkOMComment "unsupported : ExtFORMULA"

processConstraintsOM::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->[ABC.Constraint]
  ->OMDoc.OMElement
processConstraintsOM _ _ _ _ _ _ [] = error "!"
processConstraintsOM go lenv ln nn uN fN ((ABC.Constraint news ops' origs):_)
  =
    OMDoc.mkOMBINDE
      (OMDoc.mkOMS caslS (show news))
      (
        OMDoc.mkOMBVAR
          (
          foldl
            (\vars (op, il) ->
              vars
                ++
                  [
                    OMDoc.mkOMATTR
                      (
                        OMDoc.mkOMATP
                          [
                            (
                                OMDoc.mkOMS
                                  caslS
                                  "constraint-indices"
                              , OMDoc.OMSTR
                                  (foldl
                                    (\s i -> (s++(show i)++"|"))
                                    ""
                                    il
                                  )
                            )
                          ]
                      )
                      (processOperatorOM go lenv ln nn uN fN op)
                  ]
            )
            []
            ops'
          )
      )
      (OMDoc.mkOMS caslS (show origs))

wrapFormulasCMPIOOM::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->[(Ann.Named CASLFORMULA)]
  ->IO ([OMDoc.Axiom], [OMDoc.Definition], [OMDoc.Presentation])
wrapFormulasCMPIOOM go lenv ln nn cM uN fN fs =
  let
    posLists = concatMap Id.getPosList (map Ann.sentence fs)
  in
  do
    poslinemap <- posLines posLists
    return
      $
      foldl
        (\(wax, wde, wpr) f ->
          let
            (axdef, pr) = wrapFormulaCMPOM go lenv ln nn cM uN fN f poslinemap
          in
            case axdef of
              (Left ax) ->
                (wax++[ax], wde, wpr++[pr])
              (Right def) ->
                (wax, wde++[def], wpr++[pr])
        )
        ([], [], [])
        (zip fs [1..])

wrapFormulaCMPOM::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->((Ann.Named CASLFORMULA), Int)
  ->(Map.Map Id.Pos String)
  ->(Either OMDoc.Axiom OMDoc.Definition, OMDoc.Presentation)
wrapFormulaCMPOM
  go
  lenv
  ln
  nn
  currentMapping
  uniqueNames
  fullNames
  (ansen, sennum)
  poslinemap =
  let
    senxmlid =
      case
        Hets.getNameForSens
          [currentMapping]
          (Hets.stringToId $ Ann.senName ansen, sennum)
      of
        Nothing ->
          error
            ("No unique name for Sentence \"" ++ Ann.senName ansen ++ "\"")
        (Just n) -> n
    sens = Ann.sentence ansen
    sposl = Id.getPosList sens
    omformula = processFormulaOM go lenv ln nn uniqueNames fullNames sens
    omobj = OMDoc.mkOMOBJ omformula
    cmptext = 
      foldl
        (\cmpt p ->
          cmpt ++ (Map.findWithDefault "" p poslinemap) ++ "\n"
        )
        ""
        sposl
    cmp = OMDoc.mkCMP (OMDoc.MTextText cmptext) 
    fmp = OMDoc.FMP Nothing (Left omobj)
    axiom =
      if Ann.isAxiom ansen
        then
          Left $ OMDoc.mkAxiom senxmlid [cmp] [fmp]
        else
          Right $ OMDoc.mkDefinition senxmlid [cmp] [fmp]
    pres = makePresentationForOM senxmlid (Ann.senName ansen)
  in
    (axiom, pres)

