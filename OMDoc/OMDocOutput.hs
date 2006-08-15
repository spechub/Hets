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
  ( (+++), (+=)
    , a_name, k_public, k_system, emptyRoot
    , v_1, a_indent,{- a_issue_errors,-} a_output_file
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
    libToOMDocIdNameMapping hco lnle file

-- | create OMDoc (files) from a library environment
libToOMDocIdNameMapping::
  HetcatsOpts
  ->(ASL.LIB_NAME, LibEnv)
  ->FilePath
  ->IO ()
libToOMDocIdNameMapping
  hco
  (ln, lenv)
  fp
  =
    let
      tracemarks = id $! (Hets.createTraceMarks lenv)
      minlenv = Hets.createMinimalLibEnv lenv tracemarks
      uniqueNames = Hets.createUniqueNames minlenv tracemarks
      fullNames = Hets.createFullNameMapping lenv tracemarks uniqueNames
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
                        libEnvLibNameIdNameMappingToOMDocCMPIOIN 
                          (emptyGlobalOptions { hetsOpts = hco })
                          lenv
                          libname
                          (createLibName libname)
                          uniqueNamesXml
                          fullNamesXml
                      putStrLn ("Writing " ++ filename ++ " to " ++ outfile)
                      System.Directory.createDirectoryIfMissing True (snd $ splitPath outfile)
                      writeOMDocDTD dtduri omdoc outfile >> return ()
                )
                (Map.keys lenv)
              return ()
          else
            do
              dtduri <- envDTDURI
              omdoc <-
                libEnvLibNameIdNameMappingToOMDocCMPIOIN 
                  (emptyGlobalOptions { hetsOpts = hco })
                  lenv
                  ln
                  (createLibName ln)
                  uniqueNamesXml
                  fullNamesXml
              writeOMDocDTD dtduri omdoc fp >> return ()
    in
      outputio

-- | creates a xml structure describing a Hets-presentation for a symbol 
makePresentationFor::XmlName->String->HXT.XmlFilter
makePresentationFor xname presstring =
  HXT.etag "presentation" += (
    (HXT.sattr "for" xname)
    +++ HXT.etag "use" += (
      (HXT.sattr "format" "Hets")
      +++ (HXT.txt presstring)
      )
    )

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

{- |
  creates a xml-representation of a definitional link (LocalDef, GlobalDef,
  HidingDef [, FreeDef, CofreeDef]) using given 'IdNameMapping'S in creation
  of morphisms
-}
createXmlDefLink::
  Static.DevGraph.LibEnv
  ->Hets.LIB_NAME
  ->Graph.LEdge Static.DevGraph.DGLinkLab
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(HXT.XmlTree->HXT.XmlTrees)
createXmlDefLink lenv ln (from, to, ll) uniqueNames names =
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
            qualattr "" "type" "local" 
        _ -> xmlNullFilter
  in
    HXT.etag "imports"
      += (
        qualattr "" "from" (liburl ++ "#" ++ fromname) +++ linktype
        +++ (createXmlMorphism lenv ln (from, to, ll) uniqueNames names)
      )


{- |
  creates a xml-representation of a theorem link (LocalThm, GlobalThm,
  HidingThm) using given 'IdNameMapping'S in creation
  of morphisms
-}
createXmlThmLink::
  Static.DevGraph.LibEnv
  ->Hets.LIB_NAME
  ->Graph.LEdge Static.DevGraph.DGLinkLab
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(HXT.XmlTree->HXT.XmlTrees)
createXmlThmLink lenv ln (edge@(from, to, ll)) uniqueNames names =
  let
    dg = devGraph $ Map.findWithDefault (error "!") ln lenv
    fromnode = Data.Maybe.fromMaybe (error "!") $ Graph.lab dg from
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
    tagname =
      case dgl_type ll  of
        (Static.DevGraph.GlobalThm _ _ _) -> theoryInclusionS
        (Static.DevGraph.LocalThm _ _ _) -> axiomInclusionS
        _ -> error "corrupt data"
    consattr =
      case dgl_type ll of
        (Static.DevGraph.GlobalThm _ c _) -> consAttr c
        (Static.DevGraph.LocalThm _ c _) -> consAttr c
        _ -> error "corrupt data"
  in
      HXT.etag tagname
        += (
          qualattr
            "xml"
            "id"
            (
              (if tagname == axiomInclusionS then "ai" else "ti")
                ++ "." ++ toname ++ "." ++ fromname
            )
          +++ HXT.sattr "from" (liburl ++ "#" ++ fromname) 
          +++ HXT.sattr "to" ("#" ++ toname)
          +++ consattr
          +++ (createXmlMorphism lenv ln edge uniqueNames names)
        )
  where
  consAttr::Static.DevGraph.Conservativity->HXT.XmlFilter
  consAttr Static.DevGraph.None = xmlNullFilter
  consAttr Static.DevGraph.Mono = HXT.sattr "conservativity" "monomorphism"
  consAttr Static.DevGraph.Cons = HXT.sattr "conservativity" "conservative"
  consAttr Static.DevGraph.Def = HXT.sattr "conservativity" "definitional"

{- |
  create a xml-representation of a (CASL-)morphism
-}
createXmlMorphism::
  Static.DevGraph.LibEnv
  ->Hets.LIB_NAME
  ->Graph.LEdge Static.DevGraph.DGLinkLab
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(HXT.XmlTree->HXT.XmlTrees)
createXmlMorphism
  _
  ln
  (from, to, ll)
  uniqueNames
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
                Hets.getNameOrigins uniqueNames oname
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
                Hets.getNameOrigins uniqueNames nname
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
               [] -> error "Pred not in From-Set!" 
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
                Hets.getNameOrigins uniqueNames oname
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
                Hets.getNameOrigins uniqueNames nname
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
                Hets.getNameOrigins uniqueNames oname
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
                Hets.getNameOrigins uniqueNames nname
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
    hiddenattr = 
      case hidden of
        [] -> xmlNullFilter
        _ -> qualattr "" "hiding" (implode " " hidden)
    reqs =
      foldl
        (\r ((f,fo), (t,to')) ->
          r
          +++
          HXT.etag "requation"
            += (
              HXT.etag "OMOBJ"
                += (
                  HXT.etag "OMS"
                    += (
                      qualattr "" "cd" (Hets.inmGetNodeId fo)
                      +++
                      qualattr "" "name" f
                    )
                )
              +++
              HXT.etag "OMOBJ"
                += (
                  HXT.etag "OMS"
                    += (
                      qualattr "" "cd" (Hets.inmGetNodeId to')
                      +++
                      qualattr "" "name" t
                    )
                )
            )
            +++
            xmlNL
        )
        xmlNullFilter
        allmapped
  in
    if Hets.isEmptyMorphism caslmorph && null hidden
      then
        xmlNullFilter
      else
        xmlNL +++
        HXT.etag "morphism"
          += (
            hiddenattr
              +++ (
                if Hets.isEmptyMorphism caslmorph
                  then
                    xmlNullFilter
                  else
                    xmlNL +++ reqs
                  )
          )
        +++
        xmlNL
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

{- |
  create a xml representation for a set of contructors
-}
createConstructorsIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->Set.Set (OpType, String)
  ->HXT.XmlFilter
createConstructorsIN
  ln
  nn
  uniqueNames
  fullNames
  conset
  =
  if Set.null conset
    then
      xmlNullFilter
    else
      Set.fold
        (\c x ->
          x
          +++
          createConstructorIN
            ln
            nn
            uniqueNames
            fullNames
            c
          +++
          xmlNL
        )
        xmlNullFilter
        conset

{- |
  create a xml presentation for a constructor
-}
createConstructorIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(OpType, String)
  ->HXT.XmlFilter
createConstructorIN
  ln
  nn
  uniqueNames
  fullNames
  (ot, oxmlid)
  =
  HXT.etag "constructor"
    += (
      HXT.sattr "name" oxmlid
      +++
      xmlNL
      +++
      foldl
        (\argx arg ->
          argx
          +++
          xmlNL
          +++
          (
          HXT.etag "argument"
            += (
              HXT.etag "type"
                += (
                  HXT.etag "OMOBJ"
                    += (
                      createSymbolForSortIN
                        ln
                        nn
                        uniqueNames
                        fullNames
                        arg
                    )
                )
            )
          )
        )
        xmlNullFilter
        (opArgs ot)
    )
    
{- | 
  check if a relation contains information about a certain sort
-}
emptyRelForSort::Rel.Rel SORT->SORT->Bool
emptyRelForSort rel s =
  null $ filter (\(s', _) -> s' == s) $ Rel.toList rel

{- |
  create a xml representation of a sort relation
-}
createInsortFor::
  Rel.Rel SORT
  ->SORT
  ->Hets.IdNameMapping
  ->HXT.XmlFilter
  ->HXT.XmlFilter
createInsortFor rel s idNameMapping constructors =
  HXT.etag "adt"
    += (
     xmlNL +++
     HXT.etag "sortdef"
      += (
        qualattr "" "name" (getNameE s)
        +++
        qualattr "" "type" "free"
        +++
        constructors
        +++
        foldl
          (\x (s'', s') ->
            if s'' == s
              then
                x
                +++
                xmlNL
                +++
                HXT.etag "insort"
                  += (
                    qualattr "" "for" ("#" ++ getNameE s')
                  )
              else
                x
          )
          xmlNullFilter
          (Rel.toList rel)
        +++
        xmlNL
      )
    +++
    xmlNL
    )
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
  
-- | Convert a DevGraph from a library environment to OMDoc-XML with given
-- xml:id attribute
-- will also scan used (CASL-)files for CMP-generation
libEnvLibNameIdNameMappingToOMDocCMPIOIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->String
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->IO HXT.XmlTrees
libEnvLibNameIdNameMappingToOMDocCMPIOIN go lenv ln name' uniqueNames fullNames =
  do
    dgx <- libEnvLibNameIdNameMappingToXmlCMPIO go lenv ln uniqueNames fullNames
    return
      (
        (
          HXT.etag "omdoc"
            += (
              qualattr omdocNameXMLNS omdocNameXMLAttr name'
              +++ xmlNL
              +++ dgx
            )
        )
        emptyRoot
      )

{- |
  create a xml representation for a DevGraph from a library environment
-}
libEnvLibNameIdNameMappingToXmlCMPIO::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->IO (HXT.XmlTree->HXT.XmlTrees)
libEnvLibNameIdNameMappingToXmlCMPIO
  go
  lenv
  ln
  uniqueNames
  fullNames
  =
    let
      dg = devGraph $ Map.findWithDefault (error "!") ln lenv
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
            theoryXml =
              ( \sentencesXml ->
                HXT.etag "theory"
                  +=
                    (
                      qualattr "xml" "id" (Hets.inmGetNodeId idnamemapping)
                      +++
                      makePresentationFor
                        (Hets.inmGetNodeId idnamemapping)
                        (Hets.idToString $ Hets.nodeNameToId dgnodename)
                      +++
                      xmlNL
                      +++
                      foldl
                        (\nx' edge ->
                          nx' +++ 
                            createXmlDefLink
                              lenv
                              ln
                              edge
                              uniqueNames
                              fullNames
                            +++
                            xmlNL
                        )
                        xmlNullFilter
                        (filterDefLinks (Graph.inn dg nn))
                      +++
                      (
                        Set.fold
                         (\s nx' ->
                          let
                            consremap =
                              Set.map
                                (\( (_, _, ot), uname ) -> (ot, uname))
                                (Hets.inmGetIdNameConsSet uniqueidnamemapping)
                            sortcons = filterSORTConstructors consremap s
                            conxml = 
                              createConstructorsIN
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
                                nx'
                                +++
                                if (Set.size sortcons) > 0
                                  then
                                    createInsortFor
                                      Rel.empty
                                      s
                                      idnamemapping
                                      conxml
                                  else
                                    xmlNullFilter
                              (Just (uid, uname)) ->
                                nx'
                                +++
                                sortToXmlXN (XmlNamed s uname) +++ xmlNL +++
                                makePresentationFor uname (Hets.idToString s) +++ xmlNL
                                +++
                                if (not $ emptyRelForSort (sortRel caslsign) uid)
                                  || ( (Set.size sortcons) > 0 )
                                  then
                                    createInsortFor
                                      (sortRel caslsign)
                                      uid
                                      idnamemapping
                                      conxml
                                  else
                                    xmlNullFilter
                         )
                         xmlNullFilter
                         (sortSet caslsign)
                      )
                      +++
                      (
                        Map.foldWithKey
                          (\pid pts nx' ->
                            Set.fold
                              (\pt nx'' ->
                                case 
                                  find
                                    (\( (uid, upt), _) -> uid == pid && upt == pt)
                                    (Set.toList (Hets.inmGetIdNamePredSet uniqueidnamemapping))
                                of
                                  Nothing -> nx''
                                  (Just (_, uname )) ->
                                    nx''
                                    +++ xmlNL +++
                                    (
                                    predicationToXmlIN
                                      ln
                                      nn
                                      idnamemapping
                                      uniqueNames
                                      fullNames
                                      (pid, pt)
                                    )
                                    +++ xmlNL +++
                                    makePresentationFor
                                      uname
                                      (Hets.idToString pid)
                              )
                              nx'
                              pts
                          )
                          xmlNullFilter
                          (predMap caslsign)
                      )
                      +++
                      (
                        Map.foldWithKey
                          (\oid ots nx' ->
                            Set.fold
                              (\ot nx'' ->
                                case 
                                  find
                                    (\( (uid, uot), _) -> uid == oid && uot == ot)
                                    (Set.toList (Hets.inmGetIdNameOpSet uniqueidnamemapping))
                                of
                                  Nothing -> nx''
                                  (Just (_, uname )) ->
                                    nx''
                                    +++ xmlNL +++
                                    (
                                    operatorToXmlIN
                                      ln
                                      nn
                                      idnamemapping
                                      uniqueNames
                                      fullNames
                                      (oid, ot)
                                    )
                                    +++ xmlNL +++
                                    makePresentationFor
                                      uname
                                      (Hets.idToString oid)
                              )
                              nx'
                              ots
                          )
                          xmlNullFilter
                          (opMap caslsign)
                      )
                      +++
                      xmlNL
                      +++ sentencesXml +++ xmlNL
                    )
                    +++
                    (
                      foldl
                        (\t edge ->
                          t +++ xmlNL +++
                            createXmlThmLink
                              lenv
                              ln
                              edge
                              uniqueNames
                              fullNames
                        )
                        xmlNullFilter
                        (filterThmLinks $ Graph.inn dg nn)
                    )
              )
          in
            do
              x <- xio
              sensXml <-
                wrapFormulasCMPIOIN
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
                  return x
                else
                  return
                    (
                      x
                      +++
                      xmlNL
                      +++
                      (theoryXml sensXml)
                      +++
                      xmlNL
                    )
        )
        (return xmlNullFilter)
        (Graph.labNodes dg)

{- |
  create a xml-name for a library.
  this has the form of "File#Theory" for referenced libs and
  "#Theory" for other theories.
-}
getNodeNameForXml::Hets.IdNameMapping->Hets.LIB_NAME->String
getNodeNameForXml inm ln =
  (
  if Hets.inmGetLibName inm /= ln
    then
      asOMDocFile $ unwrapLinkSource $ (Hets.inmGetLibName inm)
    else
      ""
  ) ++ Hets.inmGetNodeId inm
  

{- |
  create a xml-representation for a predication
-}
predicationToXmlIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(Id.Id, PredType)
  ->(HXT.XmlTree->HXT.XmlTrees)
predicationToXmlIN 
  ln
  _ -- nn
  currentmapping
  uniqueNames
  _ -- fullNames
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
            case Hets.getNameOrigins uniqueNames argxmlid of
              [] -> error ("No origin for Sort " ++ show argxmlid)
              [o] -> getNodeNameForXml o ln
              (o:_) ->
                Debug.Trace.trace
                  ("More than one origin for \"" ++ show argxmlid ++ "\"")
                  $ 
                  getNodeNameForXml o ln
          )
          argnames
      argzip =
        zip
          argnames
          argorigins
    in
      HXT.etag "symbol"
        += (
          qualattr predNameXMLNS predNameXMLAttr pidxmlid
          +++ qualattr symbolTypeXMLNS symbolTypeXMLAttr "object"
          +++ xmlNL
          +++ (HXT.etag "type" += ( HXT.sattr "system" "casl" ))
            += (
              xmlNL
              +++
              HXT.etag "OMOBJ"
                += (
                  xmlNL
                  +++
                  HXT.etag "OMA"
                    += (
                      xmlNL
                      +++
                      (HXT.etag "OMS"
                        += (
                          HXT.sattr "cd" "casl"
                          +++ HXT.sattr "name" "predication"
                        )
                      )
                      +++
                      (
                      foldl
                        (\px (an, ao) ->
                          px +++ xmlNL
                          +++
                          (HXT.etag "OMS"
                            += (
                              HXT.sattr "cd" ao
                              +++ HXT.sattr "name" an
                            )
                          )
                        )
                        xmlNullFilter
                        argzip
                      )
                      +++
                      xmlNL
                    )
                    +++
                xmlNL
                )
                +++
                xmlNL
            )
            +++ xmlNL
        )

{-
  create a xml-representation for an operator
-}
operatorToXmlIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->(Id.Id, OpType)
  ->(HXT.XmlTree->HXT.XmlTrees)
operatorToXmlIN
  ln
  _ -- nn
  currentmapping
  uniqueNames
  _ -- fullNames
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
            case Hets.getNameOrigins uniqueNames argxmlid of
              [] -> error ("No origin for Sort " ++ show argxmlid)
              [o] -> getNodeNameForXml o ln
              (o:_) ->
                Debug.Trace.trace
                  ("More than one origin for \"" ++ show argxmlid ++ "\"")
                  $ 
                  getNodeNameForXml o ln
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
        case Hets.getNameOrigins uniqueNames resxmlid of
          [] -> error ("No origin for Sort " ++ show resxmlid)
          [o] -> getNodeNameForXml o ln
          (o:_) ->
            Debug.Trace.trace
              ("More than one origin for \"" ++ show resxmlid ++ "\"")
              $ 
              getNodeNameForXml o ln
    in
      HXT.etag "symbol"
        += (
          qualattr opNameXMLNS opNameXMLAttr oidxmlid
          +++ qualattr symbolTypeXMLNS symbolTypeXMLAttr "object"
          +++ xmlNL
          +++ (HXT.etag "type" += (HXT.sattr "system" "casl"))
            += (
              xmlNL
              +++ HXT.etag "OMOBJ"
                += (
                  xmlNL
                  +++ HXT.etag "OMA"
                    += (
                      xmlNL
                      +++ (
                        HXT.etag "OMS"
                          += (
                            HXT.sattr "cd" "casl"
                            +++ HXT.sattr "name"
                              (if (opKind ot)==Total
                                then
                                  "function"
                                else
                                  "partial-function"
                              )
                          )
                        )
                      +++
                      (
                      foldl
                        (\px (an, ao) ->
                          px +++ xmlNL
                          +++
                          (HXT.etag "OMS"
                            += (
                              HXT.sattr "cd" ao
                              +++ HXT.sattr "name" an
                            )
                          )
                        )
                        xmlNullFilter
                        argzip
                      )
                      +++ xmlNL
                      +++ (
                        HXT.etag "OMS"
                          += (
                            HXT.sattr "cd" resorigin
                            +++ HXT.sattr "name" resxmlid
                          )
                      )
                      +++ xmlNL
                    )
                    +++ xmlNL
                )
                +++ xmlNL
            )
            +++ xmlNL
        )

{-
  create a xml-representation for a sort
-}
sortToXmlXN::XmlNamed SORT->HXT.XmlFilter
sortToXmlXN xnSort =
  ((HXT.etag "symbol" +=
    ( qualattr symbolTypeXMLNS symbolTypeXMLAttr "sort"
    +++ qualattr sortNameXMLNS sortNameXMLAttr (xnName xnSort)))
  )

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
processVarDeclIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->[VAR_DECL]
  ->(HXT.XmlTree->HXT.XmlTrees)
processVarDeclIN ln nn uN fN vdl =
  (
    HXT.etag "OMBVAR"
      += (
        xmlNL
        +++
        (processVarDecls vdl)
      )
  )
  +++ xmlNL
  where
  processVarDecls::
    [VAR_DECL]
    ->(HXT.XmlTree->HXT.XmlTrees)
  processVarDecls [] = xmlNullFilter
  processVarDecls ( (Var_decl vl s _):vdl' ) =
    -- <ombattr><omatp><oms>+</omatp><omv></ombattr>
    (
      foldl
        (\decls vd ->
          decls
          +++
          ( createTypedVarIN ln nn uN fN s (show vd) )
          +++ xmlNL
        )
        (xmlNullFilter)
        vl
    )
    +++ (processVarDecls vdl')

createATPIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->SORT
  ->(HXT.XmlTree->HXT.XmlTrees)
createATPIN ln nn uniqueNames fullNames sort =
  HXT.etag "OMATP"
    += (
      (HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" typeS ))
      +++ createSymbolForSortIN ln nn uniqueNames fullNames sort
    )
                 
createTypedVarIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->SORT
  ->String
  ->(HXT.XmlTree->HXT.XmlTrees)
createTypedVarIN ln nn uniqueNames fullNames sort varname =
  HXT.etag "OMATTR"
    +=(
      (createATPIN ln nn uniqueNames fullNames sort)
      +++ (HXT.etag "OMV" += (HXT.sattr "name" varname))
    )

createSymbolForSortIN::
  Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->SORT
  ->(HXT.XmlTree->HXT.XmlTrees)
createSymbolForSortIN
  ln
  nn
  uniqueNames
  fullNames
  s
  =
    let
      currentMapping =
        fromMaybe
          (error "!")
          $
          Hets.inmFindLNNN (ln, nn) fullNames
      sortxmlid =
        case
          find
            (\(sid, _) -> s == sid)
            (Set.toList $ Hets.inmGetIdNameSortSet currentMapping)
        of
          Nothing -> error "!!"
          (Just (_, uname)) -> uname
      sortorigin =
        case
          Hets.getNameOrigins uniqueNames sortxmlid
        of
          [] -> error "!!!"
          [o] -> getNodeNameForXml o ln
          (o:_) -> Debug.Trace.trace ("!!!!") $ getNodeNameForXml o ln
    in
      HXT.etag "OMS" += ( HXT.sattr "cd" sortorigin +++ HXT.sattr "name" sortxmlid )

-- | create an xml-representation for a predication
createSymbolForPredicationIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  -> PRED_SYMB -- ^ the predication to process
  -> (HXT.XmlTree -> HXT.XmlTrees) 
       -- ^ a xml-representation of the predication
-- Pred_name
createSymbolForPredicationIN _ _ ln nn uniqueNames fullNames
  (Pred_name pr) =
    let
      currentMapping =
        fromMaybe
          (error "!")
          $
          Hets.inmFindLNNN (ln, nn) fullNames
      (predxmlid, predorigin) =
          case 
            find
              (\( (uid, _), _) -> uid == pr)
              (Set.toList (Hets.inmGetIdNamePredSet currentMapping))
          of
            Nothing -> -- error ("Unknown (unqualified) pred! " ++ show pr)
              Debug.Trace.trace
                ("Unknown (unqualified) pred! " ++ show pr)
                (show pr, getNodeNameForXml currentMapping ln)
            (Just (_, uname)) ->
              case Hets.getNameOrigins uniqueNames uname of
                [] -> error "Whoops!"
                [o] -> (uname, getNodeNameForXml o ln)
                (o:_) ->
                  Debug.Trace.trace
                    ("more than one...")
                    (uname, getNodeNameForXml o ln)
    in
      HXT.etag "OMS" +=
        (HXT.sattr "cd" predorigin +++ HXT.sattr "name" predxmlid)
-- Qual_pred_name
createSymbolForPredicationIN _ lenv ln nn uniqueNames fullNames
  (Qual_pred_name pr pt _) =
    let
      currentMapping =
        fromMaybe
          (error "!")
          $
          Hets.inmFindLNNN (ln, nn) fullNames
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
          preferEqualFindCompatible
            (Set.toList (Hets.inmGetIdNamePredSet currentMapping))
            (\( (uid, upt), _) ->
              uid == pr && upt == (Hets.cv_Pred_typeToPredType pt)
            )
            (\( (uid, upt), _) ->
              uid == pr &&
                compatiblePredicate
                  currentRel
                  upt
                  (Hets.cv_Pred_typeToPredType pt)
            )
        of
          Nothing -> -- error ("Unknown pred! " ++ show pr ++ " :: " ++ show pt )
            Debug.Trace.trace
              ("Unknown pred! " ++ show pr ++ " :: " ++ show pt )
              (show pr, getNodeNameForXml currentMapping ln)
          (Just (_, uname)) ->
            case Hets.getNameOrigins uniqueNames uname of
              [] -> error "Whoops!"
              [o] -> (uname, getNodeNameForXml o ln)
              (o:_) -> Debug.Trace.trace ("more than one...") $ (uname, getNodeNameForXml o ln)

    in
      HXT.etag "OMS" +=
        (HXT.sattr "cd" predorigin +++ HXT.sattr "name" predxmlid)


-- | create a xml-representation of an operator
processOperatorIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  -> OP_SYMB -- ^ the operator to process
  -> (HXT.XmlTree -> HXT.XmlTrees) 
      -- ^ the xml-representation of the operator
-- Op_name
processOperatorIN _ _ ln nn uniqueNames fullNames
  (Op_name op) =
    let
      currentMapping =
        fromMaybe
          (error "!")
          $
          Hets.inmFindLNNN (ln, nn) fullNames
      (opxmlid, oporigin) =
        if (show op) == "PROJ"
          then
            ("PROJ", "casl")
          else
            case 
              find
                (\( (uid, _), _) -> uid == op)
                (Set.toList (Hets.inmGetIdNameOpSet currentMapping))
            of
              Nothing -> -- error ("Unknown (unqualified) op! " ++ show op)
                Debug.Trace.trace
                  ("Unknown (unqualified) op! " ++ show op)
                  (show op, getNodeNameForXml currentMapping ln)
              (Just (_, uname)) ->
                case Hets.getNameOrigins uniqueNames uname of
                  [] -> error "Whoops!"
                  [o] -> (uname, getNodeNameForXml o ln)
                  (o:_) -> Debug.Trace.trace ("more than one...") $ (uname, getNodeNameForXml o ln)
    in
      HXT.etag "OMS" +=
        (HXT.sattr "cd" oporigin +++ HXT.sattr "name" opxmlid)
-- Qual_op_name
processOperatorIN _ lenv ln nn uniqueNames fullNames
  (Qual_op_name op ot _) =
    let
      currentMapping =
        fromMaybe
          (error "!")
          $
          Hets.inmFindLNNN (ln, nn) fullNames
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
      (opxmlid, oporigin) =
        case
          preferEqualFindCompatible
            (Set.toList (Hets.inmGetIdNameOpSet currentMapping))
            (\( (uid, uot), _) -> uid == op && uot == (Hets.cv_Op_typeToOpType ot))
            (\( (uid, uot), _) -> uid == op && compatibleOperator currentRel uot (Hets.cv_Op_typeToOpType ot))

        of
          Nothing -> -- error ("Unknown op! " ++ show op ++ " :: " ++ show ot )
            Debug.Trace.trace
              ("Unknown op! " ++ show op ++ " :: " ++ show ot )
              (show op, getNodeNameForXml currentMapping ln)
          (Just (_, uname)) ->
            case Hets.getNameOrigins uniqueNames uname of
              [] -> error "Whoops!"
              [o] -> (uname, getNodeNameForXml o ln)
              (o:_) -> Debug.Trace.trace ("more than one...") $ (uname, getNodeNameForXml o ln)

    in
      HXT.etag "OMS" +=
        (HXT.sattr "cd" oporigin +++ HXT.sattr "name" opxmlid)

preferEqualFindCompatible::[a]->(a->Bool)->(a->Bool)->Maybe a
preferEqualFindCompatible l isEqual isCompatible =
  case find isEqual l of
    Nothing ->
      find isCompatible l
    x -> x

-- | create a xml-representation from a term (in context of a theory)
processTermIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  -> TERM f -- ^ the term to process
  -> (HXT.XmlTree -> HXT.XmlTrees) -- ^ xml-representation of the term
-- Simple_id
processTermIN _ _ _ _ _ _
  (Simple_id id' ) =
    HXT.etag "OMV" +=
      HXT.sattr "name" (show id' ) -- not needed
-- Qual_var
processTermIN _ _ ln nn uniqueNames fullNames
  (Qual_var v s _) =
    ( createTypedVarIN ln nn uniqueNames fullNames s (show v) ) +++
    xmlNL
-- Application
processTermIN go lenv ln nn uniqueNames fullNames
  (Application op termlist _) =
    if null termlist
      then
        (processOperatorIN go lenv ln nn uniqueNames fullNames op) +++
        xmlNL
      else
        (HXT.etag "OMA" +=
          (xmlNL +++
          ( processOperatorIN go lenv ln nn uniqueNames fullNames op) +++
          (foldl (\terms t ->
            terms +++
            (processTermIN go lenv ln nn uniqueNames fullNames t)
            ) (xmlNullFilter) termlist
          )
          ) ) +++
          xmlNL
-- Cast
processTermIN go lenv ln nn uniqueNames fullNames
  (Cast t s _) =
    processTermIN go lenv ln nn uniqueNames fullNames
      (Application
        (Op_name $ Hets.stringToId "PROJ")
        [t, (Simple_id $ Id.mkSimpleId (show s))]
        Id.nullRange
      )
-- Conditional
processTermIN go lenv ln nn uniqueNames fullNames
  (Conditional t1 f t2 _) =
    HXT.etag "OMA" +=
      (xmlNL +++
      (HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" "IfThenElse"
        )
      ) +++
      (processFormulaIN go lenv ln nn uniqueNames fullNames f) +++
      (processTermIN go lenv ln nn uniqueNames fullNames t1) +++
      (processTermIN go lenv ln nn uniqueNames fullNames t2)
      )
-- Sorted_term is to be ignored in OMDoc (but could be modelled...) (Sample/Simple.casl uses it...)
processTermIN go lenv ln nn uniqueNames fullNames
  (Sorted_term t _ _) =
    processTermIN go lenv ln nn uniqueNames fullNames t
-- Unsupported Terms...
processTermIN _ _ _ _ _ _ _ = error "Unsupported Term encountered..." 

processFormulaIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->FORMULA f 
  -> (HXT.XmlTree -> HXT.XmlTrees) -- ^ xml-representation of the formula
-- Quantification
processFormulaIN go lenv ln nn uN fN
  (Quantification q vl f _) =
    ( HXT.etag "OMBIND" += (
      xmlNL +++
      (HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" (quantName q))
      ) +++
      (xmlNL) +++
      (processVarDeclIN ln nn uN fN vl) +++
      (processFormulaIN go lenv ln nn uN fN f) )
    ) +++
    xmlNL
-- Conjunction
processFormulaIN go lenv ln nn uN fN
  (Conjunction fl _) =
    (HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslConjunctionS)
      ) +++
      (
        foldl
          (\forms f ->
            forms
            +++
            processFormulaIN go lenv ln nn uN fN f
          )
          xmlNL
          fl
      )
    ) ) +++
    xmlNL
-- Disjunction
processFormulaIN go lenv ln nn uN fN
  (Disjunction fl _) =
    (HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslDisjunctionS)
      ) +++
      (foldl (\forms f ->
        forms +++
        processFormulaIN go lenv ln nn uN fN f
        ) (xmlNL) fl)
    ) ) +++
    xmlNL
-- Implication
processFormulaIN go lenv ln nn uN fN
  (Implication f1 f2 b _) =
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslImplicationS)
      ) +++
      (xmlNL) +++
      (processFormulaIN go lenv ln nn uN fN f1) +++
      (processFormulaIN go lenv ln nn uN fN f2) +++
      (processFormulaIN go lenv ln nn uN fN
              (if b then True_atom Id.nullRange else False_atom Id.nullRange))
    ) ) +++
    xmlNL
-- Equivalence
processFormulaIN go lenv ln nn uN fN
  (Equivalence f1 f2 _) =
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslEquivalenceS)
      ) +++
      (xmlNL) +++
      (processFormulaIN go lenv ln nn uN fN f1) +++
      (processFormulaIN go lenv ln nn uN fN f2)
    ) ) +++
    xmlNL
-- Negation
processFormulaIN go lenv ln nn uN fN
  (Negation f _) =
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslNegationS)
      ) +++
      (xmlNL) +++
      (processFormulaIN go lenv ln nn uN fN f)
    ) ) +++
    xmlNL
-- Predication
processFormulaIN go lenv ln nn uN fN
  (Predication p tl _) =
    (HXT.etag "OMA" += (
      xmlNL +++
      (HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslPredicationS)
      ) +++
      xmlNL +++
      (xmlNL) +++
      (createSymbolForPredicationIN go lenv ln nn uN fN p) +++
      (foldl (\term t ->
        term +++
        (processTermIN go lenv ln nn uN fN t) +++
        xmlNL
        ) (xmlNullFilter) tl
      ) +++
      (xmlNL)
    ) ) +++
    xmlNL
-- Definedness
processFormulaIN go lenv ln nn uN fN
  (Definedness t _ ) =
    (HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslDefinednessS)
      ) +++
      (xmlNL) +++
      (processTermIN go lenv ln nn uN fN t)
    ) ) +++
    xmlNL
-- Existl_equation
processFormulaIN go lenv ln nn uN fN
  (Existl_equation t1 t2 _) = 
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslExistl_equationS)
      ) +++
      (xmlNL) +++
      (processTermIN go lenv ln nn uN fN t1) +++
      (processTermIN go lenv ln nn uN fN t2)
    ) ) +++
    xmlNL
-- Strong_equation
processFormulaIN go lenv ln nn uN fN
  (Strong_equation t1 t2 _) = 
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslStrong_equationS)
      ) +++
      (xmlNL) +++
      (processTermIN go lenv ln nn uN fN t1) +++
      (processTermIN go lenv ln nn uN fN t2)
    ) ) +++
    xmlNL
-- Membership
processFormulaIN go lenv ln nn uN fN
  (Membership t s _) = 
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslMembershipS)
      ) +++
      (xmlNL) +++
      (processTermIN go lenv ln nn uN fN t) +++
      (createSymbolForSortIN ln nn uN fN s )
    ) ) +++
    xmlNL
-- False_atom
processFormulaIN _ _ _ _ _ _
  (False_atom _) =
    (HXT.etag "OMS" +=
      (HXT.sattr "cd" caslS +++
      HXT.sattr "name" caslSymbolAtomFalseS)
    ) +++
    xmlNL
-- True_atom
processFormulaIN _ _ _ _ _ _
  (True_atom _) =
    (HXT.etag "OMS" +=
      (HXT.sattr "cd" caslS +++
      HXT.sattr "name" caslSymbolAtomTrueS)
    ) +++
    xmlNL
-- Sort_gen_ax
processFormulaIN go lenv ln nn uN fN
  (Sort_gen_ax constraints freetype) =
    ( HXT.etag "OMA" +=
      (xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslSort_gen_axS)
      ) +++
      (xmlNL) +++
      --(HXT.etag "OMBVAR" += -- ombvar not allowed in oma
      --      ( xmlNL +++
        (processConstraintsIN go lenv ln nn uN fN constraints) +++
      --      )
      --) +++
      HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name"
          (if freetype then
              caslSymbolAtomTrueS
            else
              caslSymbolAtomFalseS)
        ) +++
        xmlNL
      ) +++
      xmlNL) +++
      xmlNL
-- unsupported formulas
-- Mixfix_formula
processFormulaIN _ _ _ _ _ _
  (Mixfix_formula _) =
    HXT.etag unsupportedS +++
    HXT.txt ( "<-- " ++ "Mixfix_formula" ++ " //-->")
-- Unparsed_formula
processFormulaIN _ _ _ _ _ _
  (Unparsed_formula s _) =
    HXT.etag unsupportedS +++
    HXT.txt ( "<-- " ++ "Unparsed_formula \"" ++ s ++ "\" //-->")
-- ExtFORMULA
processFormulaIN _ _ _ _ _ _
  (ExtFORMULA _) =
    HXT.etag unsupportedS +++
    HXT.txt ( "<-- " ++ "ExtFORMULA" ++ " //-->") 


processConstraintsIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->[ABC.Constraint]
  ->(HXT.XmlTree->HXT.XmlTrees)
processConstraintsIN _ _ _ _ _ _ [] = xmlNullFilter
processConstraintsIN go lenv ln nn uN fN ((ABC.Constraint news ops' origs):_) =
  (HXT.etag "OMBIND" += (
    (HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" (show news)))
    +++ xmlNL
    +++ (HXT.etag "OMBVAR" +=(
      foldl (\opsx (op, il) ->
        opsx +++ (HXT.etag "OMATTR" += (
          (HXT.etag "OMATP" += (
            HXT.etag "OMS"
              += (
                HXT.sattr "cd" caslS
                +++ HXT.sattr "name" "constraint-indices"
              )
            +++ (HXT.etag "OMSTR" += HXT.txt (
              foldl (\s i -> (s++(show i)++"|")) "" il
              ))
            ))
          +++ xmlNL
          +++
            processOperatorIN
              go
              lenv
              ln
              nn
              uN
              fN
              (
                debugGO
                  go
                  "pCXN"
                  ("creating conop for " ++ (show op))
                  op
              )
          ) ) +++ xmlNL
        ) (xmlNullFilter) ops'
      ) )
    +++ xmlNL
    +++ (
      HXT.etag "OMS"
        += (
          HXT.sattr "cd" caslS +++ HXT.sattr "name" (show origs)
        )
      )
    )
  ) +++ xmlNL


wrapFormulasCMPIOIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->[(Ann.Named CASLFORMULA)]
  ->IO (HXT.XmlTree->HXT.XmlTrees)
wrapFormulasCMPIOIN go lenv ln nn cM uN fN fs =
  let
    posLists = concatMap Id.getPosList (map Ann.sentence fs)
  in
  do
    poslinemap <- posLines posLists
    return
      $
      foldl
        (\wrapped f ->
          wrapped
          +++ (wrapFormulaCMPIN go lenv ln nn cM uN fN f poslinemap)
        )
        xmlNullFilter
        (zip fs [1..])
                
wrapFormulaCMPIN::
  GlobalOptions
  ->LibEnv
  ->Hets.LIB_NAME
  ->Graph.Node
  ->Hets.IdNameMapping
  ->[Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
  ->((Ann.Named CASLFORMULA), Int)
  ->(Map.Map Id.Pos String)
  ->(HXT.XmlTree->HXT.XmlTrees)
wrapFormulaCMPIN
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
  in
  (
    (createQAttributed
      "axiom"
      [
        (
            axiomNameXMLNS
          , axiomNameXMLAttr
          , senxmlid
        )
      ]
    ) += (
      (xmlNL +++
      (
        (
          foldl
            (\cmpx p ->
              cmpx
                += (
                  HXT.txt ("\n" ++ (Map.findWithDefault "" p poslinemap))
                )
            )
            (HXT.etag "CMP")
            sposl
        ) += (HXT.txt "\n")
      ) +++ 
      xmlNL +++
      (HXT.etag "FMP" += (
        xmlNL +++
        (
         HXT.etag "OMOBJ" +++
         xmlNL
        ) += (
          xmlNL +++
          (processFormulaIN
            go
            lenv
            ln
            nn
            uniqueNames
            fullNames
            sens
          )
          ) +++
        xmlNL
        )
      ) +++
      xmlNL
      )
      ) +++
    xmlNL +++
    makePresentationFor (senxmlid) (Ann.senName ansen)
  ) +++ xmlNL


