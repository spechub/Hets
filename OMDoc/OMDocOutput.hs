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
{-  (
     showOMDoc
    ,showOMDocDTD
    ,writeOMDoc
    ,writeOMDocDTD
    ,devGraphToOMDocCMPIOXN
    ,dGraphGToXmlGXN
    ,hetsToOMDoc
    ,devGraphToOMDoc
    ,libToOMDoc
    ,writeXmlG
    ,defaultDTDURI
    ,libEnvToDGraphG
    ,linkTypeToString
    ,xmlTagLibEnv
    ,createXmlNameMap
    ,createXmlNameMapping
  ) -}
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
import qualified Common.Lib.Graph as CLGraph

-- Often used symbols from HXT
import Text.XML.HXT.Parser
  ( (+++), (+=)
    , a_name, k_public, k_system, emptyRoot
    , v_1, a_indent, a_issue_errors, a_output_file
  )
        
import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)
import qualified Text.XML.HXT.DOM.XmlTreeTypes as HXTT hiding (when)
--import qualified Text.XML.HXT.XPath as XPath

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import qualified Common.AS_Annotation as Ann

--import qualified Logic.Logic as Logic

import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf, find, delete)

import Debug.Trace (trace)

import qualified System.Directory as System.Directory

import Control.Monad

import Char (toLower)

import OMDoc.Util
import OMDoc.Container
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

useLibWrite::IO Bool
useLibWrite =
  do
    me <- mGetEnv "OMDOC_USE_LIB_WRITE"
    return
      (
      case me of
        Nothing -> True -- use as default
        (Just s) ->
          elem (map toLower s) ["", "1", "yes", "y", "t", "true"]
      )
        

-- | this function wraps trees into a form that can be written by HXT
writeableTrees::HXT.XmlTrees->HXT.XmlTree
writeableTrees t =
  (HXT.NTree
    ((\(HXT.NTree a _) -> a) emptyRoot)
    t
  )
                
-- | this function wraps trees into a form that can be written by HXT
writeableTreesDTD::String->HXT.XmlTrees->HXT.XmlTree
writeableTreesDTD dtd' t =
  (HXT.NTree
    ((\(HXT.NTree a _) -> a) emptyRoot)
    ((HXT.NTree (mkOMDocTypeElem dtd' ) [])
      :(HXT.NTree (HXT.XText "\n")[])
      :t)
  )
                
-- | this function shows Xml with indention
showOMDoc::HXT.XmlTrees->IO HXT.XmlTrees
showOMDoc t = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_issue_errors, v_1)] $
    writeableTrees t
                
-- | this function shows Xml with indention
showOMDocDTD::String->HXT.XmlTrees->IO HXT.XmlTrees
showOMDocDTD dtd' t = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_issue_errors, v_1)] $
    writeableTreesDTD dtd' t

-- | this function writes Xml with indention to a file
writeOMDoc::HXT.XmlTrees->String->IO HXT.XmlTrees
writeOMDoc t f = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_output_file, f)] $
    writeableTrees t
                
-- | this function writes Xml with indention to a file
writeOMDocDTD::String->HXT.XmlTrees->String->IO HXT.XmlTrees
writeOMDocDTD dtd' t f = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_output_file, f)] $
    writeableTreesDTD dtd' t

hetsToOMDoc::HetcatsOpts->(ASL.LIB_NAME, LibEnv)->FilePath->IO ()
hetsToOMDoc hco lnle file =
  do
    ulw <- useLibWrite
    if ulw
      then
        -- libToOMDoc hco lnle file
        libToOMDocIdNameMapping hco lnle file
      else
        devGraphToOMDoc hco lnle file

-- | converts DevGraphs to OMDoc
-- depending on 'recurse'-option only the DevGraph specified by the libname
-- or all DevGraphs in libenv are written (to outdir)
-- uses OMDOC_DTD_URI environment variable for dtd or default dtd
devGraphToOMDoc::HetcatsOpts->(ASL.LIB_NAME, LibEnv)->FilePath->IO ()
devGraphToOMDoc hco (ln, le) file =
  do
    dtduri <- envDTDURI
    case (recurse hco) of
      False ->
        do
          omdoc <- devGraphToOMDocCMPIOXN
            (emptyGlobalOptions { hetsOpts = hco })
            (devGraph $ Map.findWithDefault (error "?") ln le)
            (show ln)
          writeOMDocDTD dtduri omdoc file
          return ()
      True ->
        let
          dg = (devGraph $ Map.findWithDefault (error "?") ln le)
          igdg = libEnvToDGraphG (ln, dg, le)
        in
          do
            xmlg <- dGraphGToXmlGXN igdg
            writeXmlG hco dtduri xmlg
            return ()
    return ()
								
libToOMDoc::HetcatsOpts->(ASL.LIB_NAME, LibEnv)->FilePath->IO ()
libToOMDoc hco (ln, le) file =
  let
    xtagle = xmlTagLibEnv emptyGlobalOptions le
  in
    case (recurse hco) of
      False ->
        libToOMDocCMPIOXN
          (emptyGlobalOptions { hetsOpts = hco })
          le
          xtagle
          ln
          (show ln)
        >>= \omdoc -> writeOMDocDTD defaultDTDURI omdoc file >> return ()
      True ->
        let
          dg = (devGraph $ Map.findWithDefault (error "?") ln le)
          igdg = libEnvXToDGraphG (ln, dg, le)
        in
          do
            xmlg <- dGraphGXLEToXmlGXN igdg le xtagle
            writeXmlG hco defaultDTDURI xmlg >> return ()

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

-- | Convert a DevGraph to OMDoc-XML with given xml:id attribute
-- will also scan used (CASL-)files for CMP-generation
devGraphToOMDocCMPIOXN::GlobalOptions->Static.DevGraph.DGraph->String->IO HXT.XmlTrees
devGraphToOMDocCMPIOXN go dg name' =
  do
    dgx <- devGraphToXmlCMPIOXmlNamed go dg
    return
      (
        (HXT.etag "omdoc" += ( qualattr omdocNameXMLNS omdocNameXMLAttr name'
          +++ xmlNL +++ dgx )) emptyRoot
      )

libToOMDocCMPIOXN::GlobalOptions->Static.DevGraph.LibEnv->XmlTaggedLibEnv->ASL.LIB_NAME->String->IO HXT.XmlTrees
libToOMDocCMPIOXN go lenv xtagln ln name' =
  do
    dgx <- libToXmlCMPIOXmlNamed go lenv xtagln ln
    return
      (
        (HXT.etag "omdoc" += ( qualattr omdocNameXMLNS omdocNameXMLAttr name'
          +++ xmlNL +++ dgx )) emptyRoot
      )


-- | Converts a map mapping to a Container-type (e.g. Set) to a list of
-- key,value-tuples for every element in the container and the corresponding key
mapToSetToTupelList::(Container c b)=>Map.Map a c->[(a,b)]
mapToSetToTupelList mapping =
  foldl (\l (a, s) ->
    foldl (\l' i ->
      l' ++ [(a, i)]
      ) l (getItems s)
    ) [] (Map.toList mapping)
                
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
                
-- debugging function
showSensWOMap::Map.Map a (Set.Set Hets.SentenceWO)->String
showSensWOMap mapping =
  let
    senssets = Map.elems mapping
    senslist = concatMap Set.toList senssets
    sennames = map (Ann.senName . Hets.woItem) senslist
  in
    implode ", " sennames

{-
  To create consistent xml-names the whole libenv has to be processed
  so that references to other libraries use the correct names.
  this implies to process the libenv with respect to references.

  this functionality is currently experimental
-}
type XmlNamedWONSorts = Set.Set XmlNamedWONSORT
type XmlNamedWONRels = Rel.Rel XmlNamedWONSORT
type XmlNamedWONPreds = Set.Set (XmlNamedWONId, PredTypeXNWON)
type XmlNamedWONOps = Set.Set (XmlNamedWONId, OpTypeXNWON)


-- this seems to swallow some symbols that should be preserved...
correctXmlNames ::
  XmlTaggedLibEnv
  -> -- possible wrong-named mapping
  XmlTaggedDevGraph
  -> -- imports from mappings
    [(ASL.LIB_NAME, NODE_NAME, XmlNamed Hets.NODE_NAMEWO)]
  -> -- corrected mapping
  XmlTaggedDevGraph
correctXmlNames cm wm im =
  foldl
    (\pwm (ln, nn, {-xnnnwo-} _) ->
      let
        cmap = case Map.lookup ln cm of
          Nothing -> error ("Cannot process import from unprocessed DG!")
          (Just x) -> x
        ({-xnsourcenodewo-} _, (xnsorts, _, xnrels, xnpreds, xnops, _)) =
          case
            Map.toList $ Map.filterWithKey
              (\xnw _ -> (Hets.wonItem $ xnItem xnw) == nn)
              cmap of
            [] -> error ("SourceNode not found for \"" ++ show nn ++ "\"!")
            [i] -> i
            (i:_) ->
              Debug.Trace.trace
                ("Confused: more than one matching node for \"" ++ show nn ++ "\"!")
                i
        --originInTarget = Hets.wonOrigin $ xnItem xnnnwo
        xnsortslist = Set.toList xnsorts
        xnrelslist = Rel.toList xnrels
      in
        Map.map
          (\(pwms,ms,{-pwmr-} _, pwmp, pwmo, pwme) ->
            (
                Set.map
                  (correctItem
                    xnsortslist
                    (==)
                  )
                  pwms
              ,  ms
              ,  Rel.fromList
                   (
                    map
                      (\(a,b) -> (correctItem xnsortslist (==) a, correctItem xnsortslist (==) b))
                      xnrelslist
                   )
              , map
                  (
                  correctComplexItem
                    xnpreds
                    (==)
                  )
                  pwmp
              , map
                  (
                  correctComplexItem
                    xnops
                    (==)
                  )
                  pwmo
              ,
                pwme
            )
          )
          pwm
    )
    wm
    im
  where
  correctItem:: forall a b .
    [XmlNamed a]
    ->(b->a->Bool)
    ->XmlNamed b
    ->XmlNamed b
  correctItem
    reference
    match
    tobecorrected =
      case find (match (xnItem tobecorrected) . xnItem) reference of
        Nothing -> tobecorrected
        (Just amatch) -> tobecorrected { xnName = xnName amatch }

  correctComplexItem:: forall a b c .
    [(XmlNamed a, c)]
    ->((b,c)->(a,c)->Bool)
    ->(XmlNamed b, c)
    ->(XmlNamed b, c)
  correctComplexItem
    reference
    match
    (tobecorrected@(xtb, tbc)) =
      case find (\(xa, ac) -> match (xnItem xtb, tbc) (xnItem xa, ac)) reference of
        Nothing -> tobecorrected
        (Just (xmatch, _)) -> (xtb { xnName = xnName xmatch }, tbc)

{-  correctList::forall a b .
      [XmlNamed a]
    ->(b->a->Bool)
    ->[XmlNamed b]
    ->[XmlNamed b]
  correctList
    reference
    match
    tobecorrected =
    map
      (correctItem reference match)
      tobecorrected-}

createXmlNameMap::Static.DevGraph.DGraph->XmlTaggedDevGraph
createXmlNameMap dg =
  let
    (onlynodenameset, onlyrefnameset) =
      Hets.getNodeDGNamesNodeRef dg
    (onlynodexmlnamelist, xmlnames_onxnl) =
      createXmlNames
        nodeTupelToNodeName
        []
        (Set.toList onlynodenameset)
    (onlyrefxmlnamelist, xmlnames_orxnl) =
      createXmlNames
        nodeTupelToNodeName
        xmlnames_onxnl
        (Set.toList onlyrefnameset)
    nodexmlnameset = Set.fromList (onlynodexmlnamelist ++ onlyrefxmlnamelist)
    sortswomap = Hets.getSortsWOWithNodeDGNamesWO dg
    sortswomorphmap = Hets.getSortsWOMorphWithNodeDGNamesWO dg
    relswomap= Hets.getRelationsWOWithNodeDGNamesWOSMDGWO dg sortswomap
    predswomap = Map.map mapToSetToTupelList $ Hets.getPredMapsWOWithNodeDGNamesWO dg
    opswomap = Map.map mapToSetToTupelList $ Hets.getOpMapsWOWithNodeDGNamesWO dg
    senswomap = Hets.getSentencesWOWithNodeDGNamesWO dg
    -- sorts
    -- processSubContents was not build for this, so this is a bit clumsy...
    (xmlnamedsortswomap, _) =
      processSubContents 
        (\_ kswol ->
          (
            map
              (\(k, swo) ->
                (k, XmlNamed
                      swo
                      (createUniqueName
                        xmlnames_orxnl
                        (adjustStringForXmlName $ show $ Hets.woItem swo)
                      )
                )
              )
              kswol
            , undefined
          )
        )
        undefined
        sortswomap
    -- rels
    xmlnamedrelswomap =
      foldl
        (\relmap' theory ->
          let
            theorysorts = Map.findWithDefault Set.empty theory xmlnamedsortswomap
          in
            Map.insert
              theory
              (Rel.fromList
                (map (\(a,b) ->
                  let
                    a' = case Set.toList (Set.filter (\i -> (xnItem i) == a) theorysorts) of
                      [] -> error "No such sort in theory..."
                      (i:_) -> XmlNamed a (xnName i)
                    b' = case Set.toList (Set.filter (\i -> (xnItem i) == b) theorysorts) of
                      [] -> error "No such sort in theory..."
                      (i:_) -> XmlNamed b (xnName i)
                  in
                    (a' , b' )
                  ) (Rel.toList (Map.findWithDefault Rel.empty theory relswomap))))
              relmap' 
        )
        Map.empty
        (Map.keys relswomap)
    -- predicates
    (xmlnamedpredswomap, xmlnames_pm) =
      (processSubContents
        (\xmlnames c -> uniqueXmlNamesContainerWONExt
          xmlnames
          show
          c
          (pSCStrip (\(pidwo,_) -> pidwo))
          (\(k, (pidwo, pset)) xname -> (k, (XmlNamed pidwo xname, pset)))
        )
        []
        predswomap)::(Map.Map Hets.NODE_NAMEWO [(XmlNamedWONId, PredType)], XmlNameList)
        --predswomap)::(Map.Map Hets.NODE_NAMEWO (Map.Map (XmlNamed Hets.IdWO) (Set.Set PredType)), XmlNameList)
    -- operators
    (xmlnamedopswomap, {-xmlnames_om-} _) =
      (processSubContents
        (\xmlnames c ->
          uniqueXmlNamesContainerWONExt
            xmlnames
            show
            c
            (pSCStrip (\(oidwo,_) -> oidwo))
            (\(k,(oidwo,oset)) xname -> (k, (XmlNamed oidwo xname, oset)))
        )
        xmlnames_pm
        opswomap)::(Map.Map Hets.NODE_NAMEWO [(XmlNamedWONId, OpType)], XmlNameList)
    -- sentences
    (xmlnamedsenswomap, {-xmlnames_senm-} _) =
      (processSubContents
        (\xmlnames nsensset ->
          uniqueXmlNamesContainerWONExt
            xmlnames
            (\x -> Ann.senName x)
            nsensset
            (pSCStrip id)
            (\(k, senswo) xname -> (k, XmlNamed senswo xname))
        )
        [] --xmlnames_om
        senswomap)::(Map.Map Hets.NODE_NAMEWO (Set.Set (XmlNamed Hets.SentenceWO)), XmlNameList)
    xnwonames =
      map
        (\xn ->
          let
            (nnum, nnam) = xnItem xn
          in
            XmlNamed (Hets.mkWON nnam nnum) (xnName xn)
        )
        (Set.toList nodexmlnameset)
        
  in
    Map.fromList $
      map
        (\nx ->
          let
            sorts = case Map.lookup (xnItem nx) xmlnamedsortswomap of
              Nothing -> Set.empty
              (Just s) -> s
            msorts =
              case
                find (\(o, _) -> Hets.woOrigin o == (xnWOaToO nx))
                  $ Map.toList sortswomorphmap
              of
                Nothing -> Set.empty
                (Just (_,ms')) -> ms'
            rels = case Map.lookup (xnItem nx) xmlnamedrelswomap of
              Nothing -> Rel.empty
              (Just r) -> r
            preds = case Map.lookup (xnItem nx) xmlnamedpredswomap of
              Nothing -> []
              (Just p) -> p
            ops = case Map.lookup (xnItem nx) xmlnamedopswomap of
              Nothing -> []
              (Just o) -> o
            sens = case Map.lookup (xnItem nx) xmlnamedsenswomap of
              Nothing -> []
              (Just s) -> (Set.toList s)
          in
            (nx, (sorts, msorts, rels, preds, ops, sens))
        )
        xnwonames
  where
  nodeTupelToNodeName::(a, NODE_NAME)->String
  nodeTupelToNodeName = nodeToNodeName . snd
  nodeToNodeName::NODE_NAME->String
  nodeToNodeName =
    (\nn ->
      let
        nodename = showName nn
      in
        if (length nodename) == 0
          then
            "AnonNode_"
          else
            nodename
    )

{-
 assuming unique names in a list of 'IdNameMapping'S each id (String) is
 converted to an xml:id-conform string by replacing invalid characters
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

{-
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


{-
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

{-
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
                o:_ -> Debug.Trace.trace ("more than one origin for Sort \"" ++ show oname ++ "\"...") o
            norigin =
              case
                Hets.getNameOrigins uniqueNames nname
              of
                [] -> error "!"
                n:[] -> n
                n:_ -> Debug.Trace.trace ("more than one origin for Sort \"" ++ show nname ++ "\"...") n
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
                o:_ -> Debug.Trace.trace ("more than one origin for Pred \"" ++ show oname ++ "\"...") o
            norigin =
              case
                Hets.getNameOrigins uniqueNames nname
              of
                [] -> error "!"
                n:[] -> n
                n:_ -> Debug.Trace.trace ("more than one origin for Pred \"" ++ show nname ++ "\"...") n
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
                o:_ -> Debug.Trace.trace ("more than one origin for Op \"" ++ show oname ++ "\"...") o
            norigin =
              case
                Hets.getNameOrigins uniqueNames nname
              of
                [] -> error "!"
                n:[] -> n
                n:_ -> Debug.Trace.trace ("more than one origin for Op \"" ++ show nname ++ "\"...") n
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
    

{-
  filter definitional links (LocalDef, GlobalDef, HidingDef, FreeDef, CofreeDef)
-}
filterDefLinks::[Graph.LEdge Static.DevGraph.DGLinkLab]->[Graph.LEdge Static.DevGraph.DGLinkLab]
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

{-
  filter theorem links (LocalThm, GlobalThm, HidingThm)
-}
filterThmLinks::[Graph.LEdge Static.DevGraph.DGLinkLab]->[Graph.LEdge Static.DevGraph.DGLinkLab]
filterThmLinks =
  filter
    (\(_, _, ll) ->
      case dgl_type ll of
        (LocalThm {}) -> True
        (GlobalThm {}) -> True
        (HidingThm {}) -> True
        _ -> False
    )

filterSORTConstructors::Set.Set (OpType, String)->SORT->Set.Set (OpType, String)
filterSORTConstructors
  conset
  s
  =
  Set.filter
    (\(ot, _) -> opRes ot == s )
    conset

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
    
emptyRelForSort::Rel.Rel SORT->SORT->Bool
emptyRelForSort rel s =
  null $ filter (\(s', _) -> s' == s) $ Rel.toList rel

createInsortFor::Rel.Rel SORT->SORT->Hets.IdNameMapping->HXT.XmlFilter->HXT.XmlFilter
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
  
-- | Convert a DevGraph to OMDoc-XML with given xml:id attribute
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

getNodeNameForXml::Hets.IdNameMapping->Hets.LIB_NAME->String
getNodeNameForXml inm ln =
  (
  if Hets.inmGetLibName inm /= ln
    then
      asOMDocFile $ unwrapLinkSource $ (Hets.inmGetLibName inm)
    else
      ""
  ) ++ Hets.inmGetNodeId inm
  

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
{-      currentmapping =
        fromMaybe
          (error ("No such mapping!"))
          (Hets.getLNGN fullNames ln nn) -}
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
{-      currentmapping =
        fromMaybe
          (error ("No such mapping!"))
          (Hets.getLNGN fullNames ln nn) -}
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

-- renaming should be done by 1) create names/origins for DGs but remember where
-- imports occured and 2) correct xml-names via import-information (and 
-- benefit from the unambigous xml-naming/origin-information)
xmlTagLibEnv::
  GlobalOptions
  ->Static.DevGraph.LibEnv
  ->XmlTaggedLibEnv
xmlTagLibEnv _ libenv =
  let
    libnames = Map.keys libenv
{-    (libsWithNoRefs, libsWithRefs) =
      foldl
        (\(lwnr, lwr) ln ->
          case Map.lookup ln libenv of
            Nothing -> error ("No GlobalContext for \"" ++ show ln ++ "\"!")
            (Just gc) ->
              let
                dg = Static.DevGraph.devGraph gc
              in
                if any (\(_,dgnl) -> Static.DevGraph.isDGRef dgnl) $ Graph.labNodes dg
                  then
                    (lwnr, lwr++[ln])
                  else
                    (lwnr++[ln], lwr)
        )
        ([],[])
        libnames
-}
    basicNameAndImportMap =
      foldl
        (\bNM ln ->
         case Map.lookup ln libenv of
          Nothing -> error ("No GlobalContext for \"" ++ show ln ++ "\"!")
          (Just gc) ->
            let
              dg = Static.DevGraph.devGraph gc
              refs =
                filter
                  (\(_,dgnl) -> Static.DevGraph.isDGRef dgnl)
                  (Graph.labNodes dg)
              reflookup =
                map
                  (\(nn,DGRef { dgn_node = lnn, dgn_libname = lln  }) ->
                    case Map.lookup lln libenv of
                      Nothing -> error ("No GlobalContext for \"" ++ show lln ++ "\"!")
                      (Just lgc) ->
                        case Graph.lab (Static.DevGraph.devGraph lgc) lnn of
                          Nothing -> error ("No such node in \"" ++ show lln ++ "\" : " ++ show lnn)
                          (Just anode) -> (nn, lln, dgn_name anode)  
                  )
                  refs
              xmlnamemap = createXmlNameMap dg
              imports =
                map
                  (\(nn, iln, inname) ->
                    case filter (\k -> (==) nn $ Hets.wonOrigin $ xnItem k) $ Map.keys xmlnamemap of
                      [] -> error ("Importing node is not in the map!")
                      [i] -> (iln, inname, i)
                      (i:_) ->
                        Debug.Trace.trace
                          ("Confused: more than one matching node for import!")
                          (iln, inname, i)
                  ) 
                  reflookup
            in
              Map.insert ln (xmlnamemap, imports) bNM
        )
        Map.empty
        libnames
    (initialCorrectI, initialIncorrect) =
      Map.partition
        (null . snd)
        basicNameAndImportMap
    initialCorrect = Map.map fst initialCorrectI
    (correctMap, _) =
      until
        (Map.null . snd)
        (\(cm, icm) ->
          let
            correctlibs = Map.keys cm
            candidatemap =
              Map.filter
                (\(_,imports) ->
                  all
                    (\(iln,_,_) -> elem iln correctlibs)
                    imports
                )
                icm
            (cln, (cmap, cimps)) = head $ Map.toList candidatemap 
            corrected = correctXmlNames cm cmap cimps
          in
            if Map.null candidatemap
              then
                error ("Cannot correct names! (Must be cyclic import or missing library)")
              else
                (Map.insert cln corrected cm, Map.delete cln icm) 
        )
        (initialCorrect, initialIncorrect)
  in
    correctMap

usedXTNames::XmlTaggedLibEnv->[XmlName]
usedXTNames xtagln =
  let
    liblist = Map.toList xtagln
    taggeddgs = map snd liblist
    namedmaps = map snd (concatMap Map.toList taggeddgs)
    names =
      map
        (\(ss,_,_,pl,ol,el) ->
          (map xnName (Set.toList ss))
            ++ map (xnName . fst) pl
            ++ map (xnName . fst) ol
            ++ map xnName el
        )
        namedmaps
  in
    concat names


{-
  symbols are filtered to restrictive... (abs::Int->Nat, abs::Rat->Rat...)
-}
libToXmlCMPIOXmlNamed::
  GlobalOptions
  ->Static.DevGraph.LibEnv
  ->XmlTaggedLibEnv
  ->ASL.LIB_NAME
  ->IO (HXT.XmlTree->HXT.XmlTrees)
libToXmlCMPIOXmlNamed go lenv xmlnamemap ln =
  let
    dg = case Map.lookup ln lenv of
      Nothing -> error ("No such library in LibEnv : " ++ show ln)
      (Just gc) -> Static.DevGraph.devGraph gc
    (onlynodenameset, onlyrefnameset) = Hets.getNodeDGNamesNodeRef dg
    (onlynodexmlnamelist, xmlnames_onxnl) = createXmlNames nodeTupelToNodeName [] (Set.toList onlynodenameset)
    (onlyrefxmlnamelist, {-xmlnames_orxnl-} _) = createXmlNames nodeTupelToNodeName xmlnames_onxnl (Set.toList onlyrefnameset)
    nodexmlnameset = Set.fromList (onlynodexmlnamelist ++ onlyrefxmlnamelist)
    
    inputmapwofull = Hets.getNodeAllImportsNodeDGNamesWOLL dg 
{-    importsmapwo =
      Map.map
        (\inputlist ->
          Set.fromList $
            map (\(a,_,b) -> (a,b)) $
            filter (\(_, mll, _) ->
              case mll of
                Nothing -> True
                (Just ll) ->
                  case Static.DevGraph.dgl_type ll of
                    Static.DevGraph.LocalDef -> True
                    Static.DevGraph.GlobalDef -> True
                    _ -> False
              )
              inputlist
        )
        inputmapwofull 
  -}  
    xmlNamedSymbolsWOMap = Map.findWithDefault Map.empty ln xmlnamemap
    
  in
    foldl (\xio xnodetupel ->
      let
        theoname = xnName xnodetupel
        (nodenum, nodename) = xnItem xnodetupel
        (theosorts, theomorphsorts, theorels, theopreds, theoops, theosens) =
          (\(a,b,c,d,e,f) -> (Set.toList a, Set.toList b, c, d, e, f)) $
          Map.findWithDefault
            (Set.empty, Set.empty, Rel.empty, [], [], [])
            (XmlNamed (Hets.mkWON nodename nodenum) theoname)
            xmlNamedSymbolsWOMap
--        realsorts = filter (\i -> (xnWOaToO i) == nodenum) theosorts
        realsorts =
          filter
            (\i -> 
              let
                thisorigin = xnWOaToO i
                morphorigin =
                  case
                    find (\ms -> (xnWOaToa i) == (Hets.woItem ms)) theomorphsorts
                  of
                    Nothing ->
                      Debug.Trace.trace
                        ("Thats funny. No morphing origin for \"" ++ show i ++ "\" in " ++ show theomorphsorts)
                        thisorigin
                    (Just ms) -> Hets.wonOrigin ms
              in
                (thisorigin == nodenum) && (thisorigin == morphorigin)
            )
            theosorts 
        --realsortswo = map xnItem realsorts
        realrels = Rel.fromList $ filter (\(a,b) ->
          (elem a realsorts) || (elem b realsorts)
          ) (Rel.toList theorels)
        insorts = Rel.transpose realrels
        insortmap =
          foldl (\m (a,b) ->
            Map.insert
              a
              (Set.insert b (Map.findWithDefault Set.empty a m))
              m
            ) Map.empty (Rel.toList insorts)
        tinputs = Map.findWithDefault
          []
          (Hets.mkWON nodename nodenum)
          inputmapwofull
        inputsxn = map
          (\(inodenamewo, mll, _) ->
            let
              ((itheonum, itheoname), itheoxmlname) = case find (\x -> (fst (xnItem x)) == (Hets.woOrigin inodenamewo)) (Set.toList nodexmlnameset) of
                Nothing -> error "Unknown Origin of Morphism!"
                (Just x) -> (xnItem x, xnName x)
              (itheosorts, _, _, itheopreds, itheoops, _) =
                (\(a,b,c,d,e,f) -> (Set.toList a, b, c, d, e, f)) $
                  Map.findWithDefault
                    (Set.empty, Set.empty, Rel.empty, [], [], [])
                    (XmlNamed (Hets.mkWON itheoname itheonum) itheoxmlname)
                    xmlNamedSymbolsWOMap
              mmapandset =
                let
                  (caslmorph, isHiding) = case mll of
                    Nothing -> (Hets.emptyCASLMorphism, False)
                    (Just ll) ->
                      (
                          Hets.getCASLMorph (undefined, undefined, ll)
                        , case (dgl_type ll) of
                          (Static.DevGraph.HidingDef {}) -> True
                          (Static.DevGraph.HidingThm {}) -> True
                          _ -> False
                      )
                  ((asm, apm, aom), ahid) =
                    createMorphismMapAndHiding
                      caslmorph
                      isHiding
                      itheosorts
                      itheopreds
                      itheoops
                      theosorts
                      theopreds
                      theoops
                  xnnamemap =
                    Map.fromList
                      (
                      map
                        (\(a, b) -> (xnName a, xnName b) ) 
                        (
                          (Map.toList asm)
                          ++ (Map.toList apm)
                          ++ (Map.toList aom)
                        )
                      )
                  xnnameset = Set.fromList $ map xnName $ fromMaybe [] ahid
                in
                  if (Map.null xnnamemap) && (Set.null xnnameset)
                    then
                      Nothing
                    else
                      Just (xnnamemap, xnnameset)
            in
              (itheoxmlname, mll, mmapandset)
          )
          tinputs
        importsxn =
            filter (\(_,mll,_) ->
              case mll of
                Nothing -> True
                (Just ll) ->
                  case Static.DevGraph.dgl_type ll of
                    Static.DevGraph.GlobalDef -> True
                    Static.DevGraph.LocalDef -> True
                    Static.DevGraph.HidingDef -> True
                    (Static.DevGraph.FreeDef {}) -> True
                    (Static.DevGraph.CofreeDef {}) -> True
                    _ -> False
              )
              inputsxn
        glThmLinksxn =
            filter (\(_,mll,_) ->
              case mll of
                Nothing -> False
                (Just ll) ->
                  case Static.DevGraph.dgl_type ll of
                    (Static.DevGraph.GlobalThm _ _ _) -> True
                    (Static.DevGraph.LocalThm _ _ _) -> True
                    _ -> False
              )
              inputsxn
        realtheopreds = filter (\(idxnwon, _) -> (xnWOaToO idxnwon) == nodenum) theopreds
        realtheoops = filter (\(idxnwon, _) -> (xnWOaToO idxnwon) == nodenum) theoops
        
        realtheosens = filter (\i -> (xnWOaToO i) == nodenum) theosens
        
        (axiomxn, sortgenxn) = partitionSensSortGenXN realtheosens
        
        (constructors, _) = makeConstructorsXN theosorts (usedXTNames xmlnamemap) sortgenxn
        
        adtsorts = Map.keys insortmap ++ (map (\(a,_) -> a) (Map.toList constructors))
        
        theopredsxn = map (\(k,p) -> (k, predTypeToPredTypeXNWON theosorts p)) theopreds
        theoopsxn = map (\(k,op) -> (k, opTypeToOpTypeXNWON theosorts op)) theoops
        
        sensxmlio =
          wrapFormulasCMPIOXN
            (PFInput
              {
                  pfiGO = go
                , theorySet = nodexmlnameset
                , theorySorts = (Set.fromList theosorts)
                , theoryRel = theorels
                , theoryPreds = theopredsxn
                , theoryOps = theoopsxn
                , debugInfo = (show (nodename, nodenum))
              }
            )
            axiomxn 
      in
        do
          x <- xio
          sensxml <- sensxmlio
          return $ (x +++ xmlNL +++ HXT.etag "theory" += (
            (qualattr "xml" "id" theoname) +++
            -- presentation
            makePresentationFor
              theoname
              (Hets.idToString $ Hets.nodeNameToId (snd (xnItem xnodetupel))) +++
            xmlNL +++
            -- imports/morphisms
            (foldl (\x' (nodenamex , mll,  mmm) ->
              let
                isglobal = case mll of
                  (Just ll) -> case Static.DevGraph.dgl_type ll of
                    (Static.DevGraph.LocalDef) -> False
                    _ -> True
                  _ -> True
                refs = filter (\(_, node) -> isDGRef node) $ Graph.labNodes dg
                isexternal = find (\xref -> (xnName xref) == nodenamex) onlyrefxmlnamelist
                liburl = case isexternal of
                  (Just xnode) ->
                    case find (\(_, node) -> (dgn_name node) == (snd (xnItem xnode))) refs of
                      Nothing ->
                        "unknown"
                      (Just (_, node)) -> 
                        (asOMDocFile (unwrapLinkSource $ dgn_libname node))
                  _ ->
                    ""
              in
                x' +++
                HXT.etag "imports" += (
                  (
                    qualattr
                      "xml"
                      "id"
                      (
                        (if isglobal then "ig" else "il")
                        ++ "." ++ theoname ++ "." ++ nodenamex
                      )
                    +++ HXT.sattr "from" (liburl++"#" ++ nodenamex)
                    +++ (if isglobal then xmlNullFilter else HXT.sattr "type" "local")
                  ) +++
                  (
                    case mmm of
                      (Just (sm, hs)) -> morphismMapToXmlXN sm hs nodenamex theoname
                      Nothing -> xmlNullFilter
                  )
                ) +++
                xmlNL
              ) (xmlNullFilter) importsxn 
            ) +++
            -- sorts
            (foldl (\x' xnwos ->
              x' +++
              (sortToXmlXN (xnWOaToXNa xnwos)) +++
              xmlNL +++
              makePresentationFor
                (xnName xnwos)
                (Hets.idToString (xnWOaToa xnwos)) +++
              xmlNL
              ) xmlNL realsorts) +++
            -- adts
            {- 
               no presentation needed for adts as they are 
               generated from a) relations and b) sentences.
               relations have their presentation via sort-definition
               and sentences get their own presentation tags.
            -}
            (foldl (\x' sortx ->
              let
                insortsetx = Map.findWithDefault Set.empty sortx insortmap
                constructorx = createAllConstructorsXN nodexmlnameset $ Map.toList $ Map.findWithDefault Map.empty sortx constructors
              in
                x' +++ createADTXN (xnWOaToXNa sortx, Set.map xnWOaToXNa insortsetx) constructorx +++ xmlNL
              ) xmlNL adtsorts) +++ 
            -- predicates
            (foldl
              (\x' (pxnid, p) ->
                let
                  px = predTypeToPredTypeXNWON theosorts p 
                in
                  x' +++
                  predicationToXmlXN
                    nodexmlnameset
                    (pxnid, px) +++
                  xmlNL +++
                  makePresentationFor
                    (xnName pxnid)
                    (Hets.idToString $ xnWOaToa pxnid) +++
                  xmlNL
              )
              (xmlNullFilter)
              realtheopreds
            ) +++
            -- operators
            (foldl
              (\x' (oxnid, op) ->
                let
                  ox = opTypeToOpTypeXNWON theosorts op 
                in
                  x' +++ 
                  operatorToXmlXN
                    nodexmlnameset
                    (oxnid, ox) +++
                  xmlNL +++
                  makePresentationFor
                    (xnName oxnid)
                    (Hets.idToString $ xnWOaToa oxnid) +++
                  xmlNL
              )
              (xmlNullFilter)
              realtheoops
            ) +++
            -- sentences
            sensxml
            )
            -- this constructs Hets-internal links as private data (but uses xmlnames for reference)
            +++ xmlNL +++ (inDGToXmlXN dg nodenum nodexmlnameset) +++ xmlNL 
            +++
              (foldl (\xml (fromxn, mll, mmm) ->
                let
                  tagname =
                    case mll of
                      Nothing -> error "corrupt data"
                      (Just ll) ->
                        case Static.DevGraph.dgl_type ll of
                          (Static.DevGraph.GlobalThm _ _ _) -> theoryInclusionS
                          (Static.DevGraph.LocalThm _ _ _) -> axiomInclusionS
                          _ -> error "corrupt data"
                  consattr =
                    case mll of
                      Nothing -> error "corrupt data"
                      (Just ll) ->
                        case Static.DevGraph.dgl_type ll of
                          (Static.DevGraph.GlobalThm _ c _) -> consAttr c
                          (Static.DevGraph.LocalThm _ c _) -> consAttr c
                          _ -> error "corrupt data"
                          
                in
                  xml +++ xmlNL +++
                    HXT.etag tagname += (
                      qualattr
                        "xml"
                        "id"
                        ( (if tagname == axiomInclusionS then "ai" else "ti")
                          ++ "." ++ theoname ++ "." ++ fromxn
                        )
                      +++ HXT.sattr "from" ("#"++fromxn) 
                      +++ HXT.sattr "to" ("#" ++ theoname)
                      +++ consattr
                      +++ case mmm of
                        Nothing -> xmlNullFilter
                        (Just (sm,hs)) -> morphismMapToXmlXN sm hs fromxn theoname
                      )
                )
                (xmlNullFilter)
                glThmLinksxn)
              )
              -- when constructing the catalogues a reference to the xmlname used in _this_ document is used
              -- it is very likely possible, that this theory has another name in real life (unless there are no name-collisions)
  -- catalogue-support is gone...
  --    ) (return $ refsToCatalogueXN dg nodexmlnameset +++ xmlNL) onlynodexmlnamelist 
      ) (return $ (xmlNullFilter)) onlynodexmlnamelist 
    where
    nodeTupelToNodeName::(a, NODE_NAME)->String
    nodeTupelToNodeName = nodeToNodeName . snd
    nodeToNodeName::NODE_NAME->String
    nodeToNodeName =
      (\nn ->
        let
          nodename = showName nn
        in
          if (length nodename) == 0
            then
              "AnonNode_"
            else
              nodename
      )
    consAttr::Static.DevGraph.Conservativity->HXT.XmlFilter
    consAttr Static.DevGraph.None = xmlNullFilter
    consAttr Static.DevGraph.Mono = HXT.sattr "conservativity" "monomorphism"
    consAttr Static.DevGraph.Cons = HXT.sattr "conservativity" "conservative"
    consAttr Static.DevGraph.Def = HXT.sattr "conservativity" "definitional"

    createMorphismMapAndHiding::
      Morphism.Morphism () () ()
      ->Bool
      ->[XmlNamedWONSORT]
      ->[(XmlNamedWONId, PredType)]
      ->[(XmlNamedWONId, OpType)]
      ->[XmlNamedWONSORT]
      ->[(XmlNamedWONId, PredType)]
      ->[(XmlNamedWONId, OpType)]
      ->(
         (Map.Map XmlNamedWONSORT XmlNamedWONSORT
        , Map.Map XmlNamedWONId XmlNamedWONId
        , Map.Map XmlNamedWONId XmlNamedWONId)
        , Maybe [XmlNamedWONId]
        )
    createMorphismMapAndHiding
      caslmorph
      isHiding
      ssorts
      spreds
      sops
      tsorts
      tpreds
      tops =
      let
        adjmorph =
          adjustMorphismSymbols
            ssorts
            spreds
            sops
            tsorts
            tpreds
            tops
            caslmorph
        mhl =
          if isHiding
            then
              let
                hl =
                  checkHidden
                   adjmorph
                   ssorts -- source node is target in hiding morphism
                   spreds
                   sops 
                   tsorts -- target node is source in hiding morphism
                   tpreds
                   tops
              in
                case hl of
                  [] -> Nothing
                  _ -> Just hl
            else
              Nothing
      in
        (adjmorph, mhl)

-- create a representation of a morphism using xmlnamed symbols with their
-- origins
adjustMorphismSymbols::
  -- source
    [XmlNamedWONSORT]
  ->[(XmlNamedWONId, PredType)]
  ->[(XmlNamedWONId, OpType)]
  -- target
  ->[XmlNamedWONSORT]
  ->[(XmlNamedWONId, PredType)]
  ->[(XmlNamedWONId, OpType)]
  ->Morphism.Morphism () () ()
  ->(
      Map.Map XmlNamedWONSORT XmlNamedWONSORT
    , Map.Map XmlNamedWONId XmlNamedWONId
    , Map.Map XmlNamedWONId XmlNamedWONId
    )
adjustMorphismSymbols
  ssorts
  spreds
  sops
  tsorts
  tpreds
  tops
  m =
    let
      sortmap = Morphism.sort_map m
      predmap = Morphism.pred_map m
      opmap = Morphism.fun_map m
    in
--      Debug.Trace.trace ("Original Morphism : " ++ show sortmap)
      (
          Map.fromList
            $ map
              (\(a,b) -> (mapToXId ssorts a, mapToXId tsorts b))
              $ Map.toList sortmap
        , Map.fromList
            $ map
              (\((spid,spt),(tpid)) ->
                (
                    (mapTToXId spreds (==) (spid, spt))
                  , (mapTToXId tpreds (\_ _ -> True) (tpid, undefined::PredType))
                )
              )
              $ Map.toList predmap
        , Map.fromList
            $ map
              (\((soid,sot),(toid, tfk)) ->
                (
                    (mapTToXId sops (\pt tpt -> (tpt { opKind = opKind pt }) == pt ) (soid, sot))
                  , (mapTToXId tops (\ot tfk' -> (opKind ot) == tfk') (toid, tfk))
                )
              )
              $ Map.toList opmap

      )
  where
    mapToXId::[XmlNamedWONSORT]->SORT->XmlNamedWONSORT
    mapToXId l s =
      case find (\x -> (xnWOaToa x) == s ) l of
        (Just x) -> x
        Nothing -> error ("Symbol not found : " ++ show s ++ " in " ++ show l)
    mapTToXId::(Show a, Show b)=>[(XmlNamedWONSORT, a)]->(a->b->Bool)->(SORT, b)->XmlNamedWONSORT
    mapTToXId l check (s,b) =
      case find (\(x,a) -> ((xnWOaToa x) == s) && (check a b)) l of
        (Just (x,_)) -> x
        Nothing -> error ("Symbol not found : " ++ show (s,b) ++ " in " ++ show l)

checkHidden::
  (
      Map.Map XmlNamedWONSORT XmlNamedWONSORT
    , Map.Map XmlNamedWONId XmlNamedWONId
    , Map.Map XmlNamedWONId XmlNamedWONId
  )
  -- source
  ->[XmlNamedWONSORT]
  ->[(XmlNamedWONId, PredType)]
  ->[(XmlNamedWONId, OpType)]
  -- target
  ->[XmlNamedWONSORT]
  ->[(XmlNamedWONId, PredType)]
  ->[(XmlNamedWONId, OpType)]
  ->[XmlNamedWONId]
checkHidden
  (sortmap, predmap, opmap)
  ssorts
  spreds
  sops
  tsorts
  tpreds
  tops
  =
  let
    rsortmap = Map.fromList $ map (\(a,b) -> (b,a)) $ Map.toList sortmap
    rpredmap = Map.fromList $ map (\(a,b) -> (b,a)) $ Map.toList predmap
    ropmap = Map.fromList $ map (\(a,b) -> (b,a)) $ Map.toList opmap
    hiddensorts =
      foldl
        (\hs ts ->
          case Map.lookup ts rsortmap of
            Nothing -> 
              if elem ts hs
                then
                  delete ts hs
                else
                  hs
            (Just xs) -> delete xs hs
        )
        ssorts
        tsorts
    hiddenpreds =
      foldl
        (\hp (tp,_) ->
          case Map.lookup tp rpredmap of
            Nothing ->
              case lookup tp hp of
                Nothing -> hp
                _ -> filter (\(xhp,_) -> xhp /= tp) hp
            (Just xp) -> filter (\(xhp,_) -> xhp /= xp) hp
        )
        spreds
        tpreds
    hiddenops =
      foldl
        (\ho (to,_) ->
          case Map.lookup to ropmap of
            Nothing ->
              case lookup to ho of
                Nothing -> ho
                _ -> filter (\(xho,_) -> xho /= to) ho
            (Just xo) -> filter (\(xho,_) -> xho /= xo) ho
        )
        sops
        tops
  in
    (hiddensorts ++ (map fst hiddenpreds) ++ (map fst hiddenops))

{- |
        Converts a DevGraph into a Xml-structure (accessing used (CASL-)files 
        for CMP-generation)
-}
devGraphToXmlCMPIOXmlNamed::GlobalOptions->Static.DevGraph.DGraph->IO (HXT.XmlTree->HXT.XmlTrees)
devGraphToXmlCMPIOXmlNamed go dg =
  let
    (onlynodenameset, onlyrefnameset) = Hets.getNodeDGNamesNodeRef dg
    (onlynodexmlnamelist, xmlnames_onxnl) = createXmlNames nodeTupelToNodeName [] (Set.toList onlynodenameset)
    (onlyrefxmlnamelist, xmlnames_orxnl) = createXmlNames nodeTupelToNodeName xmlnames_onxnl (Set.toList onlyrefnameset)
    --nodenameset = Set.union onlynodenameset onlyrefnameset
    nodexmlnamelist = (onlynodexmlnamelist ++ onlyrefxmlnamelist)
    nodexmlnameset = Set.fromList nodexmlnamelist
    --nodenamemap = Map.fromList $ Set.toList nodenameset
    sortswomap = Hets.getSortsWOWithNodeDGNamesWO dg
    relswomap= Hets.getRelationsWOWithNodeDGNamesWOSMDGWO dg sortswomap
    predswomap = Map.map mapToSetToTupelList $ Hets.getPredMapsWOWithNodeDGNamesWO dg
    opswomap = Map.map mapToSetToTupelList $ Hets.getOpMapsWOWithNodeDGNamesWO dg
    senswomap = (\smap -> debugGO go "dGTXCMPIOXNsens" ("Sentences : " ++ (showSensWOMap smap)) smap) $ Hets.getSentencesWOWithNodeDGNamesWO dg
    -- importsmapwo = Hets.getNodeImportsNodeDGNamesWO dg
    inputmapwofull = Hets.getNodeAllImportsNodeDGNamesWOLL dg
    -- sorts
    -- (xmlnamedsortswomap, xmlnames_sm) =
    (xmlnamedsortswomap, _) =
      (processSubContents
        --(\xmlnames c -> uniqueXmlNamesContainerWONExt
        --  xmlnames
        (\_ c -> uniqueXmlNamesContainerWONExt
          []
          show
          c
          (pSCStrip id)
          (\(k, swo) xname -> (k,XmlNamed swo xname))
        )
        xmlnames_orxnl
        sortswomap)::(Map.Map Hets.NODE_NAMEWO (Set.Set (XmlNamed Hets.SORTWO)), XmlNameList)
    -- relations -- maybe not needed with xmlnames...
    --xmlnames_rm = xmlnames_sm
    xmlnamedrelswomap =
      foldl
        (\relmap' theory ->
          let
            theorysorts = Map.findWithDefault Set.empty theory xmlnamedsortswomap
          in
            Map.insert
              theory
              (Rel.fromList
                (map (\(a,b) ->
                  let
                    a' = case Set.toList (Set.filter (\i -> (xnItem i) == a) theorysorts) of
                      [] -> error "No such sort in theory..."
                      (i:_) -> XmlNamed a (xnName i)
                    b' = case Set.toList (Set.filter (\i -> (xnItem i) == b) theorysorts) of
                      [] -> error "No such sort in theory..."
                      (i:_) -> XmlNamed b (xnName i)
                  in
                    (a' , b' )
                  ) (Rel.toList (Map.findWithDefault Rel.empty theory relswomap))))
              relmap' 
        )
        Map.empty
        (Map.keys relswomap)
    -- predicates
    (xmlnamedpredswomap, xmlnames_pm) =
      (processSubContents
        (\xmlnames c -> uniqueXmlNamesContainerWONExt
          xmlnames
          show
          c
          (pSCStrip (\(pidwo,_) -> pidwo))
          (\(k, (pidwo, pset)) xname -> (k, (XmlNamed pidwo xname, pset)))
        )
        xmlnames_orxnl
        predswomap)::(Map.Map Hets.NODE_NAMEWO [(XmlNamedWONId, PredType)], XmlNameList)
        --predswomap)::(Map.Map Hets.NODE_NAMEWO (Map.Map (XmlNamed Hets.IdWO) (Set.Set PredType)), XmlNameList)
    -- operators
    (xmlnamedopswomap, xmlnames_om) =
      (processSubContents
        (\xmlnames c ->
          uniqueXmlNamesContainerWONExt
            xmlnames
            show
            c
            (pSCStrip (\(oidwo,_) -> oidwo))
            (\(k,(oidwo,oset)) xname -> (k, (XmlNamed oidwo xname, oset)))
        )
        xmlnames_pm
        
        opswomap)::(Map.Map Hets.NODE_NAMEWO [(XmlNamedWONId, OpType)], XmlNameList)
    --    opswomap)::(Map.Map Hets.NODE_NAMEWO (Map.Map (XmlNamed Hets.IdWO) (Set.Set OpType)), XmlNameList)
    -- sentences
    (xmlnamedsenswomap, xmlnames_senm) =
      (processSubContents
        (\xmlnames nsensset ->
          uniqueXmlNamesContainerWONExt
            xmlnames
            (\x -> debugGO go "dGTXCMPIOXN"  ("psc: " ++ (take 45 (show x))) $ Ann.senName x)
            nsensset
            (pSCStrip id)
            (\(k, senswo) xname -> (k, XmlNamed senswo xname))
        )
        xmlnames_om
        senswomap)::(Map.Map Hets.NODE_NAMEWO (Set.Set (XmlNamed Hets.SentenceWO)), XmlNameList)
  in
    foldl (\xio xnodetupel ->
      let
        theoname = xnName xnodetupel
        (nodenum, nodename) = xnItem xnodetupel
        theosorts = Map.findWithDefault Set.empty (Hets.mkWON nodename nodenum) xmlnamedsortswomap
        realsorts = Set.filter (\i -> (xnWOaToO i) == nodenum) theosorts
        realsortswo = Set.map (xnItem) (debugGO go "dGTXCMPIOXN" ("Sorts in " ++ (xnName xnodetupel) ++ " - " ++ (show realsorts) ) realsorts)
        theorels = Map.findWithDefault Rel.empty (Hets.mkWON nodename nodenum) relswomap
        theoxrels = Map.findWithDefault Rel.empty (Hets.mkWON nodename nodenum) xmlnamedrelswomap
        -- only keep relations that include at least one sort from the
        -- current theory
        realrels = Rel.fromList $ filter (\(a,b) ->
          (Set.member a realsortswo) || (Set.member b realsortswo)
          ) (Rel.toList theorels)
        insorts = Rel.transpose realrels 
        insortmap =
          foldl (\m (a,b) ->
            Map.insert
              a
              (Set.insert b (Map.findWithDefault Set.empty a m))
              m
            ) Map.empty (Rel.toList insorts)
        tinputs = Map.findWithDefault
          []
          (Hets.mkWON nodename nodenum)
          inputmapwofull
        inputsxn = map
          (\(inodenamewo, mll, _) ->
            let
              ((itheonum, itheoname), itheoxmlname) = case find (\x -> (fst (xnItem x)) == (Hets.woOrigin inodenamewo)) (Set.toList nodexmlnameset) of
                Nothing -> error "Unknown Origin of Morphism!"
                (Just x) -> (xnItem x, xnName x)
              itheosorts = Map.findWithDefault Set.empty (Hets.mkWON itheoname itheonum) xmlnamedsortswomap
              itheopreds = (Map.findWithDefault [] (Hets.mkWON itheoname itheonum) xmlnamedpredswomap)
              itheoops = (Map.findWithDefault [] (Hets.mkWON itheoname itheonum) xmlnamedopswomap)
              mmapandset =
                let
                  (caslmorph, isHiding) = case mll of
                    Nothing -> (Hets.emptyCASLMorphism, False)
                    (Just ll) ->
                      (
                          Hets.getCASLMorph (undefined, undefined, ll)
                        , case (dgl_type ll) of
                          (Static.DevGraph.HidingDef {}) -> True
                          (Static.DevGraph.HidingThm {}) -> True
                          _ -> False
                      )
                  ((asm, apm, aom), ahid) =
                    createMorphismMapAndHiding
                      caslmorph
                      isHiding
                      (Set.toList itheosorts)
                      itheopreds
                      itheoops
                      (Set.toList theosorts)
                      theopreds
                      theoops
                  xnnamemap =
                    Map.fromList
                      (
                      map
                        (\(a, b) -> (xnName a, xnName b) ) 
                        (
                          (Map.toList asm)
                          ++ (Map.toList apm)
                          ++ (Map.toList aom)
                        )
                      )
                  xnnameset = Set.fromList $ map xnName $ fromMaybe [] ahid
                in
                  if (Map.null xnnamemap) && (Set.null xnnameset)
                    then
                      Nothing
                    else
                      Just (xnnamemap, xnnameset)
            in
              (itheoxmlname, mll, mmapandset)
          )
          tinputs
        importsxn =
--          Set.fromList $ map (\(a,_,b) -> (a,b)) $
            filter (\(_,mll,_) ->
              case mll of
                Nothing -> True
                (Just ll) ->
                  case Static.DevGraph.dgl_type ll of
                    Static.DevGraph.GlobalDef -> True
                    Static.DevGraph.LocalDef -> True
                    Static.DevGraph.HidingDef -> True
                    (Static.DevGraph.FreeDef {}) -> True
                    (Static.DevGraph.CofreeDef {}) -> True
                    _ -> False
              )
              inputsxn
        glThmLinksxn =
            filter (\(_,mll,_) ->
              case mll of
                Nothing -> False
                (Just ll) ->
                  case Static.DevGraph.dgl_type ll of
                    (Static.DevGraph.GlobalThm _ _ _) -> True
                    (Static.DevGraph.LocalThm _ _ _) -> True
                    _ -> False
              )
              inputsxn
        theopreds = Map.findWithDefault [] (Hets.mkWON nodename nodenum) xmlnamedpredswomap
        realtheopreds = filter (\(idxnwon, _) -> (xnWOaToO idxnwon) == nodenum) theopreds
        theoops = (\x -> debugGO go "dGTXCMPIOXNo" ("Ops in \"" ++ (show nodename) ++ "\" : " ++ show x) x) $ Map.findWithDefault [] (Hets.mkWON nodename nodenum) xmlnamedopswomap
        realtheoops = filter (\(idxnwon, _) -> (xnWOaToO idxnwon) == nodenum) theoops
        theosens = Map.findWithDefault Set.empty (Hets.mkWON nodename nodenum) xmlnamedsenswomap
        realtheosens = Set.filter (\i -> (xnWOaToO i) == nodenum) theosens
        (axiomxn, sortgenxn) = partitionSensSortGenXN (Set.toList realtheosens)
--                              (constructors, xmlnames_cons)
        (constructors, _) = makeConstructorsXN (Set.toList theosorts) xmlnames_senm sortgenxn
        adtsorts = Map.keys insortmap ++ (map (\(a,_) -> xnItem a) (Map.toList constructors))
        --theoimports = Map.findWithDefault Set.empty nodename importsmap
        theopredsxn = map (\(k,p) -> (k, predTypeToPredTypeXNWON (Set.toList theosorts) p)) theopreds
        theoopsxn = map (\(k,op) -> (k, opTypeToOpTypeXNWON (Set.toList theosorts) op)) theoops
        sensxmlio =
          wrapFormulasCMPIOXN
            (PFInput
              {
                  pfiGO = go
                , theorySet = nodexmlnameset
                , theorySorts = theosorts
                , theoryRel = theoxrels
                , theoryPreds = theopredsxn
                , theoryOps = theoopsxn
                , debugInfo = (show (nodename, nodenum))
              }
            )
            axiomxn
{-        theorysymbols =
          (Set.toList theosorts)
          ++ (map fst theopreds)
          ++ (map fst theoops)
-}
      in
        do
          putStrLn ("Operators for " ++ show (nodename, nodenum) ++ " : " ++ show theoops ++ "\n")
          x <- xio
          sensxml <- sensxmlio
          return $ (x +++ xmlNL +++ HXT.etag "theory" += (
            (qualattr "xml" "id" theoname) +++
            -- presentation
            makePresentationFor
              theoname
              (Hets.idToString $ Hets.nodeNameToId (snd (xnItem xnodetupel))) +++
            xmlNL +++
            -- imports/morphisms
            -- I still need to find a way of modelling Hets-libraries
            -- in OMDoc-Imports...
  --                                      (foldl (\x' (nodename' , mmm) ->
            (foldl (\x' (nodenamex , mll,  mmm) ->
              let
                isglobal = case mll of
                  (Just ll) -> case Static.DevGraph.dgl_type ll of
                    (Static.DevGraph.LocalDef) -> False
                    _ -> True
                  _ -> True
                refs = filter (\(_, node) -> isDGRef node) $ Graph.labNodes dg
                isexternal = find (\xref -> (xnName xref) == nodenamex) onlyrefxmlnamelist
                liburl = case isexternal of
                  (Just xnode) ->
                    case find (\(_, node) -> (dgn_name node) == (snd (xnItem xnode))) refs of
                      Nothing ->
                        "unknown"
                      (Just (_, node)) -> 
                        (asOMDocFile (unwrapLinkSource $ dgn_libname node))
                  _ ->
                    ""
                --nodenamex = case Set.toList $ Set.filter (\i -> (snd (xnItem i)) == nodename' ) nodexmlnameset of
                --      [] -> error "Import from Unknown node..."
                --      (l:_) -> xnName l
              in
                x' +++
                HXT.etag "imports" += (
                  (
                    qualattr
                      "xml"
                      "id"
                      (
                        (if isglobal then "ig" else "il")
                        ++ "." ++ theoname ++ "." ++ nodenamex
                      )
                    +++ HXT.sattr "from" (liburl++"#" ++ nodenamex)
                    +++ (if isglobal then xmlNullFilter else HXT.sattr "type" "local")
                  ) +++
                  (
                    case mmm of
                      (Just (sm, hs)) -> morphismMapToXmlXN sm hs nodenamex theoname
                      Nothing -> xmlNullFilter
                  )
                ) +++
                xmlNL
              ) (xmlNullFilter) importsxn --(Set.toList importsxn) --(Set.toList theoimports)
            ) +++
            -- sorts
            (Set.fold (\xnwos x' ->
              x' +++
              (sortToXmlXN (xnWOaToXNa xnwos)) +++
              xmlNL +++
              makePresentationFor
                (xnName xnwos)
                (Hets.idToString (xnWOaToa xnwos)) +++
              xmlNL
              ) xmlNL realsorts) +++
            -- adts
            {- 
               no presentation needed for adts as they are 
               generated from a) relations and b) sentences.
               relations have their presentation via sort-definition
               and sentences get their own presentation tags.
            -}
            (foldl (\x' sortwo ->
              let
                insortset = Map.findWithDefault Set.empty sortwo insortmap
                --sortxn = case find (\i -> Hets.sameOrigin sortwo (xnItem i) && sortwo == (xnItem i)) (Set.toList theosorts) of
                sortxn = case findItemPreferOrigin xnItem (Hets.woItem sortwo) (Hets.woOrigin sortwo) (mapSetToSet xmlnamedsortswomap) of
                  Nothing -> error ("Sort in relation but not in theory... (1) (" ++ (show sortwo) ++ ") [ " ++ (show theosorts) ++ "]")
                  (Just sortxn' ) -> xnWOaToXNa sortxn'
                insortsetxn = Set.map (\i ->
                  --case find (\j -> Hets.sameOrigin i (xnItem j) && i == (xnItem j)) (Set.toList theosorts) of
                  case findItemPreferOrigin xnItem (Hets.woItem i) (Hets.woOrigin i) (mapSetToSet xmlnamedsortswomap) of
                          Nothing -> error ("Sort in relation but not in theory... (2) (" ++ (show i) ++ ") [ " ++ (show theosorts) ++ "]")
                          (Just sortxn' ) -> xnWOaToXNa sortxn'
                  ) insortset
                constructorx = createAllConstructorsXN nodexmlnameset $ Map.toList $ Map.findWithDefault Map.empty (XmlNamed sortwo (xnName sortxn)) constructors
              in
                x' +++ createADTXN (sortxn, insortsetxn) constructorx +++ xmlNL
              ) xmlNL adtsorts) +++
            -- predicates
            (foldl
              (\x' (pxnid, p) ->
                let
                  px = predTypeToPredTypeXNWON (Set.toList theosorts) p 
                in
                  x' +++
                  predicationToXmlXN
                    nodexmlnameset
                    (pxnid, px) +++
                  xmlNL +++
                  makePresentationFor
                    (xnName pxnid)
                    (Hets.idToString $ xnWOaToa pxnid) +++
                  xmlNL
              )
              (xmlNullFilter)
              realtheopreds
            ) +++
            -- operators
            (foldl
              (\x' (oxnid, op) ->
                let
                  ox = opTypeToOpTypeXNWON (Set.toList theosorts) op 
                in
                  x' +++ 
                  operatorToXmlXN
                    nodexmlnameset
                    (oxnid, ox) +++
                  xmlNL +++
                  makePresentationFor
                    (xnName oxnid)
                    (Hets.idToString $ xnWOaToa oxnid) +++
                  xmlNL
              )
              (xmlNullFilter)
              realtheoops
            ) +++
            -- sentences
            sensxml
            )
            -- this constructs Hets-internal links as private data (but uses xmlnames for reference)
            +++ xmlNL +++ (inDGToXmlXN dg nodenum nodexmlnameset) +++ xmlNL 
            +++
              (foldl (\xml (fromxn, mll, mmm) ->
                let
                  tagname =
                    case mll of
                      Nothing -> error "corrupt data"
                      (Just ll) ->
                        case Static.DevGraph.dgl_type ll of
                          (Static.DevGraph.GlobalThm _ _ _) -> theoryInclusionS
                          (Static.DevGraph.LocalThm _ _ _) -> axiomInclusionS
                          _ -> error "corrupt data"
                  consattr =
                    case mll of
                      Nothing -> error "corrupt data"
                      (Just ll) ->
                        case Static.DevGraph.dgl_type ll of
                          (Static.DevGraph.GlobalThm _ c _) -> consAttr c
                          (Static.DevGraph.LocalThm _ c _) -> consAttr c
                          _ -> error "corrupt data"
                          
                in
                  xml +++ xmlNL +++
                    HXT.etag tagname += (
                      qualattr
                        "xml"
                        "id"
                        ( (if tagname == axiomInclusionS then "ai" else "ti")
                          ++ "." ++ theoname ++ "." ++ fromxn
                        )
                      +++ HXT.sattr "from" ("#"++fromxn) 
                      +++ HXT.sattr "to" ("#" ++ theoname)
                      +++ consattr
                      +++ case mmm of
                        Nothing -> xmlNullFilter
                        (Just (sm,hs)) -> morphismMapToXmlXN sm hs fromxn theoname
                      )
              )
              (xmlNullFilter)
              glThmLinksxn)
            )
            -- when constructing the catalogues a reference to the xmlname used in _this_ document is used
            -- it is very likely possible, that this theory has another name in real life (unless there are no name-collisions)
-- catalogue-support is gone...
--    ) (return $ refsToCatalogueXN dg nodexmlnameset +++ xmlNL) onlynodexmlnamelist 
    ) (return $ (xmlNullFilter)) onlynodexmlnamelist 
  where
  nodeTupelToNodeName::(a, NODE_NAME)->String
  nodeTupelToNodeName = nodeToNodeName . snd
  nodeToNodeName::NODE_NAME->String
  nodeToNodeName =
    (\nn ->
      let
        nodename = showName nn
      in
        if (length nodename) == 0
          then
            "AnonNode_"
          else
            nodename
    )
  consAttr::Static.DevGraph.Conservativity->HXT.XmlFilter
  consAttr Static.DevGraph.None = xmlNullFilter
  consAttr Static.DevGraph.Mono = HXT.sattr "conservativity" "monomorphism"
  consAttr Static.DevGraph.Cons = HXT.sattr "conservativity" "conservative"
  consAttr Static.DevGraph.Def = HXT.sattr "conservativity" "definitional"

  createMorphismMapAndHiding::
    Morphism.Morphism () () ()
    ->Bool
    ->[XmlNamedWONSORT]
    ->[(XmlNamedWONId, PredType)]
    ->[(XmlNamedWONId, OpType)]
    ->[XmlNamedWONSORT]
    ->[(XmlNamedWONId, PredType)]
    ->[(XmlNamedWONId, OpType)]
    ->(
       (Map.Map XmlNamedWONSORT XmlNamedWONSORT
      , Map.Map XmlNamedWONId XmlNamedWONId
      , Map.Map XmlNamedWONId XmlNamedWONId)
      , Maybe [XmlNamedWONId]
      )
  createMorphismMapAndHiding
    caslmorph
    isHiding
    ssorts
    spreds
    sops
    tsorts
    tpreds
    tops =
    let
      adjmorph =
        adjustMorphismSymbols
          ssorts
          spreds
          sops
          tsorts
          tpreds
          tops
          caslmorph
      mhl =
        if isHiding
          then
            let
              hl =
                checkHidden
                 adjmorph
                 ssorts -- source node is target in hiding morphism
                 spreds
                 sops 
                 tsorts -- target node is source in hiding morphism
                 tpreds
                 tops
            in
              case hl of
                [] -> Nothing
                _ -> Just hl
          else
            Nothing
    in
      (adjmorph, mhl)
                                                    
-- | create catalogue xml-structures for a DevGraph and its theories
-- theories needed because they have xml-names
refsToCatalogueXN::DGraph->TheoryXNSet->HXT.XmlFilter
refsToCatalogueXN dg theoryset =
  let
    refs = filter (\(_, node) -> isDGRef node) $ Graph.labNodes dg
  in
    HXT.etag "catalogue" += (
      xmlNL +++
      foldl (\cx (n, node) ->
        cx +++
        HXT.etag "loc" += (
          HXT.sattr
            "theory"
            (case getTheoryXmlName theoryset n of
              Nothing -> error "No Theory for Reference!"
              (Just xnname' ) -> xnname' )
            +++
          HXT.sattr "omdoc" (asOMDocFile (unwrapLinkSource $ dgn_libname node))
          ) +++
          xmlNL
        ) (xmlNullFilter) refs
      )
                
sortToXmlXN::XmlNamed SORT->HXT.XmlFilter
sortToXmlXN xnSort =
  ((HXT.etag "symbol" +=
    ( qualattr symbolTypeXMLNS symbolTypeXMLAttr "sort"
    +++ qualattr sortNameXMLNS sortNameXMLAttr (xnName xnSort)))
  {- +++ xmlNL +++
  (HXT.etag "presentation" += (
          (HXT.sattr "for" (xnName xnSort))
          +++ HXT.etag "use" += (
                  (HXT.sattr "format" "Hets")
                  +++ (HXT.txt (idToString (xnItem xnSort)))
                  )
          )
  ) -}
  )
        
-- | create an ADT for a SORT-Relation and constructor information (in xml)
createADTXN::(XmlNamed SORT, Set.Set (XmlNamed SORT))->HXT.XmlFilter->HXT.XmlFilter
createADTXN (s,ss) constructors =
  HXT.etag "adt" -- += (qualattr "xml" "id" ((show s)++"-adt")) -- id must be unique but is optional anyway... 
  += (
    xmlNL +++
    (HXT.etag "sortdef" += (
      HXT.sattr "name" (xnName s) +++
      HXT.sattr "type" "free" +++
      constructors +++
      (foldl (\isx is ->
              isx +++ xmlNL +++ (HXT.etag "insort" += (HXT.sattr "for" ("#" ++ (xnName is))))
      ) (xmlNullFilter) $ Set.toList ss)
      +++ xmlNL
      ) +++ xmlNL
    )
  )
          
createAllConstructorsXN::TheoryXNSet->[(XmlNamedWON Id.Id, Set.Set OpTypeXNWON)]->HXT.XmlFilter
createAllConstructorsXN theoryset cs = foldl (\cx c ->  
  cx +++ createConstructorsXN theoryset c +++ xmlNL ) (xmlNullFilter) cs
                
createConstructorsXN::TheoryXNSet->(XmlNamedWON Id.Id, Set.Set OpTypeXNWON)->HXT.XmlFilter
createConstructorsXN theoryset (cidxn, opxnset) =
  foldl (\cx opxn -> cx +++ createConstructorXN theoryset cidxn opxn +++ xmlNL) (xmlNullFilter) $ Set.toList opxnset
                
createConstructorXN::TheoryXNSet->(XmlNamedWON Id.Id)->OpTypeXNWON->HXT.XmlFilter
createConstructorXN theoryset cidxn (OpTypeXNWON _ opargsxn _) =
  HXT.etag "constructor" += (
    HXT.sattr "name" (xnName cidxn) +++
    xmlNL +++
    foldl (\argx arg ->
      argx +++ xmlNL +++
      --(HXT.etag "argument" += (HXT.sattr "sort" (xnName arg))) -- old syntax ?
      (HXT.etag "argument" += (
        HXT.etag "type" += (
          HXT.etag "OMOBJ" += (
            HXT.etag "OMS" += (
              HXT.sattr
                "cd"
                (case getTheoryXmlName theoryset (xnWOaToO arg) of
                  Nothing -> "unknown"
                  (Just xnname' ) -> xnname'
                )
              +++
              HXT.sattr "name" (xnName arg)
              )
            )
          )
        )
      )
      ) (xmlNullFilter) opargsxn
    )
            
-- | creates a xml-representation for a predication
-- needs a map of imports, sorts, the name of the current theory and the predication
predicationToXmlXN::TheoryXNSet->(XmlNamedWON Id.Id, PredTypeXNWON)->(HXT.XmlTree->HXT.XmlTrees)
predicationToXmlXN theoryset (pIdXN, (PredTypeXNWON predArgsXN)) =
  (HXT.etag "symbol" += (
    qualattr predNameXMLNS predNameXMLAttr (xnName pIdXN)
    +++ qualattr symbolTypeXMLNS symbolTypeXMLAttr "object"
          )
  ) += ( 
      xmlNL
      +++
      (HXT.etag "type" += (
        HXT.sattr "system" "casl"
              )
      ) += (
        xmlNL +++
        HXT.etag "OMOBJ" += (
          xmlNL +++
          HXT.etag "OMA" += (
            xmlNL +++
            (HXT.etag "OMS" += (
              HXT.sattr "cd" "casl"
              +++ HXT.sattr "name" "predication"
              )
            ) +++
            (foldl (\px sxn ->
              px +++ xmlNL
              +++
              (HXT.etag "OMS" += (
                HXT.sattr
                  "cd"
                  (fromMaybe
                    "unknownOrigin"
                    (getTheoryXmlName theoryset (xnWOaToO sxn))
                  )
                  +++ HXT.sattr "name" (xnName sxn)
                )
              )
            ) (xmlNullFilter) predArgsXN )
            +++ xmlNL
          )
          +++ xmlNL
        )
        +++ xmlNL
      )
      +++ xmlNL
    )
          
-- | creates a xml-representation for an operator
-- needs a map of imports, sorts, the name of the current theory and the operator
operatorToXmlXN::TheoryXNSet->(XmlNamedWON Id.Id, OpTypeXNWON)->(HXT.XmlTree->HXT.XmlTrees)
operatorToXmlXN theoryset (opIdXN, (OpTypeXNWON fk opArgsXN opResXN)) =
  (HXT.etag "symbol" += (
    qualattr opNameXMLNS opNameXMLAttr (xnName opIdXN)
    +++ qualattr symbolTypeXMLNS symbolTypeXMLAttr "object")
  )
  += ( 
    xmlNL
    +++
    (HXT.etag "type" += (HXT.sattr "system" "casl"))
    += (    xmlNL +++
      HXT.etag "OMOBJ"
      += (
        xmlNL +++
        HXT.etag "OMA"
        += (
          xmlNL +++
          (HXT.etag "OMS" += (HXT.sattr "cd" "casl" +++ HXT.sattr "name" (if fk==Total then "function" else "partial-function") ))
          +++
          (foldl (\px sxn ->
            px +++ xmlNL
            +++
            createSymbolForSortXN theoryset sxn
            ) (xmlNullFilter) opArgsXN )
          +++ xmlNL +++
          createSymbolForSortXN theoryset opResXN
          +++ xmlNL
        )
        +++ xmlNL
      )
      +++ xmlNL
    )
    +++ xmlNL
  )
          
inOMOBJ::HXT.XmlFilter->(HXT.XmlTree->HXT.XmlTrees)
inOMOBJ x = HXT.etag "OMOBJ" += x
{-
transformMorphOp::(Id.Id, OpType)->OP_SYMB
transformMorphOp (id' , ot) = Qual_op_name id' (cv_OpTypeToOp_type ot) Id.nullRange

transformMorphPred::(Id.Id, PredType)->PRED_SYMB
transformMorphPred (id' , pt) = Qual_pred_name id' (cv_PredTypeToPred_type pt) Id.nullRange
-}

-- relying on unique names there is no need for separating sorts, preds, ops, etc
-- but when naming changes occur (e.g. because the original casl changed) all documents
-- have to be updated...
morphismMapToXmlXN::(Map.Map String String)->Set.Set String->String->String->HXT.XmlFilter
morphismMapToXmlXN symbolmap hidings source target =
  if (Map.null symbolmap) && (Set.null hidings)
    then
      xmlNullFilter
    else
      HXT.etag "morphism" += (
        (if Set.null hidings
          then
            xmlNullFilter
          else
            (HXT.sattr "hiding" (implode " " $ Set.toList hidings))
        )
        +++
        (foldl
          (\sx (ss, st) -> 
            sx +++
              requation
                (inOMOBJ (HXT.etag "OMS" += (HXT.sattr "cd" source +++ HXT.sattr "name" ss)))
                (inOMOBJ (HXT.etag "OMS" += (HXT.sattr "cd" target +++ HXT.sattr "name" st)))
          )
          (xmlNullFilter)
          (Map.toList symbolmap)
        )
      )       
      where
      requation::(HXT.XmlTree->HXT.XmlTrees)->(HXT.XmlTree->HXT.XmlTrees)->(HXT.XmlTree->HXT.XmlTrees)
      requation p v =
        HXT.etag "requation" +=
          (
          xmlNL +++
          p +++
          xmlNL +++
          v +++
          xmlNL
          ) +++
        xmlNL

-- use xml-names instead
morphismMapToXmlXNR::
  (Map.Map String String) -- renamed symbols
  ->Set.Set String -- hidden symbols
  ->[XmlNamedWON Id.Id] -- symbols in source with xmlnames
  ->[XmlNamedWON Id.Id] -- symbols in target "
  ->String -- name of source (xml-reference)
  ->String -- name of target "
  ->HXT.XmlFilter
morphismMapToXmlXNR symbolmap hidings ssymsl tsymsl source target =
  HXT.etag "morphism" += (
    (HXT.sattr "hiding" (implode " " $ Set.toList hidings))
    +++
    (foldl
      (\sx (ss, st) -> 
        let
          ssx = case find (\x -> show (xnItem x) == ss) ssymsl of
            Nothing ->
              Debug.Trace.trace
                ("No symbol for \"" ++ ss ++ "\" in source")
                ss
            (Just x) -> xnName x
          stx = case find (\x -> show (xnItem x) == st) tsymsl of
            Nothing ->
              Debug.Trace.trace
                ("No symbol for \"" ++ st ++ "\" in source")
                st
            (Just x) -> xnName x
        in
          sx +++
            requation
              (inOMOBJ (HXT.etag "OMS" += (HXT.sattr "cd" source +++ HXT.sattr "name" ssx)))
              (inOMOBJ (HXT.etag "OMS" += (HXT.sattr "cd" target +++ HXT.sattr "name" stx)))
      )
      (xmlNullFilter)
      (Map.toList symbolmap)
    )
  )       
  where
  requation::(HXT.XmlTree->HXT.XmlTrees)->(HXT.XmlTree->HXT.XmlTrees)->(HXT.XmlTree->HXT.XmlTrees)
  requation p v =
    HXT.etag "requation" +=
      (
      xmlNL +++
      p +++
      xmlNL +++
      v +++
      xmlNL
      ) +++
    xmlNL

  -- @OldFormat@
  -- need to check if I implemented replacement correctly...
  {-
  caslMorphismToXml::Hets.ImportsMap->Hets.SortsMap->Hets.PredsMap->Hets.OpsMap->String->String->(CASL.Morphism.Morphism () () ())->HXT.XmlFilter
  caslMorphismToXml imports' sorts' preds' ops' sourcename targetname (CASL.Morphism.Morphism ssource starget sortmap funmap predmap _) =
          let
                  hides = Hets.createHidingString $ diffSig ssource starget -} -- comment placement because of jEdit...
  {-              hides = createHidingString2 $ (\(a,b,c,d,_) -> (a,b,c,d)) $
                          Hets.diffMaps
                                  (Hets.lookupMaps sorts Map.empty preds ops Map.empty sourcename)
                                  (Hets.lookupMaps sorts Map.empty preds ops Map.empty targetname) -}
                  
                  {-
                  morphx =
                          HXT.etag "morphism" +=
                                  (
                                  (if (length hides) /= 0 then
                                          HXT.sattr "hiding" hides
                                  else
                                          xmlNullFilter) +++
                                  (foldl (\mx (ss,st) ->
                                          mx +++
                                          HXT.etag "requation" +=
                                                  (
                                                  xmlNL +++
                                                  HXT.etag "pattern" +=
                                                          (
                                                          xmlNL +++
                                                          (inOMOBJ $ sortToOM imports' sorts' sourcename ss)
                                                          )
                                                   +++
                                                  HXT.etag "value" +=
                                                          (
                                                          xmlNL +++
                                                          (inOMOBJ $ sortToOM imports' sorts' targetname st)
                                                          )
                                                  )
                                          +++ xmlNL
                                          ) (xmlNL) $ Map.toList sortmap)
                                  +++ 
                                  (foldl (\mx ((ids, ots), (idt, fkt)) ->
                                          mx +++
                                          HXT.etag "requation" +=
                                                  (
                                                  xmlNL +++
                                                  HXT.etag "pattern" +=
                                                          (
                                                          xmlNL +++
                                                          (inOMOBJ $
                                                                  (processOperator
                                                                          imports'
                                                                          ops'
                                                                          sourcename
                  -- using a qualified OP_SYMB does not work correctly.
                  -- for example the reference to Sample/Simple in 
                  -- Advancend/Architectural has a morphism with a
                  -- Partial Operator while the Operator is defined as Total...
                  --                                                      (transformMorphOp
                  --                                                              (ids, ots)
                  -- workaround :
                  -- try both variants for function kind...
                                                                  (
                                                                          let     op = transformMorphOp (ids, ots)
                                                                                  -- get cd for original optype
                                                                                  cd = Hets.findNodeNameForOperatorWithSorts
                                                                                                  imports'
                                                                                                  ops'
                                                                                                  (ids, ots)
                                                                                                  sourcename
                                                                                  -- optype with flipped function kind
                                                                                  ots' = (\(OpType fk args res) ->
                                                                                          OpType 
                                                                                                  (case fk of
                                                                                                          Partial -> Total
                                                                                                          Total -> Partial)
                                                                                                  args
                                                                                                  res ) ots
                                                                                  -- operator with flipped fk
                                                                                  op' = transformMorphOp (ids, ots' )
                                                                                  -- get cd for 'flipped' optype
                                                                                  cd' = Hets.findNodeNameForOperatorWithSorts
                                                                                                  imports'
                                                                                                  ops'
                                                                                                  (ids, ots' )
                                                                                                  sourcename
                                                                                  -- check if a cd was found for the original op
                                                                                  -- if not, check if there was one for the flipped
                                                                                  -- if this fails use the original op again
                                                                                  -- (in this case something else is wrong...)
                                                                                  op'' = if cd == Nothing then
                                                                                                          if cd' == Nothing then
                                                                                                                  op
                                                                                                          else
                                                                                                                  op'
                                                                                                  else
                                                                                                          op
                                                                          -- actually this leads into generating output that
                                                                          -- in turn will lead to an input with this morphism
                                                                          -- wich may be different to the intended morphism...
                                                                          in op''
                                                                  )
                  
                                                                  )
                                                                  
                                                          ) +++
                                                          xmlNL
                                                          )
                                                  +++
                                                  xmlNL +++
                                                  HXT.etag "value" +=
                                                          ( xmlNL +++
                                                          ( let   otset = Set.filter (\(OpType fk _ _) -> fk == fkt) $
                                                                                  Map.findWithDefault Set.empty idt $
                                                                                          Map.findWithDefault Map.empty targetname ops'
                                                                  ott = if Set.null otset
                                                                          then
                                                                                  error "Cannot find Operator for Morphism..."
                                                                          else
                                                                                  head $ Set.toList otset
                                                            in 
                                                                  inOMOBJ $
                                                                          processOperator
                                                                                  imports'
                                                                                  ops'
                                                                                  targetname
                                                                                  (transformMorphOp
                                                                                          (idt, ott)
                                                                                  )
                                                          ) +++
                                                          xmlNL
                                                  ) +++
                                                  xmlNL
                                                  )
                                          +++ xmlNL
                                          ) (xmlNullFilter) $ Map.toList funmap)
                                  +++ 
                                  (foldl (\mx ((ids, pts), idt) ->
                                          mx +++
                                          HXT.etag "requation" +=
                                                  (
                                                  HXT.etag "pattern" +=
                                                          ( inOMOBJ $
                                                                  createSymbolForPredication imports' preds' sourcename
                                                                          (transformMorphPred (ids, pts))
                                                          ) +++
                                                  HXT.etag "value" +=
                                                          ( let   ptset = Map.findWithDefault Set.empty idt $
                                                                                  Map.findWithDefault Map.empty targetname preds'
                                                          
                                                                  ptt = if Set.null ptset
                                                                                  then
                                                                                          error "Cannot find Predication for Morphism..."
                                                                                  else
                                                                                          head $ Set.toList ptset
                                                            in
                                                                  inOMOBJ $
                                                                          createSymbolForPredication imports' preds' targetname
                                                                                  (transformMorphPred (idt, ptt))
                                                          ) +++
                                                  xmlNL
                                                  )
                                          +++ xmlNL
                                          ) (xmlNullFilter) $ Map.toList predmap)
                                  )
                          in
                                  morphx -- maybe some postprocessing ?
  -}      
                          
-- | this function partitions a list of CASLFORMULAS into two lists of
-- 'CASLFORMULA's : the first list contains 'normal' CFs and the second
-- all CFs that generate sorts (constructors)
partitionSensSortGenXN::[XmlNamedWON (Ann.Named CASLFORMULA)]->([XmlNamedWON (Ann.Named CASLFORMULA)], [XmlNamedWON (Ann.Named CASLFORMULA)])
partitionSensSortGenXN sens =
  foldl (\(sens' ,sortgen) xnsens -> --s@(Ann.NamedSen name' _ _ sentence) ->
    let
      (Ann.NamedSen name' _ _ sentence) = xnWOaToa xnsens
    in
      if isPrefixOf "ga_generated_" name' then
        case sentence of
                (Sort_gen_ax _ True) -> (sens' , sortgen++[xnsens])
                _ -> (sens' ++ [xnsens],sortgen)
      else
        (sens' ++[xnsens],sortgen)
    ) ([],[]) sens

-- | this function partitions a list of CASLFORMULAS into two lists of
-- 'CASLFORMULA's : the first list contains 'normal' CFs and the second
-- all CFs that generate sorts (constructors)
partitionSensSortGen::
  [Ann.Named CASLFORMULA]
  ->([Ann.Named CASLFORMULA], [Ann.Named CASLFORMULA])
partitionSensSortGen senslist =
  foldl
    (\(sens' ,sortgen) s -> 
      if isPrefixOf "ga_generated_" (Ann.senName s)
        then
          case (Ann.sentence s) of
            (Sort_gen_ax _ True) -> (sens' , sortgen++[s])
            _ -> (sens' ++ [s],sortgen)
        else
          (sens' ++[s],sortgen)
    )
    ([],[])
    senslist
                  
-- | creates constructors from a list of 'CASLFORMULA's (see : 'partitionSensSortGen')
makeConstructorsXN::[XmlNamedWONSORT]->XmlNameList->[XmlNamedWON (Ann.Named CASLFORMULA)]->(Map.Map (XmlNamedWON Id.Id) (Map.Map (XmlNamedWON Id.Id) (Set.Set OpTypeXNWON)), XmlNameList)
makeConstructorsXN sortsxnwo xmlnames sortgenaxxnlist =
  foldl (\(mapping, xmlnames' ) sortgenaxxn ->
    let
      (conidxnwo, conmap, xmlnames'' ) =
        makeConstructorMapXN sortsxnwo xmlnames' sortgenaxxn
    in
      (Map.insertWith (\a b -> Map.union a b) conidxnwo conmap mapping, xmlnames'' )
      ) (Map.empty, xmlnames) sortgenaxxnlist
                                        
-- | creates constructors from a 'CASLFORMULA'
makeConstructorMapXN::[XmlNamedWONSORT]->XmlNameList->XmlNamedWON (Ann.Named CASLFORMULA)->(XmlNamedWON Id.Id, (Map.Map (XmlNamedWON Id.Id) (Set.Set OpTypeXNWON)), XmlNameList)
makeConstructorMapXN sortsxnwo xmlnames sensxnwo =
  let
    sens = xnWOaToa sensxnwo
    (Ann.NamedSen senname _ _ (Sort_gen_ax cons _)) = sens
    origin = xnWOaToO sensxnwo
    sort = case cons of
      [] -> read ("[" ++ (drop (length "ga_generated_") senname) ++ "]")
      (c:_) -> newSort c
    sortxn = case sortToXmlNamedWONSORT sortsxnwo (sort) of
      Nothing -> error ("Cannot find sort to make constructor for! (No \"" ++ (Hets.idToString sort) ++ "\" in "
        ++ (show $ map (\x -> Hets.idToString (xnWOaToa x)) sortsxnwo) ++ ")")
      (Just sortxn' ) -> sortxn'
    (constructormap, xmlnames' ) =
      foldl(\(cmap, xmlnames'' ) (Constraint _ symbs _) ->
        foldl (\(tcmap, xmlnames''' ) (Qual_op_name name' ot _) ->
          let
            opxmlname = createUniqueName xmlnames''' (adjustStringForXmlName (show name' ))
          in
            (Map.insertWith (Set.union) (XmlNamed (Hets.mkWON name' origin) opxmlname) (Set.singleton (opTypeToOpTypeXNWON sortsxnwo (Hets.cv_Op_typeToOpType ot))) tcmap, xmlnames''' )
          ) (cmap, xmlnames'' ) $ map fst symbs
        ) (Map.empty, xmlnames) cons
  in
    (sortxn, constructormap, xmlnames' )
                  

-- | creates a String-representation of a DGLinkType    
linkTypeToString::DGLinkType->String
linkTypeToString LocalDef = "LocalDef"
linkTypeToString GlobalDef = "GlobalDef"
linkTypeToString HidingDef = "HidingDef"
linkTypeToString (LocalThm _ cons _) = "LocalThm Open "++ conservativityToString cons ++ " Open"
linkTypeToString (GlobalThm _ cons _) = "GlobalThm Open "++ conservativityToString cons ++ " Open"
linkTypeToString (HidingThm _ _) = "HidingThm EmptyMorphism Open"
linkTypeToString (FreeDef _) = "FreeDef EmptyNode"
linkTypeToString (CofreeDef _) = "CofreeDef EmptyNode"
-- TODO
-- Parameters 
linkTypeToString x = (take 7 (show x)) ++ "..."

-- | creates a String-representation of a Conservativity
conservativityToString::Conservativity->String
conservativityToString None = "None"
conservativityToString Cons = "Cons"
conservativityToString Mono = "Mono"
conservativityToString Def = "Def"

{-
-- | creates a Conservativity from a String or fails with error
stringToConservativity::String->Conservativity
stringToConservativity "None" = None
stringToConservativity "Cons" = Cons
stringToConservativity "Mono" = Mono
stringToConservativity "Def" = Def
stringToConservativity s = error ("Unknown Conservativity : \"" ++ s ++ "\"") 
-}

-- | creates a String-representation of a DGLinkLab
linkToString::DGLinkLab->String
linkToString dgl =
  "Type:\"" ++ (linkTypeToString $ dgl_type dgl) ++ "\" Origin:\"" ++ (show $ dgl_origin dgl) ++ "\""

{-                
defaultDGLinkType::DGLinkType
defaultDGLinkType = GlobalDef

defaultDGOrigin::DGOrigin
defaultDGOrigin = DGExtension

defaultDGLinkLab::DGLinkLab
defaultDGLinkLab = DGLink Hets.emptyCASLGMorphism defaultDGLinkType defaultDGOrigin
-}

inDGToXmlXN::DGraph->Graph.Node->TheoryXNSet->HXT.XmlFilter
inDGToXmlXN dg n theoryset =
  let
    inLinks = map (\ (from,_,a) -> (from,a) )  $ Graph.inn dg n
    named = map (\ (from, a) -> 
      let
        xname = case getTheoryXmlName theoryset from of
          Nothing -> "unknownNode"
          (Just xname' ) -> xname'
      in
        (xname, a) ) inLinks
    xnodename = case getTheoryXmlName theoryset n of
      Nothing -> error "Origin unknown!"
      (Just xnodename' ) -> xnodename'
  in
  if length inLinks == 0 then xmlNullFilter else
  (HXT.etag "private" += (HXT.sattr "for" xnodename))
  += ((HXT.etag "data" += (HXT.sattr "format" "Hets-Imports" +++ HXT.sattr "pto" "Hets"))
    += HXT.cdata (
    foldl (\ins (from, dgl) ->
      ins ++ ("From:\""++ from ++ "\" " ++ (linkToString dgl) ++ "\n")
      ) "\n" named)
    )
{-                
inDGToXmlForPrivate::DGraph->Graph.Node->(Map.Map Graph.Node String)->HXT.XmlFilter
inDGToXmlForPrivate dg n nodenames =
        let
                inLinks = map (\ (from,_,a) -> (from, a) ) $ Graph.inn dg n
                named = map ( \ (from, a) -> (Map.findWithDefault "unknownNode" from nodenames, a)) inLinks  
        in
        if length inLinks == 0 then xmlNullFilter else
        ((HXT.etag "data" += (HXT.sattr "format" "Hets-Imports" +++ HXT.sattr "pto" "Hets"))
                += HXT.cdata (
                foldl (\ins (from, dgl) ->
                        ins ++ ("From:\""++ from ++ "\" " ++ (linkToString dgl) ++ "\n")
                        ) "\n" named)
                )
-}

-- this is just a fragment of xpath-expressions from HXT
-- maybe(!) this can be used more effective that current methods...
{-
nodeNamesFromXmlXP::HXT.XmlTrees->(Set.Set String)
nodeNamesFromXmlXP t = Set.fromList $
        map (\n -> xshow [n]) $
        applyXmlFilter
                (XPath.getXPath ("@"
                        ++theoryNameXMLNS
                        ++":"
                        ++theoryNameXMLAttr
                        ++" | @"
                        ++theoryNameXMLAttr
                        ++"") .> getChildren) t
-}

-- remove keys from a map (will result in removing double entries when merging sets)
mapSetToSet::(Ord b)=>Map.Map a (Set.Set b)->Set.Set b
mapSetToSet mapping =
  foldl (\set (_, s) ->
    Set.union set s
    ) Set.empty (Map.toList mapping)
                
findItemPreferOrigin::(Eq a, Eq b, Container c q)=>(q->Hets.WithOrigin a b)->a->b->c->Maybe q
findItemPreferOrigin trans iitem iorig icon =
  let
    candidates = filter (\i -> (Hets.woItem (trans i)) == iitem) (getItems icon)
  in
    case find (\i -> (Hets.woOrigin $ trans i) == iorig) candidates of
      Nothing ->
        case candidates of
          (i:_) -> (Just i)
          _ -> Nothing
      i -> i
                
-- | theory name, theory source (local)
data TheoryImport = TI (String, String)

instance Show TheoryImport where
  show (TI (tn, ts)) = ("Import of \"" ++ tn ++ "\" from \"" ++ ts ++ "\".")

-- | source name, source (absolute)
data Source a = S { nameAndURI::(String, String), sContent::a } 

instance Show (Source a) where
  show (S (sn, sf) _) = ("Source \"" ++ sn ++ "\" File : \"" ++ sf ++ "\".");

type ImportGraph a = CLGraph.Gr (Source a) TheoryImport 

createLibName::ASL.LIB_NAME->String
createLibName libname = splitFile . fst . splitPath $ unwrapLinkSource libname

unwrapLinkSource::ASL.LIB_NAME->String
unwrapLinkSource
  (ASL.Lib_id lid) = unwrapLID lid
unwrapLinkSource
  (ASL.Lib_version lid _) = unwrapLID lid
--unwrapLinkSource _ = error "Wrong application of unwrapLinkSource!"

unwrapLID::ASL.LIB_ID->String
unwrapLID (ASL.Indirect_link url _) = url
unwrapLID (ASL.Direct_link path _) = path
                
libEnvToDGraphG::(ASL.LIB_NAME, DGraph, LibEnv)->(ImportGraph DGraph)
libEnvToDGraphG (ln,dg,lenv) =
  let
    input = (:) (ln,dg) $ map (\(ln' , gc) -> (ln', (devGraph gc) )) .
      filter (\(ln' ,_) -> ln' /= ln) $
      Map.toList lenv
  in
    makeIG input
  where
  makeIG::[(ASL.LIB_NAME, DGraph)]->(ImportGraph DGraph)
  makeIG input =
    let
      (lnodes, edges) = foldl (\(lnodes' , edges' ) (libname, dg' ) ->
        let
          nodenum = (+) 1 $ length lnodes'
          node = (nodenum, S (splitFile . fst . splitPath $ unwrapLinkSource libname, unwrapLinkSource libname) dg' )
          refs = filter isDGRef . map snd $ Graph.labNodes dg'
          imports' = map (\n -> (nodenum, (getDGNodeName n, unwrapLinkSource $ dgn_libname n))) refs
        in
          (lnodes' ++ [node], edges' ++ imports' )
          ) ([],[]) input
      ledges = foldl (\ledges' (target, (thname, libname)) ->
        let
          source = case filter (\(_, S (_,ssrc) _) -> ssrc == libname) lnodes of
            [] -> Debug.Trace.trace ("No source found for " ++ libname ++ " in " ++ (show $ map (\(S (_,src) _) -> src) $ map snd lnodes)) 0
            sourcelist -> fst $ head sourcelist
        in
          (source, target, TI (thname, libname)):ledges'
          ) [] edges
    in
      Graph.mkGraph lnodes ledges

libEnvXToDGraphG::(ASL.LIB_NAME, DGraph, LibEnv)->(ImportGraph (DGraph, ASL.LIB_NAME))
libEnvXToDGraphG (ln,dg,lenv) =
  let
    input = (:) (ln,dg) $ map (\(ln' , gc) -> (ln', (devGraph gc) )) .
      filter (\(ln' ,_) -> ln' /= ln) $
      Map.toList lenv
  in
    makeIG input
  where
  makeIG::[(ASL.LIB_NAME, DGraph)]->(ImportGraph (DGraph, ASL.LIB_NAME))
  makeIG input =
    let
      (lnodes, edges) = foldl (\(lnodes' , edges' ) (libname, dg' ) ->
        let
          nodenum = (+) 1 $ length lnodes'
          node = (nodenum, S (splitFile . fst . splitPath $ unwrapLinkSource libname, unwrapLinkSource libname) (dg', libname) )
          refs = filter isDGRef . map snd $ Graph.labNodes dg'
          imports' = map (\n -> (nodenum, (getDGNodeName n, unwrapLinkSource $ dgn_libname n))) refs
        in
          (lnodes' ++ [node], edges' ++ imports' )
          ) ([],[]) input
      ledges = foldl (\ledges' (target, (thname, libname)) ->
        let
          source = case filter (\(_, S (_,ssrc) _) -> ssrc == libname) lnodes of
            [] -> Debug.Trace.trace ("No source found for " ++ libname ++ " in " ++ (show $ map (\(S (_,src) _) -> src) $ map snd lnodes)) 0
            sourcelist -> fst $ head sourcelist
        in
          (source, target, TI (thname, libname)):ledges'
          ) [] edges
    in
      Graph.mkGraph lnodes ledges
                                
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

dGraphGToXmlGXN::(ImportGraph DGraph)->IO (ImportGraph (HXT.XmlTrees))
dGraphGToXmlGXN ig =
  do
    nodes <- mapM (\(n, (S i@(name' ,_) dg)) ->
      do
        omdoc <- devGraphToOMDocCMPIOXN emptyGlobalOptions dg name'
        return (n, S i omdoc ) ) $ Graph.labNodes ig
    return (Graph.mkGraph nodes $ Graph.labEdges ig)

dGraphGXLEToXmlGXN::
  (ImportGraph (DGraph, ASL.LIB_NAME))
  ->LibEnv
  ->XmlTaggedLibEnv
  ->IO (ImportGraph (HXT.XmlTrees))
dGraphGXLEToXmlGXN ig le xtagle =
  do
    nodes <- mapM (\(n, (S i@(name' ,_) (_, ln))) ->
      do
        omdoc <- libToOMDocCMPIOXN emptyGlobalOptions le xtagle ln name'
        return (n, S i omdoc ) ) $ Graph.labNodes ig
    return (Graph.mkGraph nodes $ Graph.labEdges ig)
  

fileSandbox::String->String->String
fileSandbox [] file = file
fileSandbox sb file =
  sb ++ "/" ++ case head file of
    '/' -> tail file
    _ -> file

-- | writes an XmlTrees-Graph to disk relative to a given directory
-- will create directory-structures from libnames
writeXmlG::HetcatsOpts->String->(ImportGraph (HXT.XmlTrees))->IO ()
writeXmlG hco dtduri ig =
  let
    nodes = map snd $ Graph.labNodes ig
  in
    (mapM (\(S (name' ,file) x) ->
      let
        omfile = fileSandbox (outdir hco) $ asOMDocFile file
      in
        putIfVerbose hco 0 ("Writing \"" ++ name' ++ "\" to \"" ++ omfile ++ "\"") >>
        -- putStrLn ("Writing \"" ++ name' ++ "\" to \"" ++ omfile ++ "\"") >>
        System.Directory.createDirectoryIfMissing True (snd $ splitPath omfile) >>
        writeOMDocDTD dtduri x omfile
      ) nodes) >> return ()
                        
                        
{-
-- FETCHPROOFSTEPS BEGIN
-- Needs to be rewritten completely...


-- This function extracts proof-steps from Xml using an already constructed
-- DGraph for Information
fetchProofSteps::Static.DevGraph.DGraph->HXT.XmlTrees->Static.DevGraph.DGraph
fetchProofSteps dg t = let      theories = applyXmlFilter (isTag "theory") t
                       in
                          -- fold the proofsteps into the DGraph
                          -- by theory
                          foldl (\newdg theory ->
                                        fetchProofStepsFor dg [theory] ) dg theories
                                        
-- after all these helpers lets get back to the problem
-- we are folding proof-steps into the DGraph for each theory, so this
-- function gets the current DGraph and an XmlTree containing the single theory
-- (so it fetches the proof-steps _for_ this theory...)
fetchProofStepsFor::Static.DevGraph.DGraph->HXT.XmlTrees->Static.DevGraph.DGraph
fetchProofStepsFor dg t = let   tnameS = xshow $ applyXmlFilter (getValue "id") t
                                toNodeN = nodeNameToNodeNum (Graph.labNodes dg) tnameS
                                importswithproofsteps = applyXmlFilter (getChildren .> (isTag axiomInclusionS +++ isTag theoryInclusionS)) t
                                proofsteps = applyXmlFilter (getChildren .> isTag "proof-object") t
                          in
                            foldl (\newdg importx ->
                                        let     isLocalThm = applyXmlFilter (isTag axiomInclusionS) [importx] /= []
                                                fromNameS = xshow $ applyXmlFilter (getValue "from") [importx]
                                                fromNodeN = nodeNameToNodeNum (Graph.labNodes dg) fromNameS
                                                (n, m, myedge) = getSpecialEdge (Graph.labEdges newdg) fromNodeN toNodeN (if isLocalThm then isLocalThmEdge else isGlobalThmEdge)
                                                -- every import has at most one proof-object...
                                                thisproofsteps = applyXmlFilter (withSValue "theory" fromNameS .> withSValue "for" tnameS) proofsteps
                                                (tls1, cons, tls2) = xmlToLinkStatus dg thisproofsteps
                                        in Graph.insEdge (n, m, (replaceThmLinkStati myedge (tls1, cons, tls2))) (Graph.delEdge (n,m) newdg)
                                        ) dg importswithproofsteps

-}
{-

-- Helper-function to get the Number of a Node in the DGraph given the Name
nodeNameToNodeNum::[Graph.LNode Static.DevGraph.DGNodeLab]->String->Graph.Node
nodeNameToNodeNum [] _ = error "no such node"
nodeNameToNodeNum ((n, node):rest) name' = if name' == (Static.DevGraph.getDGNodeName node) then n
                                                else nodeNameToNodeNum rest name'
  -}              
{-
-- we get into the problem to delete an edge wich may not be the only egde
-- between two nodes. So this function performs a test on a edge that
-- may fit the connection.
getSpecialEdge::[Graph.LEdge Static.DevGraph.DGLinkLab]->Graph.Node->Graph.Node->(Static.DevGraph.DGLinkLab->Bool)->(Graph.LEdge Static.DevGraph.DGLinkLab)
getSpecialEdge [] _ _ _ = error "no such special edge"
getSpecialEdge ((theedge@(n,m,edge)):rest) n' m' isSpecial = if ( n==n' ) && ( m == m' ) && (isSpecial edge) then theedge
                                                                else getSpecialEdge rest n' m' isSpecial

-- externalized test-function for edges                                                                 
isLocalThmEdge::Static.DevGraph.DGLinkLab->Bool
isLocalThmEdge (DGLink _ (LocalThm _ _ _) _) = True
isLocalThmEdge _ = False

-- externalized test-function for edges                                                                 
isGlobalThmEdge::Static.DevGraph.DGLinkLab->Bool
isGlobalThmEdge (DGLink _ (GlobalThm _ _ _) _) = True
isGlobalThmEdge _ = False

-- this is a very clumsy yet simple way to change 'just' the Proof-Steps of
-- an edge (So I do not have to worry about Global/Local later).
replaceThmLinkStati::Static.DevGraph.DGLinkLab->(ThmLinkStatus, Conservativity, ThmLinkStatus)->Static.DevGraph.DGLinkLab
replaceThmLinkStati (DGLink a (LocalThm _ _ _) b) (tls1, c, tls2) = DGLink a (LocalThm tls1 c tls2) b
replaceThmLinkStati (DGLink a (GlobalThm _ _ _) b) (tls1, c, tls2) = DGLink a (GlobalThm tls1 c tls2) b
replaceThmLinkStati a _ = error ("Cannot replace ThmLinkStati on \"" ++ show a ++ "\"") 

-- to delete an edge, we have to find it first
-- this function finds an edge provided the two nodes connected (direction matters)
-- i think this function is not used
getEdgeByNodeNums::[Graph.LEdge Static.DevGraph.DGLinkLab]->Graph.Node->Graph.Node->(Graph.LEdge Static.DevGraph.DGLinkLab)
getEdgeByNodeNums [] _ _ = error "no such edge"
getEdgeByNodeNums ((theedge@(n,m,_)):rest) n' m' = if ( n==n' ) && ( m == m' ) then theedge
                                                        else getEdgeByNodeNums rest n' m'

-- To create proof-steps, all Edges have to be already in the DG
xmlToProofSteps::HXT.XmlTrees->Static.DevGraph.DGraph->[Static.DevGraph.DGLinkLab]
xmlToProofSteps t dg = map (\n -> xmlToProofStep [n] dg) $ ((applyXmlFilter (isTag "OMSTR") t)::[HXT.XmlTree])

-- create a single proof-step (find an edge)
xmlToProofStep::HXT.XmlTrees->Static.DevGraph.DGraph->Static.DevGraph.DGLinkLab
xmlToProofStep t dg = let       n1ton2S = xshow $ applyXmlFilter (getChildren) t
                                n1S = getStringBefore "->" n1ton2S
                                n2S = drop ((length n1S) + (length "->")) n1ton2S
                                labnodes = Graph.labNodes dg
                                labedges = Graph.labEdges dg
                                (Just n1Num) = findNodeNumFor labnodes n1S
                                (Just n2Num) = findNodeNumFor labnodes n2S
                                maybeEdge = findEdgeFor labedges n1Num n2Num
                      in case maybeEdge of
                                (Just a) -> a
                                Nothing -> error ("Cannot find Edge for \"" ++ xshow t ++ "\"")
                                
-- another helper
getStringBefore::String->String->String
getStringBefore _ [] = []
getStringBefore sub (c:s) = if isPrefix sub (c:s) then []
                        else [c] ++ (getStringBefore sub s)
-- finds a nodeNumber by Name (maybe)
findNodeNumFor::[(Graph.LNode Static.DevGraph.DGNodeLab)]->String->(Maybe Graph.Node)
findNodeNumFor [] _ = Nothing
findNodeNumFor ((n, node):rest) name' = if (name' == Static.DevGraph.getDGNodeName node) then (Just n)
                                        else findNodeNumFor rest name'
-- finds an edge by node numbers (maybe)                                        
findEdgeFor::[(Graph.LEdge Static.DevGraph.DGLinkLab)]->Graph.Node->Graph.Node->(Maybe Static.DevGraph.DGLinkLab)
findEdgeFor [] _ _ = Nothing
findEdgeFor ((n1, n2, edge):rest) node1 node2 = if (node1==n1) && (node2==n2) then (Just edge)
                                                        else findEdgeFor rest node1 node2
-- convert Xml to Conservativity
xmlToConservativity::HXT.XmlTrees->Static.DevGraph.Conservativity
xmlToConservativity t = if applyXmlFilter (isTag "OMSTR") t /= [] then
                          let conS = drop (length "Conservativity: ") (xshow $ applyXmlFilter (getChildren) t)
                          in
                          if conS == "None" then None
                          else
                          if conS == "Cons" then Cons
                          else
                          if conS == "Mono" then Mono
                          else
                          if conS == "Def" then Def
                          else
                            error ("Illegal Conservativity : \""++ conS ++"\"")
                        else
                          error ("Cannot create Conservativity from \""++ xshow t ++"\"")
  -}                        
-- FETCHPROOFSTEPS END

{- not used yet         
-- to clear the code a bit      
validImports::HXT.XmlFilter
validImports = (isTag "imports" +++ isTag axiomInclusionS +++ isTag theoryInclusionS)

-- to clear the code a bit      
validProofs::HXT.XmlFilter
validProofs = (isTag "proofobject")


-- this function splits a theory-XmlTree into its name, imports and proof-steps
getTheoryNameImportAndProof::HXT.XmlTrees->(String, HXT.XmlTrees, HXT.XmlTrees)
getTheoryNameImportAndProof t = (
                                 xshow $ applyXmlFilter (isTag "theory" .> getValue "id") t
                                ,applyXmlFilter (getChildren .> validImports) t
                                ,applyXmlFilter (getChildren .> validProofs) t
                                )

-}

{-
 DGRef's have (maybe) a Name but always a Library-Name and know the
 nodes number in the DG of that library.
 We have no node-numbers in our Xml-representation just unambigous names...
 we could make sure that nodes are ordered by their node number but what
 about human intervention ?
 perhaps we should save the number of a node into the xml or -- what i like
 better -- we should only support DGRef's with a name...
 A DGRef has no signature but we need a signature to construct the edges.
 Should these signatures be saved to Xml or should we assume, that there is
 always a way to receive the signature ?
 On the long run, the latter is the only choice, but this will make testing
 more complicated...
 On the other hand : if for each DGRef-Info in the Xml a new DGraph is
 generated a lot of problems just dissolve (and come back as FileIO)...
-} 

                
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

-- FORMULAS -> X M L 

-- Above ends the part for creating DGraphs
-- No we enter the fascinating world of Formula-Processing... (22:58)

-- Formulas as OMA
-- wrap in Theory-axiom-FMP.

wrapFormulasCMPIOXN::PFInput->[XmlNamedWON (Ann.Named CASLFORMULA)]->IO (HXT.XmlTree->HXT.XmlTrees)
wrapFormulasCMPIOXN pfinput fs =
  let
    posLists = concatMap Id.getPosList (map (Ann.sentence . xnWOaToa) fs)
  in
  do
    poslinemap <- posLines posLists
    return $ foldl (\wrapped f -> wrapped +++ (wrapFormulaCMPXN pfinput f poslinemap) ) (xmlNullFilter) fs
                
wrapFormulaCMPXN::
  PFInput->
  (XmlNamedWON (Ann.Named CASLFORMULA))->
  (Map.Map Id.Pos String)->
  (HXT.XmlTree->HXT.XmlTrees)
wrapFormulaCMPXN
  pfinput
  ansenxn
  poslinemap =
  let
    sens = Ann.sentence (xnWOaToa ansenxn)
    sposl = Id.getPosList sens
  in
  (
    (createQAttributed
      "axiom"
      [
        (axiomNameXMLNS,
        axiomNameXMLAttr,
        (xnName ansenxn))
      ]
    ) += (
      (xmlNL +++
      ((foldl (\cmpx p -> cmpx += (HXT.txt ("\n" ++ (Map.findWithDefault "" p poslinemap))) ) (HXT.etag "CMP") sposl) += (HXT.txt "\n"))+++ 
      xmlNL +++
      (HXT.etag "FMP" += (
        xmlNL +++
        (
         HXT.etag "OMOBJ" +++
         xmlNL
        ) += (
          xmlNL +++
          (processFormulaXN
            pfinput
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
    makePresentationFor (xnName ansenxn) (Ann.senName (xnWOaToa ansenxn))
  ) +++ xmlNL


createSymbolForSortXN::TheoryXNSet->XmlNamedWONSORT->(HXT.XmlTree->HXT.XmlTrees)
createSymbolForSortXN theoryset xnsort =
  HXT.etag "OMS" += ( HXT.sattr "cd" (fromMaybe "unknown" $ getTheoryXmlName theoryset (xnWOaToO xnsort) ) +++ HXT.sattr "name" (xnName xnsort) )

-- create a xml-representation for a sort, searching for matching sort in set and using xml-name...     
createSymbolForSortWithSortXNSet::TheoryXNSet->Set.Set XmlNamedWONSORT->SORT->HXT.XmlFilter
createSymbolForSortWithSortXNSet theoryset theorysorts sort =
  let
    xnsort = case find (\i -> (xnWOaToa i) == sort ) (Set.toList theorysorts) of
      Nothing -> error ("Cannot create the Symbol because I cannot find the Sort !" ++ "(" ++ (show sort) ++ " , " ++ (show theorysorts) ++ ")")
      (Just xnsort' ) -> xnsort'
  in
    createSymbolForSortXN theoryset xnsort
        
data PFInput =
  PFInput
    {
       pfiGO::GlobalOptions
      ,theorySet::TheoryXNSet
      ,theorySorts::Set.Set XmlNamedWONSORT
      ,theoryRel::Rel.Rel XmlNamedWONSORT
      ,theoryPreds::[(XmlNamedWONId, PredTypeXNWON)]
      ,theoryOps::[(XmlNamedWONId, OpTypeXNWON)]
      ,debugInfo::String
    }
{-                
emptyPFInput::PFInput
emptyPFInput =
  PFInput
    emptyGlobalOptions
    Set.empty
    Set.empty
    []
    []
-}

-- | create the xml-representation for a formula (in context of a theory)       
processFormulaXN ::
  PFInput
  -> FORMULA f -- ^ the formula to process
  -> (HXT.XmlTree -> HXT.XmlTrees) -- ^ a xml-representation of the formula
-- Quantification
processFormulaXN pfinput 
  (Quantification q vl f _) =
    ( HXT.etag "OMBIND" += (
      xmlNL +++
      (HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" (quantName q))
      ) +++
      (xmlNL) +++
      (processVarDeclXN (theorySet pfinput) (theorySorts pfinput) vl) +++
      (processFormulaXN pfinput f) )
    ) +++
    xmlNL
-- Conjunction
processFormulaXN pfinput
  (Conjunction fl _) =
    (HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslConjunctionS)
      ) +++
      (foldl (\forms f ->
        forms +++
        processFormulaXN pfinput f
        ) (xmlNL) fl)
    ) ) +++
    xmlNL
-- Disjunction
processFormulaXN pfinput
  (Disjunction fl _) =
    (HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslDisjunctionS)
      ) +++
      (foldl (\forms f ->
        forms +++
        processFormulaXN pfinput f
        ) (xmlNL) fl)
    ) ) +++
    xmlNL
-- Implication
processFormulaXN pfinput
  (Implication f1 f2 b _) =
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslImplicationS)
      ) +++
      (xmlNL) +++
      (processFormulaXN pfinput f1) +++
      (processFormulaXN pfinput f2) +++
      (processFormulaXN pfinput
              (if b then True_atom Id.nullRange else False_atom Id.nullRange))
    ) ) +++
    xmlNL
-- Equivalence
processFormulaXN pfinput
  (Equivalence f1 f2 _) =
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslEquivalenceS)
      ) +++
      (xmlNL) +++
      (processFormulaXN pfinput f1) +++
      (processFormulaXN pfinput f2)
    ) ) +++
    xmlNL
-- Negation
processFormulaXN pfinput
  (Negation f _) =
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslNegationS)
      ) +++
      (xmlNL) +++
      (processFormulaXN pfinput f)
    ) ) +++
    xmlNL
-- Predication
processFormulaXN pfinput
  (Predication p tl _) =
    (HXT.etag "OMA" += (
      xmlNL +++
      (HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslPredicationS)
      ) +++
      xmlNL +++
      (xmlNL) +++
      (createSymbolForPredicationXN pfinput p) +++
      (foldl (\term t ->
        term +++
        (processTermXN pfinput t) +++
        xmlNL
        ) (xmlNullFilter) tl
      ) +++
      (xmlNL)
    ) ) +++
    xmlNL
-- Definedness
processFormulaXN pfinput
  (Definedness t _ ) =
    (HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslDefinednessS)
      ) +++
      (xmlNL) +++
      (processTermXN pfinput t)
    ) ) +++
    xmlNL
-- Existl_equation
processFormulaXN pfinput
  (Existl_equation t1 t2 _) = 
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslExistl_equationS)
      ) +++
      (xmlNL) +++
      (processTermXN pfinput t1) +++
      (processTermXN pfinput t2)
    ) ) +++
    xmlNL
-- Strong_equation
processFormulaXN pfinput
  (Strong_equation t1 t2 _) = 
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslStrong_equationS)
      ) +++
      (xmlNL) +++
      (processTermXN pfinput t1) +++
      (processTermXN pfinput t2)
    ) ) +++
    xmlNL
-- Membership
processFormulaXN pfinput
  (Membership t s _) = 
    ( HXT.etag "OMA" += (
      xmlNL +++
      ( HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" caslMembershipS)
      ) +++
      (xmlNL) +++
      (processTermXN pfinput t) +++
      (createSymbolForSortWithSortXNSet (theorySet pfinput) (theorySorts pfinput) s )
    ) ) +++
    xmlNL
-- False_atom
processFormulaXN _
  (False_atom _) =
    (HXT.etag "OMS" +=
      (HXT.sattr "cd" caslS +++
      HXT.sattr "name" caslSymbolAtomFalseS)
    ) +++
    xmlNL
-- True_atom
processFormulaXN _
  (True_atom _) =
    (HXT.etag "OMS" +=
      (HXT.sattr "cd" caslS +++
      HXT.sattr "name" caslSymbolAtomTrueS)
    ) +++
    xmlNL
-- Sort_gen_ax
processFormulaXN pfinput
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
        (processConstraintsXN pfinput constraints) +++
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
processFormulaXN _
  (Mixfix_formula _) =
    HXT.etag unsupportedS +++
    HXT.txt ( "<-- " ++ "Mixfix_formula" ++ " //-->")
-- Unparsed_formula
processFormulaXN _
  (Unparsed_formula s _) =
    HXT.etag unsupportedS +++
    HXT.txt ( "<-- " ++ "Unparsed_formula \"" ++ s ++ "\" //-->")
-- ExtFORMULA
processFormulaXN _
  (ExtFORMULA _) =
    HXT.etag unsupportedS +++
    HXT.txt ( "<-- " ++ "ExtFORMULA" ++ " //-->") 

-- | create an xml-representation for a predication
createSymbolForPredicationXN::
--  TheoryXNSet
--  -> [(XmlNamedWONId, PredTypeXNWON)] 
  PFInput
  -> PRED_SYMB -- ^ the predication to process
  -> (HXT.XmlTree -> HXT.XmlTrees) 
       -- ^ a xml-representation of the predication
-- Pred_name
createSymbolForPredicationXN pfinput -- theoryset theorypreds
  (Pred_name pr) =
    let
      (xnpid, _) =
        case
          find
            (\(xnpid' , _) ->
              (xnWOaToa xnpid' ) == pr ) (theoryPreds pfinput)
        of 
          Nothing -> error "Cannot find Spredicate in theory!"
          (Just x' ) -> x'
    in
      HXT.etag "OMS" += 
        (HXT.sattr "cd" (fromMaybe "unknown" $
          getTheoryXmlName (theorySet pfinput) (xnWOaToO xnpid)) +++
        HXT.sattr "name" (xnName xnpid)
        )
-- Qual_pred_name
createSymbolForPredicationXN pfinput -- theoryset theorypreds
  (Qual_pred_name pr pt _) =
    let
      (xnpid, _) =
        case
          findCompatiblePredicate
            (theoryRel pfinput)
            (theoryPreds pfinput)
            pr
            (Hets.cv_Pred_typeToPredType pt)
        of
          Nothing ->
            error
              (
                "Cannot find Qpredicate in theory!"
                  ++ "(" ++ (show pr) ++ ", "
                  ++ (show (theoryPreds pfinput)) ++ ")"
              )
          (Just x) -> x
    in
      HXT.etag "OMS" +=
        ( HXT.sattr "cd" ( fromMaybe "unknown" $
          getTheoryXmlName (theorySet pfinput) (xnWOaToO xnpid)
          ) +++
        HXT.sattr "name" (xnName xnpid)
        ) +++
      xmlNL


--data QUANTIFIER = Universal | Existential | Unique_existential
-- Quantifier as CASL Symbol
quantName :: QUANTIFIER->String
quantName Universal = caslSymbolQuantUniversalS
quantName Existential = caslSymbolQuantExistentialS
quantName Unique_existential = caslSymbolQuantUnique_existentialS

                
-- need to check if this is correct with Xml --
processConstraintsXN::PFInput->[ABC.Constraint]->(HXT.XmlTree->HXT.XmlTrees)
processConstraintsXN _ [] = xmlNullFilter
processConstraintsXN pfinput ((ABC.Constraint news ops' origs):_) =
  (HXT.etag "OMBIND" += (
    (HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" (show news)))
    +++ xmlNL
    +++ (HXT.etag "OMBVAR" +=(
      foldl (\opsx (op, il) ->
        opsx +++ (HXT.etag "OMATTR" += (
          (HXT.etag "OMATP" += (
            HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" "constraint-indices")
            +++ (HXT.etag "OMSTR" += HXT.txt (
              foldl (\s i -> (s++(show i)++"|")) "" il
              ))
            ))
          +++ xmlNL
          +++ processOperatorXN pfinput (debugGO (pfiGO pfinput) "pCXN" ("creating conop for " ++ (show op)) op)
          ) ) +++ xmlNL
        ) (xmlNullFilter) ops'
      ) )
    +++ xmlNL
    +++ (HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" (show origs))))) +++ xmlNL

-- first newline needs pulling up because we have a list of lists...
processVarDeclXN :: TheoryXNSet -> Set.Set XmlNamedWONSORT -> [VAR_DECL] -> (HXT.XmlTree->HXT.XmlTrees)
processVarDeclXN theoryset theorysorts vdl =
  (HXT.etag "OMBVAR" += (xmlNL +++ (processVarDecls theoryset theorysorts vdl)) ) +++ xmlNL
  where
  processVarDecls :: TheoryXNSet -> Set.Set XmlNamedWONSORT -> [VAR_DECL] -> (HXT.XmlTree->HXT.XmlTrees)
  processVarDecls _ _ [] = xmlNullFilter
  processVarDecls theoryset' theorysorts' ((Var_decl vl s _):vdl' ) = (foldl (\decls vd -> decls +++
  -- <ombattr><omatp><oms>+</omatp><omv></ombattr>
    ( createTypedVarXN theoryset theorysorts' s (show vd) )
      +++ xmlNL)
      (xmlNullFilter) vl ) -- end fold
      +++ (processVarDecls theoryset' theorysorts' vdl' )

createATPXN::TheoryXNSet -> Set.Set XmlNamedWONSORT -> SORT ->(HXT.XmlTree->HXT.XmlTrees)
createATPXN theoryset theorysorts sort =
  HXT.etag "OMATP" +=
    ((HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" typeS ) )
     +++ createSymbolForSortWithSortXNSet theoryset theorysorts sort
     )
                 
-- TODO : change to correct types
createTypedVarXN::TheoryXNSet -> Set.Set XmlNamedWONSORT->SORT->String->(HXT.XmlTree->HXT.XmlTrees)
createTypedVarXN theoryset theorysorts sort varname =
  HXT.etag "OMATTR" += ( (createATPXN theoryset theorysorts sort) +++ (HXT.etag "OMV" += (HXT.sattr "name" varname) ) )
       
-- | create a xml-representation from a term (in context of a theory)
processTermXN::
  PFInput
  -> TERM f -- ^ the term to process
  -> (HXT.XmlTree -> HXT.XmlTrees) -- ^ xml-representation of the term
-- Simple_id
processTermXN _
  (Simple_id id' ) =
    HXT.etag "OMV" +=
      HXT.sattr "name" (show id' ) -- not needed
-- Qual_var
processTermXN pfinput
  (Qual_var v s _) =
    ( createTypedVarXN (theorySet pfinput) (theorySorts pfinput) s (show v) ) +++
    xmlNL
-- Application
processTermXN pfinput
  (Application op termlist _) =
    if null termlist
      then
        (processOperatorXN pfinput (debugGO (pfiGO pfinput) "pTXN" ("app (n) : calling pOXN for " ++ (show op)) op)) +++
        xmlNL
      else
        (HXT.etag "OMA" +=
          (xmlNL +++
          ( processOperatorXN pfinput (debugGO (pfiGO pfinput) "pTXN" ("app (nn) : calling pOXN for " ++ (show op)) op)) +++
          (foldl (\terms t ->
            terms +++
            (processTermXN pfinput t)
            ) (xmlNullFilter) termlist
          )
          ) ) +++
          xmlNL
-- Cast
processTermXN pfinput
  (Cast t s _) =
    processTermXN pfinput
      (Application
        (Op_name $ Hets.stringToId "PROJ")
        [t, (Simple_id $ Id.mkSimpleId (show s))]
        Id.nullRange
      )
-- Conditional
processTermXN pfinput
  (Conditional t1 f t2 _) =
    HXT.etag "OMA" +=
      (xmlNL +++
      (HXT.etag "OMS" +=
        (HXT.sattr "cd" caslS +++
        HXT.sattr "name" "IfThenElse"
        )
      ) +++
      (processFormulaXN pfinput f) +++
      (processTermXN pfinput t1) +++
      (processTermXN pfinput t2)
      )
-- Sorted_term is to be ignored in OMDoc (but could be modelled...) (Sample/Simple.casl uses it...)
processTermXN pfinput
  (Sorted_term t _ _) =
    processTermXN pfinput t
-- Unsupported Terms...
processTermXN _ _ = error "Unsupported Term encountered..." 

-- | create a xml-representation of an operator (in context of a theory)
processOperatorXN::
  PFInput
  -> OP_SYMB -- ^ the operator to process
  -> (HXT.XmlTree -> HXT.XmlTrees) 
      -- ^ the xml-representation of the operator
-- Op_name
processOperatorXN pfinput
  (Op_name op) =
    let
      (xnopid, _) =
        case
          find
            (\(xnid, _) -> (xnWOaToa xnid) == op)
            (theoryOps pfinput)
        of
          Nothing ->
            if (show op == "PROJ")
              then
                (XmlNamed (Hets.mkWON op (-1)) "PROJ", undefined)
              else
                error
                  (
                    "Operator is unknown! (" ++ (show op)
                      ++ " in "++ (show (theoryOps pfinput)) ++")")
          (Just x' ) -> x'
    in
      HXT.etag "OMS" +=
        (HXT.sattr "cd" 
          (fromMaybe "casl" $
            getTheoryXmlName (theorySet pfinput) (xnWOaToO xnopid)) +++
          HXT.sattr "name" (xnName xnopid)
        )
-- Qual_op_name
processOperatorXN pfinput
  (Qual_op_name op ot _) =
    let
      (xnopid, _) =
        case
          findCompatibleOperator
            (theoryRel pfinput)
            (theoryOps pfinput)
            op
            (Hets.cv_Op_typeToOpType ot)
        of
          Nothing ->
            error
              (
                "No compatible Operator for ("
                  ++ (show op) ++ "( "++ (show ot) ++ " ) in "
                  ++ (show (theoryOps pfinput)) ++
                  ") where the sort relation is " 
                  ++ (show (theoryRel pfinput))
                  ++ "OpsShort : " ++ (show (map (show . xnWOaToa . fst) (theoryOps pfinput)))
                  ++ " DebugInfo : " ++ (debugInfo pfinput)
              )
          (Just x) -> x
    in
      HXT.etag "OMS" +=
        ( HXT.sattr "cd"
          ( fromMaybe "casl" $
            getTheoryXmlName (theorySet pfinput) (xnWOaToO xnopid)
          ) +++
          HXT.sattr "name" (xnName xnopid)
        )


-- find a compatible predicate
-- compatible predicates have a more generic type than the actual
-- predicate, that is, their parameter types are supersorts
findCompatiblePredicate::
  Rel.Rel XmlNamedWONSORT
  ->[(XmlNamedWONId, PredTypeXNWON)]
  ->Id.Id
  ->PredType
  ->Maybe (XmlNamedWONId, PredTypeXNWON)
findCompatiblePredicate
  sortrel
  predicates
  predname
  predtype =
  let
    srel = xmlRelToRel sortrel
  in
    find
      (\(xnid, xnprt) ->
        ((xnWOaToa xnid) == predname)
          && (
            compatiblePredicate
              srel
              predtype -- optype is checked to be compatible with one
                     -- from the list
              (predTypeXNWONToPredType xnprt)
            )
      )
      predicates

-- find a compatible operator
-- compatible operators have a more generic type than the actual
-- operator, that is, their parameter types are supersorts
findCompatibleOperator::
  Rel.Rel XmlNamedWONSORT
  ->[(XmlNamedWONId, OpTypeXNWON)]
  ->Id.Id
  ->OpType
  ->Maybe (XmlNamedWONId, OpTypeXNWON)
findCompatibleOperator
  sortrel
  operators
  opname
  optype =
  let
    srel = xmlRelToRel sortrel
  in
    find
      (\(xnid, xnopt) ->
        ((xnWOaToa xnid) == opname)
          && (
            compatibleOperator
              srel
              optype -- optype is checked to be compatible with one
                     -- from the list
              (opTypeXNWONToOpType xnopt)
            )
      )
      operators
        

-- strip xmlnames and origins from a relation
xmlRelToRel::Rel.Rel XmlNamedWONSORT->Rel.Rel SORT
xmlRelToRel xrel =
  Rel.fromList $ map (\(a,b) -> (xnWOaToa a, xnWOaToa b)) $ Rel.toList xrel

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

{-
idToXml::Id.Id->(HXT.XmlTree->HXT.XmlTrees)
idToXml id' = HXT.cdata (Hets.idToString id' )


idFromXml::HXT.XmlTrees->Id.Id
idFromXml = read . xshow . applyXmlFilter getChildren
-}

{-                
createPresentationForId::Id.Id->String->HXT.XmlFilter
createPresentationForId theId givenName =
  HXT.etag "presentation" += (
            (HXT.sattr "for" givenName)
    +++ xmlNL
    +++     (HXT.etag "use" += (
                    (HXT.sattr "format" "Hets")
            +++     (HXT.txt (Hets.idToString theId)) 
            ))
    +++     xmlNL
    )
                
createIdFromPresentation::HXT.XmlTree->Id.Id
createIdFromPresentation t =
  let
    idString = xshow $ applyXmlFilter (getChildren .> isTag "use" .>
      withSValue "format" "Hets" .> getChildren) [t]
  in
    read idString
-}

uniqueXmlNamesContainerWONExt::(Container c i, Container d j, Eq a)=>
  XmlNameList
  -> (a->String) -- ^ how to find an initial name for a converted item
  -> c
  -> (i->(Hets.WithOriginNode a)) 
           -- ^ specify a conversion of items (or 'id')
  -> (i->XmlName->j)
  -> (d, XmlNameList)
uniqueXmlNamesContainerWONExt xmlnames tostring container extract synthesize =
  uniqueXmlNamesContainerExt
    xmlnames
    (tostring . Hets.woItem)
    container
    (\p q -> p == q) -- sameOrigin and equalItem
    extract
    synthesize
{-        
uniqueXmlNamesContainerWON::(Eq i, Container c (Hets.WithOriginNode i), Container d (XmlNamed (Hets.WithOriginNode i)))=>
  XmlNameList->
  (a->String)->
  c->
  (i->a)->
  (d, XmlNameList)
uniqueXmlNamesContainerWON
  xmlnames
  tostring
  container
  extract =
    uniqueXmlNamesContainer
      xmlnames
      tostring
      container
      (\a b -> a == b) -- sameOrigin and equalItem
      (extract . Hets.woItem)
-}

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
                 
-- TODO : change to correct types
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
            Nothing -> error "Unknown pred!"
            (Just (_, uname)) ->
              case Hets.getNameOrigins uniqueNames uname of
                [] -> error "Whoops!"
                [o] -> (uname, getNodeNameForXml o ln)
                (o:_) -> Debug.Trace.trace ("more than one...") $ (uname, getNodeNameForXml o ln)
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
            (\( (uid, upt), _) -> uid == pr && upt == (Hets.cv_Pred_typeToPredType pt))
            (\( (uid, upt), _) -> uid == pr && compatiblePredicate currentRel upt (Hets.cv_Pred_typeToPredType pt))
        of
          Nothing -> error "Unknown op!"
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
              Nothing -> error "Unknown op!"
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

{-          find
            (\( (uid, uot), _) -> uid == op && uot == (Hets.cv_Op_typeToOpType ot))
            (Set.toList (Hets.inmGetIdNameOpSet currentMapping)) -}
        of
          Nothing -> error "Unknown op!"
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
            HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" "constraint-indices")
            +++ (HXT.etag "OMSTR" += HXT.txt (
              foldl (\s i -> (s++(show i)++"|")) "" il
              ))
            ))
          +++ xmlNL
          +++ processOperatorIN go lenv ln nn uN fN (debugGO go "pCXN" ("creating conop for " ++ (show op)) op)
          ) ) +++ xmlNL
        ) (xmlNullFilter) ops'
      ) )
    +++ xmlNL
    +++ (HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" (show origs))))) +++ xmlNL


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
        (\wrapped f -> wrapped +++ (wrapFormulaCMPIN go lenv ln nn cM uN fN f poslinemap) )
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
{-    currentMapping =
      fromMaybe
        (error "!")
        $
        Hets.inmFindLNNN (ln, nn) fullNames -}
    senxmlid =
      case
        Hets.getNameForSens [currentMapping] (Hets.stringToId $ Ann.senName ansen, sennum)
      of
        Nothing -> error ("No unique name for Sentence \"" ++ Ann.senName ansen ++ "\"")
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
      ((foldl (\cmpx p -> cmpx += (HXT.txt ("\n" ++ (Map.findWithDefault "" p poslinemap))) ) (HXT.etag "CMP") sposl) += (HXT.txt "\n"))+++ 
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


