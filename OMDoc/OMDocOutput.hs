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
module OMDoc.OMDocOutput
  (
    hetsToOMDoc
  )
  where

import qualified OMDoc.HetsDefs as Hets
import OMDoc.CASLOutput
import CASL.Sign
import CASL.AS_Basic_CASL as ABC
import qualified Common.Id as Id
import qualified Common.LibName as ASL

import Driver.Options

import Static.DevGraph
import qualified Data.Graph.Inductive.Graph as Graph

-- Often used symbols from HXT
import Text.XML.HXT.Parser
  (
      {- a_name, k_public, k_system, -} emptyRoot
    , v_1, a_indent, a_output_file
  )

import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)
import qualified Text.XML.HXT.DOM.XmlTreeTypes as HXTT hiding (when)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

import qualified Common.AS_Annotation as Ann

import Data.List (find, intercalate)

import Debug.Trace (trace)

import System.Directory

import Control.Monad

import OMDoc.Util
import OMDoc.XmlHandling
import OMDoc.OMDocDefs

import qualified OMDoc.OMDocInterface as OMDoc
import qualified OMDoc.OMDocXml as OMDocXML

import qualified Network.URI as URI
import OMDoc.Sentences

caslImportURI::URI.URI
caslImportURI =
  case
    URI.parseURIReference "Logic/casl.omdoc"
  of
    Nothing -> error "!"
    (Just u) -> u

-- DTD is currently suspended in favor of RelaxNG (DTD violates RNG)
{-
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
-}
{-
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
defaultDTDURI = "http://www.informatik.uni-bremen.de/~hiben/omdoc/dtd/omdoc.dtd"

envDTDURI::IO String
envDTDURI = getEnvDef "OMDOC_DTD_URI" defaultDTDURI
-}
{-
-- | this function wraps trees into a form that can be written by HXT
writeableTreesDTD::String->HXT.XmlTrees->HXT.XmlTree
writeableTreesDTD dtd' t =
  (HXT.NTree
    ((\(HXT.NTree a _) -> a) emptyRoot)
    ((HXT.NTree (mkOMDocTypeElem dtd' ) [])
      :(HXT.NTree (HXT.XText "\n")[])
      :t)
  )
-}

-- | this function wraps trees into a form that can be written by HXT
writeableTrees::HXT.XmlTrees->HXT.XmlTree
writeableTrees t =
  (HXT.NTree
    ((\(HXT.NTree a _) -> a) emptyRoot)
    t
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

-- | this function writes Xml with indention to a file
writeOMDoc::
  HXT.XmlTrees -- ^ tree to write
  ->String  -- ^ name of file to output to
  ->IO HXT.XmlTrees -- ^ errors are wrapped inside 'XmlTrees'
writeOMDoc t f = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_output_file, f)] $
    writeableTrees t

{-
-- | this function writes Xml with indention to a file
writeOMDocDTD::String->HXT.XmlTrees->String->IO HXT.XmlTrees
writeOMDocDTD dtd' t f = HXT.run' $
  HXT.writeDocument
    [(a_indent, v_1), (a_output_file, f)] $
    writeableTreesDTD dtd' t
-}

-- | Hets interface for writing OMDoc files.
--   Output is written into directory specified in options.
--  Create one ore more OMDoc-documents from a library-environment
hetsToOMDoc::
  HetcatsOpts -- ^ Hetcats-Options, if recurse is set, all libraries are
              --   extracted.
  ->(ASL.LIB_NAME, LibEnv) -- ^ Name of the loaded library and the environment
  ->FilePath               -- ^ Name of output-file (not used when recurse is set)
  ->IO ()
hetsToOMDoc
  hco
  (ln, lenv)
  fp
  =
    let
      -- get all names used in the environment
      flatNames = Hets.getFlatNames lenv
      -- mutliorigin
      {-
      multiOrigins = Hets.getMultiOrigins lenv
      interesting =
        Map.foldWithKey
          (\mln mset i ->
            let
              keepSets =
                Set.filter (\s -> Set.size s > 1) mset
            in
              if Set.size keepSets > 0
                then
                  Map.insert mln keepSets i
                else
                  i
          )
          Map.empty
          multiOrigins
      tryReal =
        Map.foldWithKey
          (\mln mset tR ->
            let
              remapped =
                Set.map
                  (\s ->
                    Set.map
                      (\i ->
                        Hets.traceRealIdentifierOrigins
                          lenv
                          mln
                          (Hets.woOrigin i)
                          (Hets.woItem i)
                      )
                      s
                  )
                  mset
            in
              Map.insert mln remapped tR
          )
          Map.empty
          interesting
      trying = Hets.findMultiOriginUnifications lenv interesting
      -}
      -- identify names so we know where a name has it's origin
      identMap = Hets.identifyFlatNames lenv flatNames
      -- referenced identifiers are imported and are not needed
      -- for name generation
      remMap = Hets.removeReferencedIdentifiers flatNames identMap
      -- tag same names with different origins according to their appearance
      useMap = Hets.getIdUseNumber remMap
      -- create unique names by creating new names from use tag and name
      unnMap = Hets.makeUniqueNames useMap
      -- use the unique names to created before to create a mapping
      -- of names corresponding to their use in the library environment
      uniqueNames = Hets.makeUniqueIdNameMapping lenv unnMap
      -- similar to uniqueNames but also populate the mappings with all
      -- names known in a theory (still annotated with their origin)
      -- (_, collectionMap) = Hets.makeFullNames lenv unnMap identMap
      collectionMap = Hets.makeCollectionMap lenv unnMap identMap
      -- transform names to XML-conform strings
      uniqueNamesXml = (createXmlNameMapping uniqueNames)
      outputio =
        -- write all libraries in the library environment ?
        if recurse hco
          then
            do
              -- putStrLn ("Multi: " ++ (show interesting) ++ " -> " ++ (show tryReal))
              -- dtduri <- envDTDURI
              mapM
                (\libname ->
                  let
                    -- get filename of library
                    filename = unwrapLinkSource libname
                    modtime = ASL.getModTime (ASL.getLIB_ID libname)
                    -- transform to an OMDoc-filename in outout directory
                    outfile = fileSandbox (outdir hco) $ asOMDocFile filename
                  in
                    do
                      -- create OMDoc
                      doesExists <- System.Directory.doesFileExist outfile
                      keepFile <-
                        -- do not keep, if there is no time info or no file...
                        if (modtime /= ASL.noTime) && doesExists
                          then
                            do
                              mTime <-
                                System.Directory.getModificationTime outfile
                              -- keep xml if newer
                              return (mTime > modtime)
                          else
                            return False
                      if keepFile
                        then
                          do
                            putStrLn
                              (
                                "Keeping \""
                                ++ outfile
                                ++ "\" (newer than corresponding library)..."
                              )
                            return ()
                        else
                          do
                            omdoc <-
                              libEnvLibNameIdNameMappingToOMDoc
                                (emptyGlobalOptions { hetsOpts = hco })
                                lenv
                                libname
                                (createLibName libname)
                                uniqueNamesXml
                                collectionMap
                            -- transform to HXT-Data
                            omdocxml <- return $ (OMDocXML.toXml omdoc) HXT.emptyRoot
                            -- Tell user what we do
                            putStrLn ("Writing " ++ filename ++ " to " ++ outfile)
                            -- setup path
                            System.Directory.createDirectoryIfMissing True (snd $ splitPath outfile)
                            --writeOMDocDTD dtduri omdocxml outfile >> return ()
                            -- write XML to the file
                            writeOMDoc omdocxml outfile >> return ()
                )
                (Map.keys lenv) -- all libnames
              return ()
          else -- only single library
            do
              -- putStrLn ("Multi: " ++ (show interesting))
              -- dtduri <- envDTDURI
              -- create OMDoc
              omdoc <-
                libEnvLibNameIdNameMappingToOMDoc
                  (emptyGlobalOptions { hetsOpts = hco })
                  lenv
                  ln
                  (createLibName ln)
                  uniqueNamesXml
                  collectionMap
              -- transform to HXT-Data
              omdocxml <- return $ (OMDocXML.toXml omdoc) HXT.emptyRoot
              --writeOMDocDTD dtduri omdocxml fp >> return ()
              -- write to given file
              writeOMDoc omdocxml fp >> return ()
    in
        -- actually perform IO
        outputio

{-
 assuming unique names in a list of 'IdNameMapping'S each id (String) is
 converted to an xml:id-conform string by replacing invalid characters
-}
{- |
  create xml ids from unique names. Adjusts names to conform to XML-Standards.
-}
createXmlNameMapping::
  [Hets.IdNameMapping]
  ->[Hets.IdNameMapping]
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
--      , idNameConsSet
      , idNameGaPredSet
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
--        , Set.map (\(a, uN) -> (a, adjustStringForXmlName uN)) idNameConsSet
        , Set.map (\(a, uN) -> (a, adjustStringForXmlName uN)) idNameGaPredSet
      )
    )

caslLogicImports::OMDoc.Imports
caslLogicImports =
  OMDoc.Imports caslImportURI Nothing Nothing OMDoc.ITGlobal OMDoc.CNone

-- | translate a definitional link to OMDoc (/imports/)
createOMDefLink::
  Static.DevGraph.LibEnv -- ^ library environment
  ->ASL.LIB_NAME        -- ^ library (where link occures)
  ->Graph.LEdge Static.DevGraph.DGLinkLab -- ^ the link
  ->[Hets.IdNameMapping] -- ^ mapping of unique names (Hets\<->OMDoc)
--  ->[Hets.IdNameMapping] -- ^ mapping of names (Hets\<->OMDoc)
  ->Hets.CollectionMap
  ->OMDoc.Imports
createOMDefLink lenv ln (from, to, ll) uniqueNames {-names-} collectionMap =
  let
    e_fname = "OMDoc.OMDocOutput.createOMDefLink: "
    dg = lookupDGraph ln lenv
    fromnode = labDG dg from
    fromname =
      case
        find
          (\ inm ->
            Hets.inmGetLibName inm == ln && Hets.inmGetNodeNum inm == from
          )
          uniqueNames
      of
        Nothing ->
          error (e_fname ++ "No such node in names!")
        (Just inm) -> Hets.inmGetNodeId inm
    liburl =
      if isDGRef fromnode
        then
          asOMDocFile $ unwrapLinkSource $ dgn_libname fromnode
        else
          ""
    linktype = if isLocalDef $ dgl_type ll
               then OMDoc.ITLocal
               else OMDoc.ITGlobal
    mommorph = createOMMorphism lenv ln (from, to, ll) uniqueNames {-names-} collectionMap
    fromuri = case URI.parseURIReference (liburl ++ "#" ++ fromname) of
      Nothing ->
        error (e_fname ++ "Error parsing URI!")
      (Just u) -> u
  in
    OMDoc.Imports fromuri mommorph Nothing linktype OMDoc.CNone

{-
  since 'conservativity' has been dropped from
  x-inclusionS, it should be carried by an
  imports element that refers to the x-inclusion
  via 'base'
-}
-- | translate a theorem-link to OMDoc (/(axiom|theory)-inclusion/).
--   This may result in an additional /imports/-element for the /linked-to/-theory
--   carrying conservativity-information.
createXmlThmLinkOM::
    Int -- ^ link number (for disambiguation when there are multiple similar links)
  ->Static.DevGraph.LibEnv -- ^ library environment
  ->ASL.LIB_NAME -- ^ library (where link occures)
  ->Graph.LEdge Static.DevGraph.DGLinkLab -- ^ the link
  ->[Hets.IdNameMapping] -- ^ mapping of unique names (Hets\<->OMDoc)
--  ->[Hets.IdNameMapping] -- ^ mapping of names (Hets\<->OMDoc)
  ->Hets.CollectionMap
  ->(OMDoc.Inclusion, Maybe OMDoc.Imports)
createXmlThmLinkOM lnum lenv ln (edge@(from, to, ll)) uniqueNames {-names-} collectionMap =
  let
    e_fname = "OMDoc.OMDocOutput.createXmlThmLinkOM: "
    dg = lookupDGraph ln lenv
    fromnode =
        labDG dg from
    tonode =
        labDG dg to
    fromname =
      case
        find
          (\inm ->
            Hets.inmGetLibName inm == ln && Hets.inmGetNodeNum inm == from
          )
          uniqueNames
      of
        Nothing ->
          error (e_fname ++ "No such node in names!")
        (Just inm) -> Hets.inmGetNodeId inm
    toname =
      case
        find
          (\inm ->
            Hets.inmGetLibName inm == ln && Hets.inmGetNodeNum inm == to
          )
          uniqueNames
      of
        Nothing ->
          error (e_fname ++ "No such node in names!")
        (Just inm) -> Hets.inmGetNodeId inm
    -- if the link comes from a referenced library
    -- we need the (assumed) URL of this library to build
    -- the OMDoc-link
    liburl =
      if isDGRef fromnode
        then
          asOMDocFile $ unwrapLinkSource $ dgn_libname fromnode
        else
          ""
    -- the same applies to links into referenced libraries
    toliburl =
      if isDGRef tonode
        then
          asOMDocFile $ unwrapLinkSource $ dgn_libname tonode
        else
          ""
    -- does this link get translated into an axiom-inclusion ?
    isaxinc = isLocalEdge $ dgl_type ll
    -- translate conservativity
    cons = consConv . getCons $ dgl_type ll
    touri = case URI.parseURIReference (toliburl ++ "#" ++ toname) of
      Nothing -> error (e_fname ++ "Error parsing URI (to)!")
      (Just u) -> u
    fromuri = case URI.parseURIReference (liburl ++ "#" ++ fromname) of
      Nothing -> error (e_fname ++ "Error parsing URI (from)!")
      (Just u) -> u
    -- construct a (somewhat) human readable id for this link
    iid =
      (if isaxinc then "ai" else "ti")
        ++ "." ++ toname ++ "." ++ fromname ++ "_" ++ (show lnum)
    -- create morphism if necessary
    mommorph' = createOMMorphism lenv ln edge uniqueNames {-names-} collectionMap
    mommorph =
      -- if we have a helper-imports we need to modify the base of the morphism
      -- (or even create an empty morphism)
      case helpimports of
        Nothing -> mommorph'
        _ ->
          case mommorph' of
            Nothing ->
              Just
                $
                OMDoc.Morphism
                  {
                      OMDoc.morphismId = Nothing
                    , OMDoc.morphismHiding = []
                    , OMDoc.morphismBase = [iid ++ "-base"]
                    , OMDoc.morphismRequations = []
                  }
            (Just mm') ->
              Just (mm' { OMDoc.morphismBase = (OMDoc.morphismBase mm') ++ [iid ++ "-base"] })
    -- a helper imports is needed to carry conservativity  (the feature has been taken out of
    -- OMDoc, so we need this workaround)
    helpimports =
      case cons of
        OMDoc.CNone -> Nothing
        _ ->
          Just $
            OMDoc.Imports
              fromuri
              (
                Just
                  $
                  OMDoc.Morphism
                    (Just (iid ++ "-base"))
                    []
                    []
                    []
              )
              Nothing
              (if isaxinc then OMDoc.ITLocal else OMDoc.ITGlobal)
              cons -- the reason for this
  in
    if isaxinc
      then
        (OMDoc.AxiomInclusion fromuri touri mommorph (Just iid) cons, helpimports)
      else
        (OMDoc.TheoryInclusion fromuri touri mommorph (Just iid) cons, helpimports)
  where
  consConv::Static.DevGraph.Conservativity->OMDoc.Conservativity
  consConv Static.DevGraph.None = OMDoc.CNone
  consConv Static.DevGraph.Mono = OMDoc.CMonomorphism
  consConv Static.DevGraph.Cons = OMDoc.CConservative
  consConv Static.DevGraph.Def = OMDoc.CDefinitional


{- |
  create a xml-representation of a (CASL-)morphism.
-}
createOMMorphism::
  Static.DevGraph.LibEnv -- ^ library environment
  ->ASL.LIB_NAME -- ^ library (of morphism)
  ->Graph.LEdge Static.DevGraph.DGLinkLab -- ^ link carrying morphism
  ->[Hets.IdNameMapping] -- ^ mapping of unique names (Hets\<->OMDoc)
--  ->[Hets.IdNameMapping] -- ^ mapping of names (Hets\<->OMDoc)
  ->Hets.CollectionMap
  ->Maybe OMDoc.Morphism
createOMMorphism
  lenv
  ln
  (from, to, ll)
  uniqueNames
--  names
  collectionMap
  =
  let
    e_fname = "OMDoc.OMDocOutput.createOMMorphism: "
    caslmorph = Hets.getCASLMorphLL ll
    dg = lookupDGraph ln lenv
    fromnode =
        labDG dg from
    tonode =
        labDG dg to
    fromSign = Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign fromnode)
    toSign = Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign tonode)
    fromRel = sortRel fromSign
    toRel = sortRel toSign
    -- get name mapping from the from-node
    fromIds = Hets.getIdentifierAt collectionMap (ln, from)
    toIds = Hets.getIdentifierAt collectionMap (ln, to)

    fromSortIds = Hets.getSortsAt collectionMap (ln, from)
    fromPredIds = Hets.getPredsAt collectionMap (ln, from)
    fromOpIds = Hets.getOpsAt collectionMap (ln, from)

    toSortIds = Hets.getSortsAt collectionMap (ln, to)
    toPredIds = Hets.getPredsAt collectionMap (ln, to)
    toOpIds = Hets.getOpsAt collectionMap (ln, to)

    {-
    fromIdNameMapping =
      Data.Maybe.fromMaybe
        (error (e_fname ++ "Cannot find Id-Name-Mapping (from)!"))
        $
        Hets.inmFindLNNN (ln, from) names
    -- get name mapping from the to-node
    toIdNameMapping =
      Data.Maybe.fromMaybe
        (error (e_fname ++ "Cannot find Id-Name-Mapping (to)!"))
        $
        Hets.inmFindLNNN (ln, to) names
    -}
    -- retrieve the XML-names for the sort mapping
    -- retrieved names are all of same type, so merge
    allmapped = mappedsorts fromSortIds e_fname toSortIds ln collectionMap
                                                uniqueNames from to caslmorph
                        ++ mappedpreds fromPredIds e_fname caslmorph toPredIds ln
                                                collectionMap uniqueNames fromRel from toRel to
                        ++ mappedops fromOpIds e_fname caslmorph toOpIds ln
                                                collectionMap uniqueNames fromRel from toRel to -- ++ unclashedSorts
    -- merging makes hiding easier also...
    hidden = if isHidingEdge $ dgl_type ll
             then mkHidingB fromIds toIds allmapped
             else []
    reqs =
      foldl
        (\r ((f,(fb,fo)), (t,(tb,to'))) ->
          r
          ++
          [
            (
                OMDoc.MTextOM $ OMDoc.mkOMOBJ $ OMDoc.mkOMS fb fo (adjustStringForXmlName f)
              , OMDoc.MTextOM $ OMDoc.mkOMOBJ $ OMDoc.mkOMS tb to' (adjustStringForXmlName t)
            )
          ]
        )
        []
        allmapped
  in
    -- empty morphism still can contain hiding information
    if Hets.isEmptyMorphism caslmorph && null hidden
      then
        Nothing
      else
        -- construct morphism
        Just $ OMDoc.Morphism Nothing hidden [] reqs
  where
  -- find the hidden symbols by comparing the name mappings
  -- from each node and the mapping created by the morphism
  {-
  mkHiding::Hets.IdNameMapping->Hets.IdNameMapping->[((String,a),b)]->[String]
  mkHiding fromIdNameMapping toIdNameMapping mappedIds =
    let
      -- uniformly get all symbols
      idsInFrom = Hets.inmGetIdNameAllSet fromIdNameMapping
      idsInTo = Hets.inmGetIdNameAllSet toIdNameMapping
    in
      -- for every symbol in the source node...
      Set.fold
        (\(_, fname) h ->
          case
            -- try to find it in the mapping...
            find
              (\( (fname', _)  , _ ) -> fname == fname')
              mappedIds
          of
            -- it's not in the mapping...
            Nothing ->
              if
                -- make sure that it is not already defined in the target node
                Set.null
                  $
                  Set.filter
                    (\(_, tname) -> tname == fname)
                    idsInTo
                then
                  -- then this symbol is hidden
                  h ++ [fname]
                else
                  h
            _ -> h
        )
        []
        idsInFrom
  -}
  mkHidingB::[(a, String)]->[(b, String)]->[((String,c),d)]->[String]
  mkHidingB fromIds toIds mappedIds =
    -- for every symbol in the source node...
    foldl
      (\h (_, fname) ->
        case
          -- try to find it in the mapping...
          find
            (\( (fname', _)  , _ ) -> fname == fname')
            mappedIds
        of
          -- it's not in the mapping...
          Nothing ->
            if
              -- make sure that it is not already defined in the target node
              null
                $
                filter
                  (\(_, tname) -> tname == fname)
                  toIds
              then
                -- then this symbol is hidden
                h ++ [adjustStringForXmlName fname]
              else
                h
          _ -> h
      )
      []
      fromIds



{- |
  filter definitional links (LocalDef, GlobalDef, HidingDef, FreeDef, CofreeDef)
-}
filterDefLinks::
  [Graph.LEdge Static.DevGraph.DGLinkLab]
  ->[Graph.LEdge Static.DevGraph.DGLinkLab]
filterDefLinks =
  filter
    (\(_, _, ll) -> isDefEdge $ dgl_type ll)

{- |
  filter theorem links (LocalThm, GlobalThm, HidingThm)
-}
filterThmLinks::
  [Graph.LEdge Static.DevGraph.DGLinkLab]
  ->[Graph.LEdge Static.DevGraph.DGLinkLab]
filterThmLinks =
  filter
    (\(_, _, ll) -> not . isDefEdge $ dgl_type ll)

-- | translate operators representing sort constructors to
--   OMDoc-ADT-constructors.
createConstructorsOM::
  ASL.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->Hets.CollectionMap
  ->Set.Set (OpType, String)
  ->[OMDoc.Constructor]
createConstructorsOM
  ln
  nn
  uniqueNames
  collectionMap
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
            collectionMap
            c
        ]
      )
      []
      conset

-- | translate a single sort constructing operator to
-- an OMDoc-ADT-constructor
createConstructorOM::
  ASL.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->Hets.CollectionMap
  ->(OpType, String)
  ->OMDoc.Constructor
createConstructorOM
  ln
  nn
  uniqueNames
  collectionMap
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
                    collectionMap
                    arg
              )
          ]
        )
        []
        (opArgs ot) -- op result is not needed. it is bound by the ADT
    )

{- |
  check if a relation contains information about a certain sort
-}
emptyRelForSort::Rel.Rel SORT->SORT->Bool
emptyRelForSort rel s =
  null $ filter (\(s', _) -> s' == s) $ Rel.toList rel

-- | create an OMDoc-Abstract-Data-Type for a sort
--   with respect to the relation of sorts and previously
--   translated sort constructors.
createADTFor::
    String
  ->Rel.Rel SORT
  ->SORT
  ->ASL.LIB_NAME
  ->Graph.Node
  ->[Hets.IdNameMapping]
  ->Hets.CollectionMap
  ->[OMDoc.Constructor] -- ^ contructors generated via 'createConstructorsOM'
  ->[SORT]
  ->(OMDoc.ADT, [SORT])
createADTFor theoname rel s ln nn uniqueNames collectionMap constructors fixed =
  let
    (_, adtSortId') =
      findOriginId
        collectionMap
        uniqueNames
        Hets.findIdIdsForId
        (ln, nn)
        s
        " OMDoc.createADTFor"

    adtSortId = adjustStringForXmlName adtSortId'

    --  adtSortID = getSortIdName idNameMapping s
    -- compute insorts for this ADT and find out
    -- for which sorts this sort should show up
    -- in an insort-element but does not
    (insorts, recogs, pins) =
      foldl
        (\(is, recogs', pins') (s'', s') ->
          let
            (_, spUname) =
              findOriginId
                collectionMap
                uniqueNames
                Hets.findIdIdsForId
                (ln, nn)
                s'
                " OMDoc.createADTFor"
            (_, sppUname) =
              findOriginId
                collectionMap
                uniqueNames
                Hets.findIdIdsForId
                (ln, nn)
                s''
                " OMDoc.createADTFor"
          in
            -- normal insort, this means s'' needs to appear
            -- in an insort in this ADT
            if s' == s
              then
                (
                    is
                    ++
                    [
                      OMDoc.mkInsort
                        (OMDoc.mkSymbolRef (adjustStringForXmlName sppUname))
                        --(OMDoc.mkSymbolRef (getSortIdName idNameMapping s''))
                    ]
                  , recogs'
                  , pins'
                )
              else
                -- this means that this sort should be in an insort for s'
                -- but maybe s' has already been defined (fixed)
                if s'' == s && elem s' fixed
                  then
                    let
                      recognizer =
                        OMDoc.mkRecognizer
                            (
                              "recognizer_"
                              ++ (adjustStringForXmlName spUname)
                              -- ++ (getSortIdName idNameMapping s')
                              ++ "_in_"
                              ++ adtSortId
                            )
                      -- this debug message is a reminder to
                      -- find a way out of this...
                    in
                      Debug.Trace.trace
                        ("Generating recognizer for " ++ (show s) ++ " in " ++ (show s'))
                        (is, recogs' ++ [recognizer], pins' ++ [s'])
                  else
                    -- is s' is not fixed, the ADT will be generated later
                    (is, recogs', pins')
        )
        ([], [], [])
        (Rel.toList $ Rel.transReduce rel)
  in
    (
        OMDoc.mkADTEx
          (Just (theoname ++ "-" ++ adtSortId ++ "-adt"))
          $
          [
            OMDoc.mkSortDef
              adtSortId
--              (getSortIdName idNameMapping s)
              constructors
              insorts
              recogs
          ]
      , pins
    )

{-
-- | lookup a symbols XML-name
lookupIdName::
  Set.Set (Id.Id, String) -- ^ Set containing associating tuples
  ->Id.Id                 -- ^ Symbol to lookup
  ->Maybe String
lookupIdName ss sid =
  case
    find
      (\(sid', _) -> sid' == sid)
      (Set.toList ss)
  of
    Nothing -> Nothing
    (Just x) -> Just (snd x)

-- | lookup a sorts XML-name
getSortIdName::
    Hets.IdNameMapping -- ^ Mapping to use
  ->Id.Id              -- ^ Sort to lookup
  ->String
getSortIdName idNameMapping sid =
  Data.Maybe.fromMaybe
    (error "OMDoc.OMDocOutput.getSortIdName: Cannot find name!")
    $
    lookupIdName (Hets.inmGetIdNameSortSet idNameMapping) sid
-}

-- | convert a library from a library-environment into OMDoc
libEnvLibNameIdNameMappingToOMDoc::
  GlobalOptions           -- ^ HetcatsOpts and debugging information
  ->LibEnv                -- ^ Library-Environment to process
  ->ASL.LIB_NAME         -- ^ Libary to process
  ->OMDoc.XmlId           -- ^ Name (xml:id) for OMDoc-Document
  ->[Hets.IdNameMapping]  -- ^ Mapping of unique names (Hets\<->XML)
  ->Hets.CollectionMap
  ->IO OMDoc.OMDoc
libEnvLibNameIdNameMappingToOMDoc
  go
  lenv
  ln
  omdocId
  uniqueNames
  collectionMap
  =
    let
      e_fname = "OMDoc.OMDocOutput.libEnvLibNameIdNameMappingToOMDoc: "
      dummyTheoryComment =
        (
          Just $ "This theory is not used. It serves only as a semantic"
            ++ " 'anchor' for theory- and axiom-inclusions."
        )
      dg = lookupDGraph ln lenv
      -- get all theorem links pointing
      -- to external libraries
      thmLinksToRefs =
        filter
          (\ (_, to, _) -> isDGRef $ labDG dg to
          )
          (filterThmLinks $ labEdgesDG dg)
      -- translate these external links to OMDoc
      -- and create helper imports to preserve
      -- conservativity information
      (thmLinksToRefsOM, dummyImports) =
        foldl
          (\(tL, dI) (lnum, edge) ->
            let
              (newTL, mDI) =
                createXmlThmLinkOM
                  lnum
                  lenv
                  ln
                  edge
                  uniqueNames
                  collectionMap
            in
              case mDI of
                Nothing -> (tL ++ [newTL], dI)
                (Just newDI) -> (tL ++ [newTL], dI ++ [newDI])
          )
          ([], [])
          (zip [1..] thmLinksToRefs) -- numbers for disambiguation
      -- dummy-theory to attach links with information to it
      dummyTheory =
        OMDoc.Theory
          "import-dummy-for-hets"
          (map OMDoc.CIm dummyImports)
          []
          dummyTheoryComment
      -- initial present theories.
      -- either none or the dummy
      initTheories =
        case dummyImports of
          [] -> []
          _ -> [dummyTheory]
      -- create an initial (emtpy) OMDoc-Document
      initialOMDoc =
        OMDoc.OMDoc omdocId initTheories thmLinksToRefsOM
      -- appending theories and inclusions must be done
      -- in the IO-Monad because axioms pull in their
      -- original (CASL) Source in CMP elements
      omdocio =
        foldl
          (\xio (nn, node) -> -- fold over labnodes
            do
              -- get current OMDoc and a list of created ADTs
              -- The ADTs are needed to work around changing
              -- sort-relation-information
              (omdoc, fixedADTs) <- xio
              -- this is the new state (OMDoc, ADTs)
              res <-
                let
                  dgnodename = dgn_name node
                  caslsign = (\(Just a) -> a) $ Hets.getCASLSign (dgn_sign node)
                  -- get the (unique) name mapping for this theory (node)
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
                      Nothing -> error (e_fname ++ "No such name...")
                      (Just a) -> a
                  -- previously computed unique theory name for XML
                  theoryXmlId = (Hets.inmGetNodeId uniqueidnamemapping)
                  -- create presentatio symbol for this theory
                  -- (does this make sense in OMDoc ?)
                  theoryPresentation =
                    makePresentationForOM
                      theoryXmlId
                      (Hets.idToString $ Hets.nodeNameToId dgnodename)
                  -- create definitional links for the theory (imports)
                  theoryDefLinks =
                    caslLogicImports:
                      map
                        (\edge ->
                          createOMDefLink
                            lenv
                            ln
                            edge
                            uniqueNames
                            collectionMap
                        )
                        (filterDefLinks (innDG dg nn))
                  -- process ADTs for this theory and keep track of changing sort relations
                  (theoryADTs, theoryLateInsorts, theorySorts, theoryPresentations, adtList) =
                    Set.fold
                     (\s (tadts, tlis, tsorts, tpres, adtl) ->
                      let
                        sortcons =
                          Set.map
                            (\((_, t, _, _), uname) -> (t, uname))
                            $
                            Set.filter
                              (\((_, _, _, a), _) -> a == s)
                              (Hets.inmGetIdNameConstructors uniqueidnamemapping)
                        -- constructors for current sort (s)
                        -- translate to XML (children of adt)
                        constructors =
                          createConstructorsOM
                            ln
                            nn
                            uniqueNames
                            collectionMap
                            sortcons
                      in
                        case
                          find
                            (\(uid, _) -> uid == s)
                            (Set.toList (Hets.inmGetIdNameAllSet uniqueidnamemapping))
                        of
                          -- sort has no origin here...
                          Nothing ->
                            if (Set.size sortcons) > 0
                              then -- some constructors have been introduced here
                                let
                                  -- create ADT (and record new insorts)
                                  (newadt, adtlis) =
                                    createADTFor
                                      theoryXmlId
                                      (sortRel caslsign)
                                      s
                                      ln
                                      nn
                                      uniqueNames
                                      collectionMap
                                      constructors
                                      adtl
                                  newlis =
                                    case adtlis of
                                      [] -> []
                                      _ ->
                                        let
                                        (_, sortUName) =
                                          findOriginId
                                            collectionMap
                                            uniqueNames
                                            Hets.findIdIdsForId
                                            (ln, nn)
                                            s
                                            " OMDoc.createADTFor"
                                        in
                                        -- if there are new insorts find xml-name
                                        -- and create typed variables (name == sort)
                                        -- for later use (in OpenMath)
                                        [
                                          (
                                              adjustStringForXmlName sortUName
                                            , createTypedVarOM
                                                ln
                                                nn
                                                uniqueNames
                                                collectionMap
                                                s
                                                (show s)
                                            , map
                                                (\s' ->
                                                  createTypedVarOM
                                                    ln
                                                    nn
                                                    uniqueNames
                                                    collectionMap
                                                    s'
                                                    (show s')
                                                )
                                                adtlis
                                            , map
                                                (\s' ->
                                                  let
                                                    (_, sortUName') =
                                                      findOriginId
                                                        collectionMap
                                                        uniqueNames
                                                        Hets.findIdIdsForId
                                                        (ln, nn)
                                                        s'
                                                        " OMDoc.createADTFor"
                                                  in
                                                    adjustStringForXmlName sortUName'
                                                )
                                                adtlis
                                            , map
                                                (\s' ->
                                                  createSymbolForSortOM
                                                    ln
                                                    nn
                                                    uniqueNames
                                                    collectionMap
                                                    s'
                                                )
                                                adtlis
                                          )
                                        ]
                                in
                                  (tadts ++ [newadt], tlis ++ newlis, tsorts, tpres, adtl ++ [s])
                              else
                                -- Nothing new (no origin here and no new constructors)
                                (tadts, tlis, tsorts, tpres, adtl)
                          -- this is the origin of the sort (normal case)
                          (Just (uid, uname)) ->
                            let
                              -- create sort symbol with reference to ADT
                              -- (not used yet, but conforms to OMDoc)
                              newsort =
                                genSortToXmlOM
                                  (
                                    case OMDoc.adtId newadt of
                                      Nothing ->
                                        Debug.Trace.trace "ADT without ID..."
                                        (show uid)
                                      (Just aid) -> aid
                                  )
                                  (XmlNamed s uname)
                              -- create ADT and keep track of new insorts
                              (newadt, adtlis) =
                                createADTFor
                                  theoryXmlId
                                  (sortRel caslsign)
                                  uid
                                  ln
                                  nn
                                  uniqueNames
                                  collectionMap
                                  constructors
                                  adtl
                              -- create presentation for the sort
                              newpre =
                                makePresentationForOM
                                  uname
                                  (Hets.idToString s)
                              -- record new sorts
                              newsorts = tsorts ++ [newsort]
                               -- " new presentations
                              newpres = tpres ++ [newpre] {- ++ conpres -}
                              -- check new adts and insorts
                              (newadts, newlis) =
                                -- only record ADT if it would contain information
                                -- about the sort relation or sort constructors
                                if (not $ emptyRelForSort (sortRel caslsign) uid)
                                  || ( (Set.size sortcons) > 0 )
                                  then
                                    (
                                        tadts++[newadt]
                                      , tlis
                                        ++
                                        [
                                          (
                                              uname
                                            , createTypedVarOM
                                                ln
                                                nn
                                                uniqueNames
                                                collectionMap
                                                s
                                                uname
                                            , map
                                                (\s' ->
                                                  createTypedVarOM
                                                    ln
                                                    nn
                                                    uniqueNames
                                                    collectionMap
                                                    s'
                                                    (show s')
                                                )
                                                adtlis
                                            , map
                                                (\s' ->
                                                  let
                                                    (_, sortUName') =
                                                      findOriginId
                                                        collectionMap
                                                        uniqueNames
                                                        Hets.findIdIdsForId
                                                        (ln, nn)
                                                        s'
                                                        " OMDoc.createADTFor"
                                                  in
                                                    adjustStringForXmlName sortUName'
                                                )
                                                adtlis
                                            , map
                                                (\s' ->
                                                  createSymbolForSortOM
                                                    ln
                                                    nn
                                                    uniqueNames
                                                    collectionMap
                                                    s'
                                                )
                                                adtlis
                                          )
                                        ]
                                    )
                                  else
                                    -- ...else the ADT would say nothing
                                    (tadts, tlis)
                            in
                              (newadts, newlis, newsorts, newpres, adtl ++ [uid])
                     )
                     -- start empty, except for known ADTs
                     ([],[],[],[],fixedADTs)
                     -- calculate ADTs for all sorts
                     (sortSet caslsign)
                  -- translate to OMDoc
                  (theoryPreds, pPres) =
                    foldl
                      (\(tPr', tP') ((pidwo, pt), puname) ->
                        let
                          newpred =
                            predicationToXmlOM
                              ln
                              nn
                              uniqueNames
                              collectionMap
                              (Hets.getIdId $ Hets.woItem pidwo, pt)
                          newpres =
                            makePresentationForOM
                              (adjustStringForXmlName puname)
                              (Hets.idToString $ Hets.getIdId $ Hets.woItem pidwo)
                        in
                          (tPr' ++ [newpred], tP' ++ [newpres])
                      )
                      ([],[])
                      (Hets.getDefinedPredsAt collectionMap (ln, nn))
                  -- translate operators to OMDoc
                  (theoryOps, oPres) =
                    foldl
                      (\(tO', tP') ((oidwo, ot), ouname) ->
                        let
                          newop =
                            operatorToXmlOM
                              ln
                              nn
                              uniqueNames
                              collectionMap
                              (Hets.getIdId $ Hets.woItem oidwo, ot)
                          newpres =
                            makePresentationForOM
                              (adjustStringForXmlName ouname)
                              (Hets.idToString $ Hets.getIdId $ Hets.woItem oidwo)
                        in
                          (tO' ++ [newop], tP' ++ [newpres])
                      )
                      ([],[])
                      (Hets.getDefinedOpsAt collectionMap (ln, nn))
                  -- translate theorem links to OMDoc
                  (theoryThmLinks, theoryDummyImports) =
                    foldl
                      -- ...for every (tagged) theorem link...
                      (\(tTL, tDI) (lnum, edge) ->
                        let
                          -- create OMDoc translation and maybe a Dummy-link
                          (newtTL, mtDI) =
                            createXmlThmLinkOM
                              lnum
                              lenv
                              ln
                              edge
                              uniqueNames
                              collectionMap
                        in
                          -- check if there is a Dummy
                          case mtDI of
                            Nothing -> (tTL ++ [newtTL], tDI)
                            (Just newtDI) -> (tTL ++ [newtTL], tDI ++ [newtDI])
                      )
                      ([],[])
                      (zip [1..] (filterThmLinks $ innDG dg nn))
                  -- recognizers are formally references to
                  -- predicates that decide whether their argument
                  -- belongs to the sort defined in
                  -- the sortdef.
                  --
                  -- here the semantic is to signal that this
                  -- sort is a subsort of the sort in the argument
                  -- and that thus all members of this sort are
                  -- also members of the sort in the argument
                  --
                  -- note that the predicates do not exists;
                  -- the Hets-sort-definition-axioms can't be parsed
                  -- easily into the OMDoc-Model (?).
                  omRecognizers =
                    foldl
                      (\oS (lateSort, _, _, insorts, syms) ->
                        if null insorts
                          then
                            oS
                          else
                            oS
                              ++
                              (
                              map
                                (\(is, isSym) ->
                                    let
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
                                                        Nothing
                                                        "casl"
                                                        "predication"
                                                    , OMDoc.toElement isSym
                                                  ]
                                                )
                                    in
                                      OMDoc.mkSymbolE
                                        Nothing
                                        (
                                          "recognizer_"
                                            ++ is
                                            ++ "_in_"
                                            ++ lateSort
                                        )
                                        OMDoc.SRObject
                                        (Just typeobj)
                                )
                                (zip insorts syms)
                              )
                      )
                      []
                      theoryLateInsorts
                in
                  do
  --                  omdoc <- xio
                    -- translate formulas (axiom/definition + presentation)
                    -- (reason for IO)
                    (omAxs, omDefs, omPres) <-
                      wrapFormulasCMPIOOM
                        go
                        lenv
                        ln
                        nn
                        uniqueNames
                        collectionMap
                        (Hets.getNodeSentences node)
                    -- is the current node a reference ?
                    if isDGRef node
                      then
                        -- never mind...
                        return (omdoc, adtList)
                      else
                        let
                          -- if there are _any_ dummy imports
                          -- generate a single dummy theory
                          -- for this theory
                          mDummyTheory =
                            case theoryDummyImports of
                              [] -> Nothing
                              _ ->
                                Just
                                  $
                                  OMDoc.Theory
                                    (theoryXmlId ++ "-dummy")
                                    (map OMDoc.mkCIm theoryDummyImports)
                                    []
                                    dummyTheoryComment
                          -- create new theory with all created elements
                          newtheory =
                            OMDoc.Theory
                              theoryXmlId
                              (
                                (map OMDoc.mkCIm theoryDefLinks)
                                ++
                                (map OMDoc.mkCSy theorySorts)
                                ++
                                (map OMDoc.mkCSy theoryOps)
                                ++
                                (map OMDoc.mkCSy theoryPreds)
                                ++
                                (map OMDoc.mkCAd theoryADTs)
                                ++
                                (map OMDoc.mkCSy omRecognizers)
                                ++
                                (map OMDoc.mkCAx omAxs)
                                ++
                                (map OMDoc.mkCDe omDefs)
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
                              Nothing
                          -- and finally, if there is a dummy, prepend it to the new theory
                          newTheories =
                            case mDummyTheory of
                              Nothing -> [newtheory]
                              (Just dt) -> [dt, newtheory]
                        in
                          -- insert new theory and new inclusions
                          return
                          (
                              (
                                OMDoc.addInclusions
                                  (
                                    OMDoc.addTheories
                                      omdoc
                                      newTheories
                                  )
                                  theoryThmLinks
                              )
                            , adtList -- the new adt list
                          )
              return res -- so close, so far... ^^
          )
          (return (initialOMDoc, [])) -- start with initial
          (labNodesDG dg) -- all nodes
    in
      omdocio >>= \(om, _) -> return om -- strip adtlist

{-
{- |
  alias for 'Hets.inmGetNodeId'
-}
getNodeNameForXml::Hets.IdNameMapping->String
getNodeNameForXml = Hets.inmGetNodeId
-}


-- | create an OMDoc-/symbol/ defining a predication.
--
-- Results in something like (/typenameX/ encodes signature):
--
-- @
--   \<symbol role=\"object\" name=\"/predname/\">
--     \<type system=\"casl\">
--       \<OMOBJ>
--         \<OMA>
--           \<OMS cd=\"casl\" name=\"predication\">
--           \<OMS cd=\"/libnameOfType1/\" name=\"/typename1/\">
--           \<OMS cd=\"/libnameOfType2/\" name=\"/typename2/\">
--           /.../
--         \<\/OMA>
--       \<\/OMOBJ>
--     \<\/type>
--   \<\/symbol>
-- @
predicationToXmlOM::
  ASL.LIB_NAME -- ^ library name of predication
  ->Graph.Node -- ^ node of predication
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->(Id.Id, PredType) -- ^ predication to translate
  ->OMDoc.Symbol
predicationToXmlOM
  ln
  nn
  uniqueNames
  collectionMap
  (pid, pt)
  =
    let
      e_fname = "OMDoc.OMDocOutput.predicationToXmlOM: "
      preds = Hets.getPredsAt collectionMap (ln, nn)
      validPreds =
        filter
          (\((predidwo, pt'), _) ->
            Hets.getIdId (Hets.woItem predidwo) == pid
            && pt' == pt
          )
          preds
      pidxmlid =
        case validPreds of
          [] ->
            (error (e_fname ++ "No name for \"" ++ show pid ++ "\""))
          ((_, uN):_) -> uN
      argnames =
        map
          (\args ->
            let
              (_, sortUName) =
                findOriginId
                  collectionMap
                  uniqueNames
                  Hets.findIdIdsForId
                  (ln, nn)
                  args
                  " OMDoc.predicationToXmlOM"
            in
              sortUName
          )
          (predArgs pt)
      argorigins =
        map
          (\argxmlid ->
            getNodeNameBaseForXml
              ln
              $
              findOrigin
                collectionMap
                uniqueNames
                (Hets.findIdIdsForName)
                (ln, nn)
                argxmlid
                id -- adjustStringForXmlName
                (e_fname ++ " (predication, sort)")
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
                    OMDoc.mkOMSE Nothing "casl" "predication"
                  ]
                  ++
                  (
                    map
                      (\(an, (ab, ao)) ->
                        OMDoc.mkOMSE ab ao (adjustStringForXmlName an)
                      )
                      argzip
                  )
                )
    in
      OMDoc.mkSymbolE
        Nothing
        (adjustStringForXmlName pidxmlid)
        OMDoc.SRObject
        (Just typeobj)

-- | create an OMDoc-/symbol/ defining an operator.
--
-- Results in something like
-- (/typenameX/ encodes signature, /typenameR/ encodes result type) :
--
-- @
--   \<symbol role=\"object\" name=\"/opname/\">
--     \<type system=\"casl\">
--       \<OMOBJ>
--         \<OMA>
--           \<OMS cd=\"casl\" name=\"function\">
--           \<OMS cd=\"/libnameOfType1/\" name=\"/typename1/\">
--           \<OMS cd=\"/libnameOfType2/\" name=\"/typename2/\">
--           /.../
--           \<OMS cd=\"/libnameOfTypeR/\" name=\"/typenameR/\">
--         \<\/OMA>
--       \<\/OMOBJ>
--     \<\/type>
--   \<\/symbol>
-- @
operatorToXmlOM::
  ASL.LIB_NAME -- ^ library name of operator
  ->Graph.Node -- ^ node of operator
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->Hets.CollectionMap
  ->(Id.Id, OpType) -- ^ operator to translate
  ->OMDoc.Symbol
operatorToXmlOM
  ln
  nn
  uniqueNames
  collectionMap
  (oid, ot)
  =
    let
      e_fname = "OMDoc.OMDocOutput.operatorToXmlOM: "
      ops = Hets.getOpsAt collectionMap (ln, nn)
      validOps =
        filter
          (\((opidwo, ot'), _) ->
            Hets.getIdId (Hets.woItem opidwo) == oid
            && ot' { opKind = opKind ot } == ot
          )
          ops
      oidxmlid =
        case validOps of
          [] ->
            (error (e_fname ++ "No name for \"" ++ show oid ++ "\""))
          ((_, uN):_) -> uN

      argnames =
        map
          (\args ->
            let
              (_, sortUName) =
                findOriginId
                  collectionMap
                  uniqueNames
                  Hets.findIdIdsForId
                  (ln, nn)
                  args
                  " OMDoc.operatorToXmlOM"
            in
              sortUName
          )
          (opArgs ot)
      argorigins =
        map
          (\argxmlid ->
            getNodeNameBaseForXml
              ln
              $
              findOrigin
                collectionMap
                uniqueNames
                (Hets.findIdIdsForName)
                (ln, nn)
                argxmlid
                id -- adjustStringForXmlName
                (e_fname ++ " (operator, sort)")
          )
          argnames
      argzip =
        zip
          argnames
          argorigins
      (_, resxmlid) =
        findOriginId
          collectionMap
          uniqueNames
          Hets.findIdIdsForId
          (ln, nn)
          (opRes ot)
          " OMDoc.operatorToXmlOM"
      (resbase, resorigin) =
        getNodeNameBaseForXml
          ln
          $
          findOrigin
            collectionMap
            uniqueNames
            (Hets.findIdIdsForName)
            (ln, nn)
            resxmlid
            id -- adjustStringForXmlName
            (e_fname ++ " (operator, sort)")

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
                      Nothing
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
                      (\(an, (ab, ao)) ->
                        OMDoc.mkOMSE ab ao (adjustStringForXmlName an)
                      )
                      argzip
                  )
                  ++
                  [
                    OMDoc.mkOMSE
                      resbase
                      resorigin
                      (adjustStringForXmlName resxmlid)
                  ]
                )
    in
      OMDoc.mkSymbolE
        Nothing
        (adjustStringForXmlName oidxmlid)
        OMDoc.SRObject
        (Just typeobj)

{-
sortToXmlOM::XmlNamed SORT->OMDoc.Symbol
sortToXmlOM xnSort =
  OMDoc.mkSymbol (xnName xnSort) OMDoc.SRSort
-}

-- | create a representation for a generated sort (generated by /ADT/)
genSortToXmlOM::
  String -- ^ generated from attribute
  ->XmlNamed SORT -- ^ sort
  ->OMDoc.Symbol
genSortToXmlOM genFrom xnSort =
  OMDoc.mkSymbolE (Just genFrom) (xnName xnSort) OMDoc.SRSort Nothing

-- | theory name, theory source (local)
data TheoryImport = TI (String, String)

instance Show TheoryImport where
  show (TI (tn, ts)) = "Import of \"" ++ tn ++ "\" from \"" ++ ts ++ "\"."

-- | source name, source (absolute)
data Source a = S (String, String) a

instance Show (Source a) where
  show (S (sn, sf) _) = "Source \"" ++ sn ++ "\" File : \"" ++ sf ++ "\"."

-- | create a filename from a library name (without path and extension).
-- Used to generate the name (xml:id) for an OMDoc-Document.
createLibName::ASL.LIB_NAME->String
createLibName libname = splitFile . fst . splitPath $ unwrapLinkSource libname

-- | separates the path and filename part from a filename, first element is the
-- name, second the path (without last delimiter)
splitPath::String->(String, String)
splitPath f = case explode "/" f of
  [x] -> (x, "")
  l -> (last l, intercalate "/" $ init l)

-- | returns the name of a file without extension
splitFile::String->String
splitFile file =
  let
    filenameparts = explode "." file
  in
    case (length filenameparts) of
            1 -> file
            2 -> case head filenameparts of
                            "" -> "." ++ last filenameparts
                            fn -> fn
            _ -> implode "." $ init filenameparts

-- | prepend a path to a pathname
fileSandbox::
  String -- ^ path to prepend (may not end on \'\/\')
  ->String -- ^ path
  ->String
fileSandbox [] file = file
fileSandbox sb file =
  sb ++ "/" ++ case head file of
    '/' -> tail file
    _ -> file

-- | used in /CMP/ generation.
--
-- Takes a list of 'Id.Pos'-file-positions and extracts the
-- corresponding strings into a mapping.
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

{-
-- | find the XML-name and library name mapping for a sort
findSortOriginCL::
  ASL.LIB_NAME -- ^ library to search in
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->[Hets.IdNameMapping] -- ^ name mapping
  ->SORT -- ^ sort to find
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
-}

{-
-- | Tries to find the XML-name and the library name mapping
-- of a predicate.
--
-- For qualified predicates the given sort-relation is used
-- to find a predicate with a compatible signature (according to
-- the relation).
findPredicateOriginCL::
  ASL.LIB_NAME -- ^ name of library to search in
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->[Hets.IdNameMapping] -- ^ name mapping
  ->Rel.Rel SORT -- ^ sort relation for compatibility checks
  ->PRED_SYMB -- ^ predication to find
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
            (Set.toList
              (
                Set.union
                  (Hets.inmGetIdNameGaPredSet cm)
                  (Hets.inmGetIdNamePredSet cm)
              )
            )
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
            (Set.toList
              (
                Set.union
                  (Hets.inmGetIdNameGaPredSet cm)
                  (Hets.inmGetIdNamePredSet cm)
              )
            )
            (\( (uid, upt), _) ->
              uid == pr && upt == (Hets.cv_Pred_typeToPredType pt)
            )
            (\( (uid, upt), _) ->
              uid == pr &&
                Hets.compatiblePredicate
                  sortrel
                  upt
                  (Hets.cv_Pred_typeToPredType pt)
            )
        of
          Nothing -> Nothing
          (Just (_, uname)) -> Just (uname, cm)
      )
-}

{-
-- | Tries to find the XML-name and the library name mapping
-- of an operator.
--
-- For qualified operators the given sort-relation is used
-- to find an operator with a compatible signature (according to
-- the relation).
findOperatorOriginCL::
  ASL.LIB_NAME -- ^ name of library to search in
  ->[Hets.IdNameMapping] -- ^ unique name mapping
  ->[Hets.IdNameMapping] -- ^ name mapping
  ->Rel.Rel SORT -- ^ sort relation for compatibility checks
  ->OP_SYMB -- ^ operator to find
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
            )
            (\( (uid, uot), _) ->
              uid == op && uot == (Hets.cv_Op_typeToOpType ot)
            )
            (\( (uid, uot), _) ->
              uid == op
              && Hets.compatibleOperator sortrel uot (Hets.cv_Op_typeToOpType ot)
            )
        of
          Nothing -> Nothing
          (Just (_, uname)) -> Just (uname, cm)
      )
-}

{-
-- | Generic function to search for an element where two predicates
-- signal preferred (/equal/) and sufficient (/compatible/) elements
-- respectively.
--
-- If an /equal/ element exists it is returned, else if a /compatible/
-- element exists, it is returned and else 'Nothing' is returned.
preferEqualFindCompatible::
  [a] -- ^ elements to search in
  ->(a->Bool) -- ^ /equality/-predicate
  ->(a->Bool) -- ^ /compatibility/-predicate
  ->Maybe a
preferEqualFindCompatible l isEqual isCompatible =
  case find isEqual l of
    Nothing ->
      find isCompatible l
    x -> x
-}

-- | translate 'CASLFORMULA's to OMDoc-elements (/axiom|definition|presentation/)
--  where for each /axiom/- or /definition/-element a /presentation/-element
--  is generated to preserve the internal (Hets) name.
wrapFormulasCMPIOOM::
  GlobalOptions -- ^ HetcatsOpts + debugging-information
  ->LibEnv -- ^ library environment
  ->ASL.LIB_NAME -- ^ library of formulas
  ->Graph.Node -- ^ node of formulas
  ->[Hets.IdNameMapping] -- ^ mapping of unique names
  ->Hets.CollectionMap
  ->[(Ann.Named CASLFORMULA)] -- ^ named formulas
  ->IO ([OMDoc.Axiom], [OMDoc.Definition], [OMDoc.Presentation])
wrapFormulasCMPIOOM go lenv ln nn uN collectionMap fs =
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
            (axdef, pr) = wrapFormulaCMPOM go lenv ln nn uN collectionMap f poslinemap
          in
            case axdef of
              (Left ax) ->
                (wax++[ax], wde, wpr++[pr])
              (Right def) ->
                (wax, wde++[def], wpr++[pr])
        )
        ([], [], [])
        (zip fs [1..])

