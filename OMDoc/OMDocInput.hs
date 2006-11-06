{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

Input-methods for reading OMDoc
-}
{-
TODO:
  bug:
    When referencing over several imports, sorts are disappearing.
    (e.g. Basic/Graphs.casl can be converted to OMDoc but not back)
-}
module OMDoc.OMDocInput
  (
    mLibEnvFromOMDocFile
  ) 
 -- debug 
{-  (
     Source(..)
    -- options currently for debugging, stores HetcatsOptions
    ,GlobalOptions(..)
    ,FFXInput(..)
    -- reads an OMDoc-File and builds a graph of the files imported
    ,makeImportGraphFullXml
    -- transforms an import graph into a graph holding a DevGraph for
    -- each OMDoc-File (+ document)
    ,processImportGraphXN
    -- strips documents from processed import graph creating a graph of
    -- DevGraphs
    ,hybridGToDGraphG
    -- converts a graph of DevGraphs into a LibEnv (using file names for
    -- library names)
    -- same as above but using the documents id (name) for library name
    ,dGraphGToLibEnvOMDocId
    -- wrapper for Hets that tries to create a LibEnv from an OMDoc file
    -- and returns Nothing on error
    ,mLibEnvFromOMDocFile
    -- executes a sequence of the above functions to create a LibEnv from
    -- an OMDoc file
    ,libEnvFromOMDocFile
    -- loads an xml file via HXT and returns the 'omdoc'-tree
    -- ,loadOMDoc
    ,getImportedTheories
    ,fetchRequationSymbols
    ,preprocessXml
  )
-}
  where

import qualified OMDoc.HetsDefs as Hets
import CASL.Sign
import CASL.Morphism
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import qualified Common.Id as Id
import qualified Syntax.AS_Library as ASL
import qualified CASL.AS_Basic_CASL as ABC

import Static.DevGraph
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Common.Lib.Graph as CLGraph

-- Often used symbols from HXT
import Text.XML.HXT.Parser
  ( (+++), (.>), xshow, isTag, getChildren, processChildren, getValue
    ,emptyRoot, v_1, v_0, a_issue_errors, a_source, a_validate
    ,a_check_namespaces
  )
        
import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)
import qualified Text.XML.HXT.DOM.XmlTreeTypes as HXTT hiding (when)

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import qualified Common.AS_Annotation as Ann

import qualified Logic.Prover as Prover

import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf, find)

import qualified Common.GlobalAnnotations as GA

import Debug.Trace (trace)

import qualified System.IO.Error as System.IO.Error

import Driver.Options

import Control.Monad
import Control.Exception as Control.Exception

import qualified Network.URI as URI

import OMDoc.Util
import OMDoc.Container
import OMDoc.XmlHandling

import OMDoc.OMDocDefs

import qualified System.Directory as System.Directory

{- |
  A wrapper-function for Hets.
  Tries to load an OMDoc file and to create a LibEnv.
  Uses library-path specified in HetcatsOpts to search for imported files.
  On (IO-)error Nothing is returned
-}
mLibEnvFromOMDocFile::
  HetcatsOpts -- ^ setup libdir to search for files
  ->FilePath -- ^ the file to load
  ->IO (Maybe (ASL.LIB_NAME, LibEnv))
mLibEnvFromOMDocFile hco file =
  Control.Exception.catch
    (
      do
        (ln, _, lenv) <- libEnvFromOMDocFile
          (emptyGlobalOptions { hetsOpts = hco })
          file
        return (Just (ln, lenv))
    )
    (\_ -> putIfVerbose hco 0 "Error loading OMDoc!" >> return Nothing)

{- |
  Tries to load an OMDoc file an to create a LibEnv.
  Uses @dGraphGToLibEnvOMDocId@ to create library names.
-}
libEnvFromOMDocFile::
  GlobalOptions -- ^ library path setup with hetsOpts + debugging options
  ->String -- ^ URI \/ File to load
  ->IO (ASL.LIB_NAME, DGraph, LibEnv)
libEnvFromOMDocFile go f =
  makeImportGraphFullXml go f >>=
    return . importGraphToLibEnv go
--    return . dGraphGToLibEnvOMDocId go . hybridGToDGraphG go . processImportGraphXN go


{- -- debug
  loads an OMDoc file and returns it even if there are errors
  fatal errors lead to IOError
-}
{-
loadOMDoc ::
  String -- ^ URI \/ File to load
  ->(IO HXT.XmlTrees)
loadOMDoc f =
  do
    tree <- (
      HXT.run' $
      HXT.parseDocument
        [
           (a_source, f)
          ,(a_validate, v_0) -- validation is nice, but HXT does not give back
                             -- even a partial document then...
          ,(a_check_namespaces,v_1) -- needed,really...
          ,(a_issue_errors, v_0)
        ]
        emptyRoot
      )
    status <- return ( (
      read $
      xshow $
      applyXmlFilter (getValue "status") tree
      ) :: Int )
    if status <= HXT.c_err
      then
        return $ applyXmlFilter (getChildren .> isTag "omdoc") tree
      else
        ioError $ userError ("Error loading \"" ++ f ++ "\"")
-}

{- |
  extracts constructors from adt-structures
-}
-- i need a back-reference to the theory to get presentations for adt-constructors...
extractConsXNWONFromADT::
  FFXInput -- ^ current input settings
  ->AnnXMLN -- ^ wrapped adt 
  ->AnnXMLN -- ^ wrapped theory containing adt
  ->(XmlNamedWONId, [(XmlNamedWONId, OpTypeXNWON)])
extractConsXNWONFromADT ffxi anxml anxmltheory =
  let
    sortdef =
      applyXmlFilter
        (isTag "adt" .> getChildren .> isTag "sortdef")
        (axXml anxml)
    sorts' = xshow $ applyXmlFilter (getValue "name") sortdef
    sortid =
      case findByNameAndOrigin
            sorts'
            (axAnn anxml)
            (mapSetToSet $ xnSortsMap ffxi)
              of
                Nothing -> error "No sort for ADT!"
                (Just si) -> si
    cons = applyXmlFilter (getChildren .> isTag "constructor") sortdef
  in
    (sortid, map (\n -> extractConXNWON [n] sortid) cons)
  where
    extractConXNWON::
      HXT.XmlTrees
      ->XmlNamedWONId
      ->(XmlNamedWONId, OpTypeXNWON) -- empty list on error
    extractConXNWON conx sortid =
      let
        conxname = xshow $ applyXmlFilter (getValue "name") conx
        conhpress = getPresentationString conxname (axXml anxmltheory)
        conid = case conhpress of
                [] -> Hets.stringToId conxname
                _ -> read conhpress
        conxnwonid = XmlNamed (Hets.mkWON conid  (axAnn anxml)) conxname
        args =
          map
            (\n -> xshow [n])
            $
            applyXmlFilter
              (getChildren .> isTag "argument" .> getValue "sort")
              conx
        argsxn =
          map
            (\n -> 
              case findByNameAndOrigin
                    n
                    (axAnn anxml)
                    (mapSetToSet $ xnSortsMap ffxi)
                      of
                        Nothing -> error "Unknown sort in constructor..."
                        (Just x) -> x
            )
            args
      in
        (conxnwonid, OpTypeXNWON Total argsxn sortid)

{- |
  creates sentences from adt-constructors
-}
consToSensXN::
  XmlNamedWONId -- ^ name of the constructed sort
  ->[(XmlNamedWONId, OpTypeXNWON)] -- ^ constructors
  ->XmlNamed Hets.SentenceWO
consToSensXN sortid conlist =
  XmlNamed 
    (Hets.mkWON
      (Ann.NamedSen
        ("ga_generated_" ++ show (xnWOaToa sortid))
        True
        False
        (Sort_gen_ax
          (
          foldl (\constraints (id' , ot) ->
              constraints ++
              [ Constraint
                  (xnWOaToa sortid)
                  [(Qual_op_name
                      (xnWOaToa id' )
                      (Hets.cv_OpTypeToOp_type $ opTypeXNWONToOpType ot)
                      Id.nullRange , [0])] 
                  (xnWOaToa sortid)
              ]
            ) [] conlist
          )
          True
        ))
      (xnWOaToO sortid)
    )
    ("ga_generated_" ++ (xnName sortid))


{- |
  extracts symbols used in a OMDoc-Morphism storing a mapping
  of symbols and a list of hidden symbols
-}
fetchRequationSymbols::HXT.XmlTrees->([String], Hets.RequationList)
fetchRequationSymbols t =
  let
    hides = xshow $ applyXmlFilter (isTag "morphism" .> getQualValue "" "hiding") t
    hiddensyms = breakSepSpace hides
    pattern = isTag "requation" .> processChildren (isTag "OMOBJ") .> getChild 1
    value = isTag "requation" .> processChildren (isTag "OMOBJ") .> getChild 2
    vsymbol = value .> getChildren .> isTag "OMS" .> getQualValue "" "name" 
    psymbol = pattern .> getChildren .> isTag "OMS" .> getQualValue "" "name" 
    vcd = value .> getChildren .> isTag "OMS" .> getQualValue "" "cd" 
    pcd = pattern .> getChildren .> isTag "OMS" .> getQualValue "" "cd" 
    requations = applyXmlFilter (isTag "morphism" .> getChildren .> isTag "requation") t
    reqlist = foldl (\rl ts ->
      let
        psymbolname = xshow $ applyXmlFilter psymbol [ts]
        vsymbolname = xshow $ applyXmlFilter vsymbol [ts]
        pcdname = xshow $ applyXmlFilter pcd [ts]
        vcdname = xshow $ applyXmlFilter vcd [ts]
      in
        if (psymbolname /= []) && (vsymbolname /= [])
          then
            rl ++ [( (pcdname, psymbolname), (vcdname, vsymbolname) )]
          else
            rl
      ) [] requations
  in
    (hiddensyms, reqlist)

defaultDGLinkType::DGLinkType
defaultDGLinkType = GlobalDef

defaultDGOrigin::DGOrigin
defaultDGOrigin = DGExtension

defaultDGLinkLab::DGLinkLab
defaultDGLinkLab =
  DGLink Hets.emptyCASLGMorphism defaultDGLinkType defaultDGOrigin


-- remove keys from a map (will result in removing double entries when merging sets)
mapSetToSet::(Ord b)=>Map.Map a (Set.Set b)->Set.Set b
mapSetToSet mapping =
  foldl (\set (_, s) ->
      Set.union set s
    ) Set.empty (Map.toList mapping)
                
{- |
  AnnotatedXML is a structure containing xml-trees and and annotation
  to these trees.
  Used to have a reference when processing these trees.
-}
data AnnotatedXML a = AXML { axAnn::a, axXml::HXT.XmlTrees }
  deriving Show
        
-- | xml-trees with Graph.Node annotation
type AnnXMLN = AnnotatedXML Graph.Node

-- | equality for AnnotatedXML is determined by equality of annotations
instance (Eq a)=>Eq (AnnotatedXML a) where
  ax1 == ax2 = (axAnn ax1) == (axAnn ax2)

-- | ordering of AnnotatedXML is determined by order of annotations
instance (Ord a)=>Ord (AnnotatedXML a) where
  compare ax1 ax2 = compare (axAnn ax1) (axAnn ax2)

{- |
  An annotated theory set is a set of AnnotatedXML where
  each element in the set contains one theory-tree and is annotated by the
  number of the theory (appearance in file) (pseudo-graph-nodes)
-}
buildAXTheorySet::HXT.XmlTrees->Set.Set AnnXMLN
buildAXTheorySet t =
  let
    theories = applyXmlFilter (getChildren .> isTag "theory") t
  in
    Set.fromList $ zipWith
      (\n t' -> AXML n [t' ])
      [1..]
      theories

{- |
  creates a set of theory names by examining the name of the theory and
  searching for presentation elements.
-}
nodeNamesXNFromXml::Set.Set AnnXMLN->TheoryXNSet
nodeNamesXNFromXml axmlset =
  Set.fromList $ Set.fold
    (\axml txnl ->
      let
        theoid = stripFragment $ xshow $ applyXmlFilter (getQualValue "xml" "id") (axXml axml)
        theohetsnodenames = xshow $ applyXmlFilter
          (
            getChildren .> isTag "presentation" .>
            withSValue "for" theoid .> getChildren .>
            isTag "use" .> withSValue "format" "Hets" .>
            getChildren
          ) (axXml axml)
        theohetsnodename =
          if (theohetsnodenames == "") || (isPrefixOf "AnonNode" theoid) 
            then
              idToNodeName $ read ("["++theoid++",,0]")
            else 
              idToNodeName $ read theohetsnodenames
      in
        txnl ++ [XmlNamed ((axAnn axml), theohetsnodename) theoid]
    )
    []
    axmlset

                
sortsXNWONFromXmlTheory::AnnXMLN->(Set.Set XmlNamedWONSORT)
sortsXNWONFromXmlTheory anxml =
  let
    sortnames = map (\m -> xshow [m]) $
      applyXmlFilter
              (
                getChildren .> isTag "symbol" .>
                withQualSValue symbolTypeXMLNS symbolTypeXMLAttr "sort" .>
                getQualValue sortNameXMLNS sortNameXMLAttr
              )
              (axXml anxml)
  in
  Set.fromList $ foldl (\xnss sn ->
    let
      hetspress = xshow $ applyXmlFilter (
        getChildren .> 
        isTag "presentation" .> withSValue "for" sn .>
        getChildren .> isTag "use" .> withSValue "format" "Hets" .>
        getChildren) (axXml anxml)
        -- hets presentations are optional
      hetspres = case hetspress of
        [] -> (Hets.stringToId sn)
        x -> read x -- incorrect hets presentations will cause an exception here
    in
      xnss ++ [ XmlNamed (Hets.mkWON hetspres (axAnn anxml)) sn ]
    ) [] sortnames
                

findByName::(Container b (XmlNamed a))=>String->b->Maybe (XmlNamed a)
findByName iname icon =
  find (\i -> (xnName i) == iname) (getItems icon)
        
findAllByNameWithAnd::(Container b a)=>(a->d)->(a->XmlNamed c)->String->b->[d]
findAllByNameWithAnd proc trans iname icon =
  map proc $ filter (\i -> xnName (trans i) == iname) $ getItems icon
  

-- search for a certainly named item and prefer items of specified origin
-- check result for origin if important
findByNameAndOrigin::(Eq b, Container c (XmlNamedWO a b))=>String->b->c->Maybe (XmlNamedWO a b)
findByNameAndOrigin iname iorig icon =
  let
    candidates = filter (\i -> (xnName i) == iname) (getItems icon)
  in
    case find (\i -> (xnWOaToO i) == iorig) candidates of
      Nothing ->
        case candidates of
          (i:_) -> (Just i)
          _ -> Nothing
      i -> i

relsXNWONFromXmlTheory::Set.Set XmlNamedWONSORT->AnnXMLN->Rel.Rel XmlNamedWONSORT
relsXNWONFromXmlTheory xnsortset anxml =
  let
    adts = applyXmlFilter (getChildren .> isTag "adt") (axXml anxml)
    relations = concat $ map relsFromXmlADT adts
  in
    Rel.fromList relations
  where
  relsFromXmlADT::HXT.XmlTree->[(XmlNamedWONSORT, XmlNamedWONSORT)]
  relsFromXmlADT t' =
    let
      xnsorts = xshow $
        applyXmlFilter
          (getChildren .> isTag "sortdef" .>
            withSValue "type" "free" .> getValue "name")
          [t' ]
      xninsortss = map (\n -> drop 1 $ xshow [n]) $
        applyXmlFilter
          (getChildren .> isTag "sortdef" .> getChildren .>
            isTag "insort" .> getValue "for")
          [t' ]
      xnsort = case findByNameAndOrigin xnsorts (axAnn anxml) xnsortset of
        Nothing -> (XmlNamed (Hets.mkWON (Hets.stringToId xnsorts) (-1)) xnsorts)
        (Just xnsort' ) -> xnsort'
      xninsorts = map (\s -> case findByNameAndOrigin s (axAnn anxml) xnsortset of
        Nothing ->
--          Debug.Trace.trace
--            ("Relation with unknown sort!" ++ (show s))
            (XmlNamed (Hets.mkWON (Hets.stringToId s) (-1)) s)
        (Just xs' ) -> xs'
        ) xninsortss
      -- note that we restore 'CASL-Order' here
    in
      map (\n -> (n, xnsort)) xninsorts


getPresentationString::String->HXT.XmlTrees->String
getPresentationString for t =
  xshow $ applyXmlFilter
    (getChildren .> isTag "presentation" .> withSValue "for" for .>
      getChildren .> isTag "use" .> withSValue "format" "Hets" .> 
      getChildren) t
        

predsXNWONFromXmlTheory::
  Map.Map
    XmlName
    FFXInput
  ->TheoryXNSet
  ->Set.Set XmlNamedWONSORT
  ->AnnXMLN
  ->[(XmlNamedWONId, PredTypeXNWON)]
predsXNWONFromXmlTheory cdmap xntheoryset xnsortset anxml =
  let
    objsymbols = applyXmlFilter (getChildren .> isTag "symbol" .> withQualSValue symbolTypeXMLNS symbolTypeXMLAttr "object") (axXml anxml)
    predsymbols = filter (\n -> applyXmlFilter (
      getChildren .> isTag "type" .>
      getChildren .> isTag "OMOBJ" .>
      getChildren .> isTag "OMA" .>
      getChildren .> isTag "OMS" .>
      withSValue "cd" "casl" .>
      withSValue "name" "predication") [n] /= []) objsymbols
  in
    map predFromXmlSymbol (map (\t -> AXML (axAnn anxml) [t]) predsymbols)
  where
    predFromXmlSymbol::AnnXMLN->(XmlNamedWONId, PredTypeXNWON)
    predFromXmlSymbol panxml =
      let
        pidxname = xshow $
          applyXmlFilter
            (getQualValue predNameXMLNS predNameXMLAttr)
            (axXml panxml)
        pids = getPresentationString pidxname (axXml anxml) -- yes, reference to 'outer' xml
        pid = case pids of
          [] ->
            Debug.Trace.trace
              ("Note: No Hets-Presentation found for Predicate with Xml-ID : \""
                ++ pidxname ++ "\"") $ Hets.stringToId pidxname
          _ -> read pids
        argtags = applyXmlFilter (getChildren .> isTag "type" .>
          withSValue "system" "casl" .> getChildren .> isTag "OMOBJ" .>
          getChildren .> isTag "OMA" .> getChildren .> isTag "OMS" .>
          withValue "name" (/="predication") )
          (axXml panxml)
        argswithcds =
          map
            (\n ->
              (
                xshow $ applyXmlFilter (getValue "name") [n],
                xshow $ applyXmlFilter (getValue "cd") [n]
              )
            )
            argtags
        xnargs =
          map
            (\(axname, acd) ->
              let
                theonode = case getNodeForTheoryName xntheoryset (stripFragment acd) of
                  Nothing -> error "Unknown Theory for Argument!"
                  (Just n) -> n
              in
                case findByNameAndOrigin axname theonode xnsortset of
                  Nothing ->
                    let
                      allffxis = Map.elems cdmap
                      allsortmaps = map xnSortsMap allffxis
                      allsortsets = concat (map Map.elems allsortmaps)
                      allsorts = concat (map Set.toList allsortsets)
                    in
                      case
                        find
                          (\x -> (xnName x) == axname)
                          allsorts
                      of
                        Nothing ->
{-                          error
                            ("Sort " ++ axname ++ " not in FFXI..." ++ show (map xnName allsorts)
                             ++ " at : " ++ (take 300 (xshow (axXml panxml)))
                            ) -}
  --                        Debug.Trace.trace
  --                          ("Sort " ++ axname ++ " not in FFXI..." ++ show (map xnName allsorts)
  --                           ++ " at : " ++ (take 300 (xshow (axXml panxml)))
  --                          )
                            (XmlNamed (Hets.mkWON (Hets.stringToId axname) (-1)) axname)
                        (Just s) ->
--                          Debug.Trace.trace
--                            ("Found sort " ++ axname  ++ " in FFXI...")
                            s
                  (Just xnarg) ->
                    if (xnWOaToO xnarg) /= theonode
                      then
                        Debug.Trace.trace
                          ("Found Argument (" ++ show xnarg ++ ") but in wrong Theory! (not theory #" ++ show theonode ++ ") while processing Predicate " ++ pidxname)
                          xnarg
                      else
                        xnarg
            )
            argswithcds
      in
        (XmlNamed (Hets.mkWON pid (axAnn anxml)) pidxname, PredTypeXNWON xnargs)
        
opsXNWONFromXmlTheory::
  Map.Map
    XmlName
    FFXInput
  ->TheoryXNSet
  ->Set.Set XmlNamedWONSORT
  ->AnnXMLN
  ->[(XmlNamedWONId, OpTypeXNWON)]
opsXNWONFromXmlTheory cdmap xntheoryset xnsortset anxml =
  let
    objsymbols = applyXmlFilter (getChildren .> isTag "symbol" .> withQualSValue symbolTypeXMLNS symbolTypeXMLAttr "object") (axXml anxml)
    opsymbols =
      filter
        (\n -> applyXmlFilter (
          getChildren .> isTag "type" .>
          getChildren .> isTag "OMOBJ" .>
          getChildren .> isTag "OMA" .>
          getChildren .> isTag "OMS" .>
          withSValue "cd" "casl" .>
          withValue "name" (\n' -> n' == "function" || n' == "partial-function")
        )
        [n] /= [])
      objsymbols
  in
    map opFromXmlSymbol (map (\n -> AXML (axAnn anxml) [n]) opsymbols) 
  where
    opFromXmlSymbol::AnnXMLN->(XmlNamedWONId, OpTypeXNWON)
    opFromXmlSymbol oanxml =
      let
        oidxname = xshow $
          applyXmlFilter (getQualValue opNameXMLNS opNameXMLAttr) (axXml oanxml)
        oids = getPresentationString oidxname (axXml anxml)
        oid = case oids of
          [] ->
            Debug.Trace.trace ("Note: No Hets-Presentation found for Operator with Xml-ID : \""
              ++ oidxname ++ "\"") $ Hets.stringToId oidxname
          _ -> read oids
        isTotal = applyXmlFilter (
          getChildren .> isTag "type" .> withSValue "system" "casl" .>
          getChildren .> isTag "OMOBJ" .>
          getChildren .> isTag "OMA" .>
          getChildren .> isTag "OMS" .>
          withSValue "name" "function") (axXml oanxml) /= []
        argsalltags = applyXmlFilter (
          getChildren .> isTag "type" .> withSValue "system" "casl" .>
          getChildren .> isTag "OMOBJ" .>
          getChildren .> isTag "OMA" .>
          getChildren .> isTag "OMS" .>
          withValue "name" (\n -> n /= "function" && n /= "partial-function")
          ) (axXml oanxml)
        argsallwithcds =
          map
            (\n ->
              (
                xshow $ applyXmlFilter (getValue "name") [n],
                xshow $ applyXmlFilter (getValue "cd") [n]
              )
            )
            argsalltags
        xnargsall =
          map
            (\(axname, acd) ->
              let
                theonode = case getNodeForTheoryName xntheoryset (stripFragment acd) of
                  Nothing ->
                    Debug.Trace.trace
                      ("No Theory for Argument! " ++ (stripFragment acd) ++ "#" ++ axname)
                      (-1)
                  (Just n) -> n
              in
                case findByNameAndOrigin axname theonode xnsortset of
                  Nothing ->
                    let
                      allffxis = Map.elems cdmap
                      allsortmaps = map xnSortsMap allffxis
                      allsortsets = concat (map Map.elems allsortmaps)
                      allsorts = concat (map Set.toList allsortsets)
                    in
                      case
                        find
                          (\x -> (xnName x) == axname)
                          allsorts
                      of
                        Nothing ->
--                          Debug.Trace.trace
--                            ("Sort " ++ axname ++ " not in FFXI..." ++ show (map xnName allsorts)
--                             ++ " at : " ++ (take 300 (xshow (axXml oanxml)))
--                            )
                            (XmlNamed (Hets.mkWON (Hets.stringToId axname) (-1)) axname)
                        (Just s) ->
--                          Debug.Trace.trace
--                            ("Found sort " ++ axname  ++ " in FFXI...")
                            s
                  (Just xnarg) -> if (xnWOaToO xnarg) /= theonode
                    then
                      Debug.Trace.trace
                        ("Found Argument (" ++ show xnarg ++ ") but in wrong Theory! (not in theory #" ++ show theonode ++ ") while processing operator " ++ oidxname)
                        xnarg
                    else
                      xnarg
            )
            argsallwithcds
        xnargs = take (length(xnargsall)-1) xnargsall
        xnres = last (xnargsall)
      in
        (
          XmlNamed (Hets.mkWON oid (axAnn anxml)) oidxname,
            OpTypeXNWON
                    (if isTotal then Total else Partial)
                    xnargs
                    xnres
        )

-- | imports lead to edges but if the information is not stored in the
-- document there is no clue on what type of edge to create...
data ImportHint = FromStructure (String, DGLinkLab) | FromData (String, DGLinkLab)
  deriving (Eq, Show)

-- simple ord-relation to make Set happy...     
instance Ord ImportHint where
  (FromStructure _) <= (FromStructure _) = True
  (FromStructure _) <= (FromData _) = True
  (FromData _) <= (FromData _) = True
  (FromData _) <= (FromStructure _) = False

glThmsFromXmlLS::
    HXT.XmlTrees
  ->[(Int, XmlName, (XmlName, Hets.HidingAndRequationList, Conservativity, Bool))]
glThmsFromXmlLS t =
  let
    inclusions =
      applyXmlFilter (isTag "theory-inclusion" +++ isTag "axiom-inclusion") t
  in
    foldl (\glts (inum, inx) ->
      let
        islocal = null $ applyXmlFilter (isTag "theory-inclusion") [inx]
        incons = consFromAttr [inx]
        --inid = xshow $ applyXmlFilter (getQualValue "xml" "id") [inx]
        infromid = stripFragment $ xshow $ applyXmlFilter (getQualValue "" "from") [inx]
        intoid = stripFragment $ xshow $ applyXmlFilter (getQualValue "" "to") [inx]
        -- inmorph = case inmorphx of [] -> []; _ -> [xmlToMorphismMap inmorphx]
        xmorph = applyXmlFilter (getChildren .> isTag "morphism") [inx]
        hreq = fetchRequationSymbols xmorph
      in
        glts ++
          [
            (
                inum
              , intoid
              , (
                    infromid
                  , hreq
                  , incons
                  , (not islocal)
                )
            )
          ]
      )
      []
      (zip [1..] inclusions)
  where
  consFromAttr::HXT.XmlTrees->Conservativity
  consFromAttr t' =
    let
      consattr = xshow $ applyXmlFilter (getValue "conservativity") t'
    in
      case consattr of
        "monomorphism" -> Mono
        "conservative" -> Cons
        "definitional" -> Def
        _ -> None

-- used by new format (for import graph)
importsFromXmlTheory::HXT.XmlTrees->Hets.Imports
importsFromXmlTheory t =
  let
    imports' = applyXmlFilter (getChildren .> isTag "imports") t
  in
    foldl
      (\imps (c, i) ->
        let
          from = xshow $ applyXmlFilter (getValue "from") [i]
          mfromURI = URI.parseURIReference from
          fromname = case mfromURI of
            Nothing -> from
            (Just uri) -> case URI.uriFragment uri of
                    "" -> from
                    f -> drop 1 f
          xmorph = applyXmlFilter (getChildren .> isTag "morphism") [i]
          hreq = fetchRequationSymbols xmorph
          -- mm = xmlToMorphismMap xmorph
          -- there is at most one morphism for each import...
{-          mm = foldl (\(mmsm, mmfm, mmpm, mmhs) m ->
              let
                (nmmsm, nmmfm, nmmpm, nmmhs) = xmlToMorphismMap [m]
                hreq = fetchRequationsSymbols [m]
              in
                (Map.union mmsm nmmsm,
                  Map.union mmfm nmmfm, Map.union mmpm nmmpm,
                    Set.union mmhs nmmhs)
            ) (Map.empty, Map.empty, Map.empty, Set.empty) $
              applyXmlFilter (getChildren .> isTag "morphism") [i] -}
        in
          Set.union imps (Set.singleton (c, (fromname, {-(Just mm)-} Nothing, hreq, True)))
      ) Set.empty (zip [1..] imports')
       
importsFromAnnXMLSet::TheoryXNSet->Set.Set AnnXMLN->Hets.ImportsMap
importsFromAnnXMLSet txns axset =
  Set.fold
    (\axml i ->
      let
        name =
          case getTheoryXmlName txns (axAnn axml) of
            Nothing -> error "!"
            (Just x) -> x
        imports = importsFromXmlTheory (axXml axml)
      in
        Map.insert name imports i
    )
    Map.empty
    axset
                
sensXNWONFromXmlTheory::FFXInput->AnnXMLN->(Set.Set (XmlNamed Hets.SentenceWO))
sensXNWONFromXmlTheory ffxi anxml =
  Set.fromList $ unwrapFormulasXNWON ffxi anxml
        

conSensXNWONFromXmlTheory::FFXInput->AnnXMLN->Set.Set (XmlNamed Hets.SentenceWO) 
conSensXNWONFromXmlTheory ffxi anxml =
  let
    adts = applyXmlFilter (getChildren .> isTag "adt") (axXml anxml)
  in
    Set.fromList $ foldl
      (\list n ->
        let
          (excon, exconlist) =
            extractConsXNWONFromADT ffxi (AXML (axAnn anxml) [n]) anxml
        in
          if (length exconlist) == 0 -- if only the relation is expressed,
                                     -- no constructors are specified
            then
              list
            else
              list ++ [consToSensXN excon exconlist] 
      ) [] adts 

consXNWONFromXmlTheory::FFXInput->AnnXMLN->[(XmlNamedWONId, [(XmlNamedWONId, OpTypeXNWON)])]
consXNWONFromXmlTheory ffxi anxml =
  let
    adts = applyXmlFilter (getChildren .> isTag "adt") (axXml anxml)
  in
    foldl
      (\list n ->
        let
          (excon, exconlist) =
            extractConsXNWONFromADT ffxi (AXML (axAnn anxml) [n]) anxml
        in
          if (length exconlist) == 0 -- if only the relation is expressed,
                                     -- no constructors are specified
            then
              list
            else
              list ++ [(excon, exconlist)]
      ) [] adts 

createTheorySpecifications::TheoryXNSet->String->Set.Set AnnXMLN->[TheorySpecification]
createTheorySpecifications
  xntheoryset
  sourcename
  anxmlset =
  Set.fold
    (\axml tsl ->
      let
        theoid = xshow $ applyXmlFilter (getQualValue "xml" "id") (axXml axml)
        theohetsnodenames = xshow $ applyXmlFilter
          (
            getChildren .> isTag "presentation" .>
            withSValue "for" theoid .> getChildren .>
            isTag "use" .> withSValue "format" "Hets" .>
            getChildren
          ) (axXml axml)
        theohetsnodename =
          if (theohetsnodenames == "") || (isPrefixOf "AnonNode" theoid) 
            then
              idToNodeName $ read ("["++theoid++",,0]")
            else 
              idToNodeName $ read theohetsnodenames
        sorts = sortsXNWONFromXmlTheory axml
        rels = relsXNWONFromXmlTheory sorts axml
        ops = Set.fromList $ opsXNWONFromXmlTheory Map.empty xntheoryset sorts axml
        preds = Set.fromList $ predsXNWONFromXmlTheory Map.empty xntheoryset sorts axml
      in
        tsl ++
          [
            TheorySpecification
              {
                  ts_name = (stripFragment theoid)
                , ts_source = sourcename
                , ts_nodename = theohetsnodename
                , ts_nodenum = (axAnn axml)
                , ts_sorts = sorts
                , ts_sortrelation = rels
                , ts_predicates = preds
                , ts_operators = ops
                , ts_constructors = Set.empty
              }
          ]
    )
    []
    anxmlset

importGraphToSpecs::
  GlobalOptions
  ->(ImportGraph (HXT.XmlTrees))
  ->Graph.Node
  ->([TheorySpecification], [LinkSpecification], TheoryXNSet, Set.Set AnnXMLN)
importGraphToSpecs
  go
  ig
  n
  =
  let
    node =
      case
        Graph.lab ig n
      of
        Nothing -> error "node error!"
        (Just n') -> n'
    refimports = (\x ->
      debugGO go "iGTDGNXN" ("Refimports : " ++ show x) x) $
        filter ( \(_,from,_) -> from /= n) $ Graph.out ig n
    axtheoryset = buildAXTheorySet omdoc
    xntheoryset = 
      nodeNamesXNFromXml
        (debugGO go "pX" "at nodeNamedXNFromXml" axtheoryset)
    theoryspecs = createTheorySpecifications xntheoryset sourcename axtheoryset
    maxUsedNodeNum =
      foldl
        (\mUNN n' ->
          if n' > mUNN
            then
              n'
            else
              mUNN
        )
        0
        (map ts_nodenum theoryspecs)
    refspecs =
      map
        (\(rn, (_, from, (TI (theoname, _)))) ->
          let
            moriginnode = Graph.lab ig from
            (S (slibname, _) _) = case moriginnode of
              Nothing -> error ("node error (Import of "
                ++ theoname ++ " from " ++ (show from) ++ " )!")
              (Just n' ) -> n'
          in
            ReferenceSpecification
              {
                  ts_name = (stripFragment theoname)
                , ts_nodename = (Hets.stringToSimpleId (stripFragment theoname), "", 0)
                , ts_source = slibname
                , ts_nodenum = rn
                , ts_realnodenum = -1
                , ts_sorts = Set.empty
                , ts_sortrelation = Rel.empty
                , ts_predicates = Set.empty
                , ts_operators = Set.empty
                , ts_constructors = Set.empty
              }
        )
        (zip [(maxUsedNodeNum + 1)..] refimports)
    refxnnames =
      Set.fromList
        $
        map
          (\ts -> XmlNamed (ts_nodenum ts, ts_nodename ts) (ts_name ts))
          refspecs
    allXNNames = Set.union xntheoryset refxnnames
    (sourcename, omdoc) = (\(S (sn, _) o) -> (sn, o)) node
    linkspecs = createLinkSpecifications go omdoc allXNNames axtheoryset
  in
    (theoryspecs ++ refspecs, linkspecs, allXNNames, axtheoryset)

createSpecMap::
  GlobalOptions
  ->(ImportGraph (HXT.XmlTrees))
  ->Map.Map String ([TheorySpecification], [LinkSpecification], TheoryXNSet, Set.Set AnnXMLN)
createSpecMap
  go
  ig
  =
    foldl
      (\sm (nn, (S (sourcename, _) _)) ->
        Map.insert sourcename (importGraphToSpecs go ig nn) sm
      )
      Map.empty
      (Graph.labNodes ig)


processSpecMap::
  Map.Map String ([TheorySpecification], [LinkSpecification], TheoryXNSet, Set.Set AnnXMLN)
  ->Map.Map String ([TheorySpecification], [LinkSpecification], TheoryXNSet, Set.Set AnnXMLN)
processSpecMap
  sm
  =
  let
    importsFromMap =
      Map.foldWithKey
        (\sourcename (ts, _ , _, _) iFM ->
          let
            references = filter isRefSpec ts
            refed = map ts_source references
          in
            Map.insert sourcename refed iFM
        )
        Map.empty
        sm
    maxNoAction = Map.size sm
    (processedMap, _, _) =
      until
        (\(_, unprocessedMap, _) -> Map.null unprocessedMap)
        (\(pM, uM, noActionSince) ->
          let
            unkeys = Map.keys uM
            unimports = map (\uk -> (uk, Map.findWithDefault (error "!") uk importsFromMap)) unkeys
            freeun = filter (\(_, i) -> all (flip elem (Map.keys pM)) i) unimports
          in
            if length freeun == 0 && noActionSince <= maxNoAction
              then
                (pM, uM, noActionSince + 1)
              else
                let
                  currentSource = fst $ head freeun
                  (ctslist, clslist, cxntheoryset, caxmlset) =
                    Map.findWithDefault (error "!") currentSource uM
                  resolvedrefs =
                    map
                      (\ts ->
                       if isRefSpec ts
                        then
                          let
                            refsource = ts_source ts
                            (rtslist, _, _, _) =
                              Map.findWithDefault
                                (
                                  Debug.Trace.trace
                                    ("referenced source has not been finished... (" ++ refsource ++ ")")
                                    (
                                      Map.findWithDefault
                                        ([], error "OMDoc.OMDocInput", error "OMDoc.OMDocInput", error "OMDoc.OMDocInput")
                                        refsource
                                        uM
                                    )
                                )
                                refsource
                                pM
                            realspec =
                              case
                                find
                                  (\ts' -> ts_name ts' == (ts_name ts))
                                  rtslist
                              of
                                Nothing ->
                                  Debug.Trace.trace
                                    ("ohoh... no source for reference to " ++ (ts_name ts))
                                    ts
                                (Just x) -> x
                          in
                            adjustOriginsToRef
                              ts
                                {
                                    ts_realnodenum = ts_nodenum realspec
                                  , ts_nodename = ts_nodename realspec
                                  , ts_sorts = ts_sorts realspec
                                  , ts_sortrelation = ts_sortrelation realspec
                                  , ts_predicates = ts_predicates realspec
                                  , ts_operators  = ts_operators realspec
                                  , ts_constructors = ts_constructors realspec
                                }
                        else
                          ts
                      )
                      ctslist
                  processedSpecs =
                    processAllDefLinks
                      resolvedrefs
                      clslist
                in
                  (\x ->
                    if noActionSince > maxNoAction
                      then
                        Debug.Trace.trace
                          ("forced procession of " ++ currentSource)
                          x
                      else
                        x
                  )
                  (
                      Map.insert currentSource (processedSpecs, clslist, cxntheoryset, caxmlset) pM
                    , Map.delete currentSource uM
                    , 0
                  )
        )
        (Map.empty, sm, 0)
  in
    processedMap

  where
    
    adjustOriginsToRef::
        TheorySpecification
      ->TheorySpecification
    adjustOriginsToRef
      ts
      =
      let
        tso = ts_nodenum ts
      in
        ts
          {
              ts_sorts =
                Set.map (setOrigin tso) (ts_sorts ts)
            , ts_sortrelation =
                Rel.fromList
                  $
                  map
                    (\(a, b) -> (setOrigin tso a, setOrigin tso b))
                    (Rel.toList (ts_sortrelation ts))
            , ts_predicates =
                Set.map
                  (\(xnpid, xnpt) ->
                    (
                        xnpid
                      , xnpt
                        {
                          predArgsXNWON =
                            map (setOrigin tso) (predArgsXNWON xnpt) 
                        }
                    )
                  )
                  (ts_predicates ts)
            , ts_operators =
                Set.map
                  (\(xnoid, xnot) ->
                    (
                        xnoid
                      , xnot
                        {
                            opArgsXNWON =
                              map (setOrigin tso) (opArgsXNWON xnot) 
                          , opResXNWON = setOrigin tso (opResXNWON xnot)
                        }
                    )
                  )
                  (ts_operators ts)
            , ts_constructors =
                Set.map
                  (\(xnforsort, conset) ->
                    (
                        setOrigin tso xnforsort
                      , Set.map
                          (\(xncid, xnct) ->
                            (
                                xncid
                              , xnct
                                {
                                    opArgsXNWON = map (setOrigin tso) (opArgsXNWON xnct)
                                  , opResXNWON = setOrigin tso (opResXNWON xnct)
                                }
                            )
                          )
                          conset
                    )
                  )
                  (ts_constructors ts)
          }

    setOrigin::Graph.Node->XmlNamedWONSORT->XmlNamedWONSORT
    setOrigin n xns = XmlNamed (Hets.mkWON (xnWOaToa xns) n) (xnName xns)   

createNodeFromSpec::
    FFXInput
  ->AnnXMLN
  ->TheorySpecification
  ->Graph.LNode DGNodeLab
createNodeFromSpec
  ffxi
  axml
  ts
  =
  let
    theorysens = sensXNWONFromXmlTheory ffxi axml
    theorycons = conSensXNWONFromXmlTheory ffxi axml
    caslsign =
      Sign
        {
            sortSet = Set.map xnWOaToa (ts_sorts ts)
          , sortRel =
              Rel.fromList
                $
                map
                  (\(a, b) -> (xnWOaToa a, xnWOaToa b))
                  $
                  (Rel.toList (ts_sortrelation ts))
          , opMap =
              implodeSetToMap
                opTypeXNWONToOpType
                (ts_operators ts)
          , predMap =
              implodeSetToMap
                predTypeXNWONToPredType
                (ts_predicates ts)
          , assocOps = Map.empty
          , varMap = Map.empty
          , envDiags = []
          , globAnnos = Hets.emptyGlobalAnnos
          , extendedInfo = ()
          , sentences = []
                
        }
    theory =
      G_theory
        CASL
        caslsign
        (
          Prover.toThSens
            $
            map
              xnWOaToa
              (
                (Set.toList theorysens)
                ++ (Set.toList theorycons)
              )
        )
    reftheory = G_theory CASL caslsign (Prover.toThSens [])
    node =
      if isRefSpec ts
        then
          DGRef
            {
                dgn_name = ts_nodename ts
              , dgn_libname =
                  ASL.Lib_id
                    (ASL.Indirect_link (ts_source ts) Id.nullRange)
              , dgn_node = ts_realnodenum ts
              , dgn_theory = reftheory
              , dgn_nf = Nothing
              , dgn_sigma = Nothing
            }
        else
          DGNode
            {
                dgn_name = ts_nodename ts
              , dgn_theory = theory
              , dgn_sigma = Nothing
              , dgn_origin = DGBasic
              , dgn_cons = None
              , dgn_cons_status = LeftOpen
              , dgn_nf = Nothing
            }
  in
    (ts_nodenum ts, node)

  where
    
    implodeSetToMap::
      (Eq a, Ord a, Eq b, Ord b, Eq c, Ord c)=>
        (b->c)
      ->Set.Set (XmlNamedWON a, b)
      ->Map.Map a (Set.Set c)
    implodeSetToMap
      convert
      theset
      =
      Set.fold
        (\(xa, b) m ->
          Map.insertWith
            Set.union
            (xnWOaToa xa)
            (Set.singleton (convert b))
            m
        )
        Map.empty
        theset

processAllDefLinks::
    [TheorySpecification]
  ->[LinkSpecification]
  ->[TheorySpecification]
processAllDefLinks
  tslist
  lslist
  =
  let
    numberOfDefLinks =
      foldl
        (\ndl ls ->
          if isDefLink ls
            then
              ndl + 1
            else
              ndl
        )
        (0::Int)
        lslist
    maxNoAction = length lslist
    ((processed, _), (final_pdl, _)) =
      until
        (\(_, (processedDefLinks, _)) ->
          processedDefLinks == numberOfDefLinks
        )
        (\((pts, ls:r), (pdl, nas)) ->
          if isDefLink ls
            then
              let
                toname = ls_toname ls
                unprocessedPrevious =
                  filter
                    (\ls' ->
                      isDefLink ls'
                      && ls_toname ls' == (ls_fromname ls)
                    )
                    r
              in
                if (length unprocessedPrevious == 0) || nas > maxNoAction
                  then
                    let
                      totspec = head $ filter (\ts -> ts_name ts == toname) pts
                      fromtspec = head $ filter (\ts -> ts_name ts == (ls_fromname ls)) pts
                      newtotspec =
                        (\x ->
                          if nas > maxNoAction
                            then
                              Debug.Trace.trace
                                (
                                  "Forcing link: " ++ (ls_fromname ls)
                                  ++ " -> " ++ toname
                                )
                                x
                            else
                              x
                        )
                        (
                        performDefLinkSpecification
                          fromtspec
                          ls
                          totspec
                        )
                      newpts =
                        map
                          (\ts ->
                            if ts_name ts == ts_name newtotspec
                              then
                                if ts_nodenum ts /= ts_nodenum newtotspec
                                  then
                                    Debug.Trace.trace
                                      (
                                        "Warning: Same names found ! "
                                        ++ (show (ts_nodenum ts, ts_name ts))
                                        ++ " and "
                                        ++ (show (ts_nodenum newtotspec, ts_name newtotspec))
                                      )
                                      ts
                                  else
                                    newtotspec
                              else
                                ts
                          )
                          pts
                    in
                      ( (newpts, r), (pdl + 1, 0) )
                  else
                    ( (pts, r++[ls]), (pdl, nas+1) )
            else
              ((pts, r), (pdl, nas+1))
        )
        ((tslist, lslist), (0::Int,0::Int))
  in
    if final_pdl /= numberOfDefLinks
      then
        Debug.Trace.trace
          (
            "Error while processing. Stopped after " ++ show final_pdl ++ " of "
            ++ show numberOfDefLinks ++ " links were processed..."
          )
          processed
      else
        processed
  where
    
    isDefLink::LinkSpecification->Bool
    isDefLink ls =
      case ls_type ls of
        LocalDef -> True
        GlobalDef -> True
        HidingDef -> True
        _ -> False

performDefLinkSpecification::
    TheorySpecification
  ->LinkSpecification
  ->TheorySpecification
  ->TheorySpecification
performDefLinkSpecification
  tsFrom
  ls
  tsTo
  =
  let
   newTS =
    if isDef (ls_type ls)
      then
        let
          (hidden, req) = ls_hreql ls
          -- Sorts
          fromSorts =
            if isLocal (ls_type ls)
              then
                Set.filter
                  (\xns -> xnWOaToO xns == ts_nodenum tsFrom)
                  (ts_sorts tsFrom)
              else
                (ts_sorts tsFrom)
          availSorts = Set.filter (\xns -> not $ elem (xnName xns) hidden) fromSorts
          newSorts =
            Set.fold
              (\xns nS ->
                case
                  find
                    (\((_, oldName),_) -> oldName == xnName xns)
                    req
                of
                  Nothing -> nS ++ [xns]
                  (Just (_, (_, newName))) ->
                    case
                      find
                        (\to_xns -> xnName to_xns == newName)
                        (Set.toList (ts_sorts tsTo))
                    of
                      Nothing ->
                        Debug.Trace.trace
                          (
                            "Warning: Sort morphism not possible for "
                            ++ (xnName xns) ++ " -> " ++ newName
                          )
                          nS
                      (Just _) -> nS
              )
              []
              availSorts
          mergedSorts =
            Set.union
              (ts_sorts tsTo)
              (Set.fromList newSorts)
          -- Predicates
          fromPreds = 
            if isLocal (ls_type ls)
              then
                Set.filter
                  (\(xnpid, _) -> xnWOaToO xnpid == ts_nodenum tsFrom)
                  (ts_predicates tsFrom)
              else
                (ts_predicates tsFrom)
          availPreds = Set.filter (\(xnpid, _) -> not $ elem (xnName xnpid) hidden) fromPreds
          newPreds =
            Set.fold
              (\(xnp@(xnpid, _)) nP ->
                case
                  find
                    (\((_, oldName),_) -> oldName == xnName xnpid)
                    req
                of
                  Nothing -> nP ++ [xnp]
                  (Just (_,(_,newName))) ->
                    case
                      find
                        (\(to_xnpid, _) -> xnName to_xnpid == newName)
                        (Set.toList (ts_predicates tsTo))
                    of
                      Nothing ->
                        Debug.Trace.trace
                          (
                            "Warning: Predicate morphism not possible for "
                            ++ (xnName xnpid) ++ " -> " ++ newName
                          )
                          nP
                      (Just _) -> nP
              )
              []
              availPreds
          mergedPreds =
            Set.union
              (ts_predicates tsTo)
              (Set.fromList newPreds)
          -- Operators
          fromOps = 
            if isLocal (ls_type ls)
              then
                Set.filter
                  (\(xnoid, _) -> xnWOaToO xnoid == ts_nodenum tsFrom)
                  (ts_operators tsFrom)
              else
                (ts_operators tsFrom)
          availOps = Set.filter (\(xnoid, _) -> not $ elem (xnName xnoid) hidden) fromOps
          newOps =
            Set.fold
              (\(xno@(xnoid, _)) nO ->
                case
                  find
                    (\((_, oldName),_) -> oldName == xnName xnoid)
                    req
                of
                  Nothing -> nO ++ [xno]
                  (Just (_,(_,newName))) ->
                    case
                      find
                        (\(to_xnoid, _) -> xnName to_xnoid == newName)
                        (Set.toList (ts_operators tsTo))
                    of
                      Nothing ->
                        Debug.Trace.trace
                          (
                            "Warning: Operator morphism not possible for "
                            ++ (xnName xnoid) ++ " -> " ++ newName
                          )
                          nO
                      (Just _) -> nO
              )
              []
              availOps
          mergedOps =
            Set.union
              (ts_operators tsTo)
              (Set.fromList newOps)
          -- checks
          checkedRels =
            Rel.fromList
              $
              map
                (\(s1, s2) ->
                  (findRealSort mergedSorts s1, findRealSort mergedSorts s2)
                )
                $
                Rel.toList (ts_sortrelation tsTo)
          checkedPreds =
            Set.map
              (\(xnpid, xnpt) ->
                (
                    xnpid
                  , xnpt
                    {
                      predArgsXNWON =
                        map (findRealSort mergedSorts) (predArgsXNWON xnpt) 
                    }
                )
              )
              mergedPreds
          checkedOps =
            Set.map
              (\(xnoid, xnot) ->
                (
                    xnoid
                  , xnot
                    {
                        opArgsXNWON =
                          map (findRealSort mergedSorts) (opArgsXNWON xnot) 
                      , opResXNWON = findRealSort mergedSorts (opResXNWON xnot)
                    }
                )
              )
              mergedOps
        in
          tsTo
            {
                ts_sorts = mergedSorts
              , ts_sortrelation = checkedRels
              , ts_predicates = checkedPreds
              , ts_operators = checkedOps
            }
      else -- Thms only affect morphisms
        tsTo
  in
    if (ls_fromname ls) /= (ts_name tsFrom) || (ls_toname ls) /= (ts_name tsTo)
      then
        error "Wrong application!"
      else
        newTS

  where

    findRealSort::Set.Set XmlNamedWONSORT->XmlNamedWONSORT->XmlNamedWONSORT
    findRealSort sorts s =
      if xnWOaToO s == -1
        then
          let
            tssorts = Set.toList sorts
          in
            case
              find
                (\s' -> xnName s' == xnName s)
                tssorts                
            of
              Nothing -> s
              (Just s') -> s'
        else
          s

    isLocal::DGLinkType->Bool
    isLocal LocalDef = True
    isLocal (LocalThm {}) = True
    isLocal _ = False

    isDef::DGLinkType->Bool
    isDef LocalDef = True
    isDef GlobalDef = True
    isDef HidingDef = True
    isDef _ = False

createDGLinkFromLinkSpecification::
    TheorySpecification
  ->LinkSpecification
  ->TheorySpecification
  ->Graph.LEdge DGLinkLab
createDGLinkFromLinkSpecification
  tsFrom
  ls
  tsTo
  =
  let
   caslmorph =
        let
          (hidden, req) = ls_hreql ls
          -- Sorts
          fromSorts =
            if isLocal (ls_type ls)
              then
                Set.filter
                  (\xns -> xnWOaToO xns == ts_nodenum tsFrom)
                  (ts_sorts tsFrom)
              else
                (ts_sorts tsFrom)
          availSorts = Set.filter (\xns -> not $ elem (xnName xns) hidden) fromSorts
          remappedSorts =
            Set.fold
              (\xns rS ->
                case
                  find
                    (\((_, oldName),_) -> oldName == xnName xns)
                    req
                of
                  Nothing -> rS
                  (Just (_, (_, newName))) ->
                    case
                      find
                        (\to_xns -> xnName to_xns == newName)
                        (Set.toList (ts_sorts tsTo))
                    of
                      Nothing ->
                        Debug.Trace.trace
                          (
                            "Warning: Predicate morphism not possible for "
                            ++ (xnName xns) ++ " -> " ++ newName
                          )
                          rS
                      (Just to_xns) -> rS ++ [(xns, to_xns)]
              )
              []
              availSorts
          sortmap =
            Map.fromList
              $
              map
                (\(oxns, nxns) -> (xnWOaToa oxns, xnWOaToa nxns))
                remappedSorts
          -- Predicates
          fromPreds = 
            if isLocal (ls_type ls)
              then
                Set.filter
                  (\(xnpid, _) -> xnWOaToO xnpid == ts_nodenum tsFrom)
                  (ts_predicates tsFrom)
              else
                (ts_predicates tsFrom)
          availPreds = Set.filter (\(xnpid, _) -> not $ elem (xnName xnpid) hidden) fromPreds
          remappedPreds =
            Set.fold
              (\(xnp@(xnpid, _)) rP ->
                case
                  find
                    (\((_, oldName),_) -> oldName == xnName xnpid)
                    req
                of
                  Nothing -> rP
                  (Just (_,(_,newName))) ->
                    case
                      find
                        (\(to_xnpid, _) -> xnName to_xnpid == newName)
                        (Set.toList (ts_predicates tsTo))
                    of
                      Nothing ->
                        Debug.Trace.trace
                          (
                            "Warning: Predicate morphism not possible for "
                            ++ (xnName xnpid) ++ " -> " ++ newName
                          )
                          rP
                      (Just to_xnp) -> rP ++ [(xnp, to_xnp)]
              )
              []
              availPreds
          predmap =
            Map.fromList
              $
              map
                (\( (oxnpid, oxnpt), (nxnpid, _) ) ->
                  ((xnWOaToa oxnpid, predTypeXNWONToPredType oxnpt), xnWOaToa nxnpid)
                )
                remappedPreds
          -- Operators
          fromOps = 
            if isLocal (ls_type ls)
              then
                Set.filter
                  (\(xnoid, _) -> xnWOaToO xnoid == ts_nodenum tsFrom)
                  (ts_operators tsFrom)
              else
                (ts_operators tsFrom)
          availOps = Set.filter (\(xnoid, _) -> not $ elem (xnName xnoid) hidden) fromOps
          remappedOps =
            Set.fold
              (\(xno@(xnoid, _)) rO ->
                case
                  find
                    (\((_, oldName),_) -> oldName == xnName xnoid)
                    req
                of
                  Nothing -> rO
                  (Just (_,(_,newName))) ->
                    case
                      find
                        (\(to_xnoid, _) -> xnName to_xnoid == newName)
                        (Set.toList (ts_operators tsTo))
                    of
                      Nothing ->
                        Debug.Trace.trace
                          (
                            "Warning: Operator morphism not possible for "
                            ++ (xnName xnoid) ++ " -> " ++ newName
                          )
                          rO
                      (Just to_xno) -> rO ++ [(xno, to_xno)]
              )
              []
              availOps
          opmap =
            Map.fromList
              $
              map
                (\( (oxnoid, oxnot), (nxnoid, nxnot) ) ->
                  ((xnWOaToa oxnoid, opTypeXNWONToOpType oxnot), (xnWOaToa nxnoid, opKindX nxnot))
                )
                remappedOps
        in
          Morphism
            {
                msource = Hets.emptyCASLSign
              , mtarget = Hets.emptyCASLSign
              , sort_map = sortmap
              , pred_map = predmap
              , fun_map = opmap
              , extended_map = ()
            }
  in
    if (ls_fromname ls) /= (ts_name tsFrom) || (ls_toname ls) /= (ts_name tsTo)
      then
        error "Wrong application!"
      else
        (
            ts_nodenum tsFrom
          , ts_nodenum tsTo
          , DGLink
              {
                  dgl_morphism = Hets.makeCASLGMorphism caslmorph
                , dgl_type = ls_type ls
                , dgl_origin = ls_origin ls
              }
        )
  where

    isLocal::DGLinkType->Bool
    isLocal LocalDef = True
    isLocal (LocalThm {}) = True
    isLocal _ = False

ffxiFromTheorySpecifications::
    GlobalOptions
  -> TheoryXNSet
  ->[TheorySpecification]
  ->FFXInput
ffxiFromTheorySpecifications
  go
  theoryxnnames
  tslist
  =
    foldl
      (\ffxi ts ->
        ffxi
          {
              xnSortsMap =
                Map.insert (ts_name ts) (ts_sorts ts) (xnSortsMap ffxi)
            , xnRelsMap =
                Map.insert (ts_name ts) (ts_sortrelation ts) (xnRelsMap ffxi)
            , xnPredsMap =
                Map.insert (ts_name ts) (ts_predicates ts) (xnPredsMap ffxi)
            , xnOpsMap =
                Map.insert
                  (ts_name ts)
                  (
                    Set.union
                      (ts_operators ts)
                      (
                        Set.fold
                          (\s1 s2 ->
                            Set.union s1 s2
                          )
                          Set.empty
                          (
                            Set.map
                              snd
                              (ts_constructors ts)
                          )
                      )
                  )
                  (xnOpsMap ffxi)
          }
      )
      emptyFFXInput { xnTheorySet = theoryxnnames, ffxiGO = go }
      tslist

createFFXIMap::
    GlobalOptions
  ->Map.Map String ([TheorySpecification], TheoryXNSet)
  ->Map.Map String FFXInput
createFFXIMap
  go
  tsmap
  =
  Map.foldWithKey
    (\sn (tslist, txns) m ->
      Map.insert sn (ffxiFromTheorySpecifications go txns tslist) m
    )
    Map.empty
    tsmap

createFinalDGraph::
  [Graph.LNode DGNodeLab]
  ->[Graph.LEdge DGLinkLab]
  ->DGraph
createFinalDGraph
  nodes
  edges
  =
  let
    newedges =
      map
        (\(from, to, edge) ->
          let
            fromnode = 
              case
                filter (\(n, _) -> n == from) nodes
              of
                [] -> error ("Cannot make link from #" ++ (show from))
                ((_, n):_) -> n
            tonode =
              case
                filter (\(n, _) -> n == to) nodes
              of
                [] -> error ("Cannot make link to #" ++ (show to))
                ((_, n):_) -> n
            fromcaslsign = Data.Maybe.fromMaybe (error "!") (Hets.getCASLSign (dgn_sign fromnode))
            tocaslsign = Data.Maybe.fromMaybe (error "!") (Hets.getCASLSign (dgn_sign tonode))
            currentmorph = Hets.getCASLMorphLL edge
            newmorph =
              if
                case dgl_type edge of
                  HidingDef -> True
                  HidingThm {} -> True
                  _ -> False
                then
                  currentmorph
                    {
                        mtarget = fromcaslsign
                      , msource = tocaslsign
                    }
                else
                  currentmorph
                    {
                        mtarget = tocaslsign
                      , msource = fromcaslsign
                    }
          in
            (
                from
              , to
              , edge
                {
                  dgl_morphism = Hets.makeCASLGMorphism newmorph 
                }
            )
        )
        edges
  in
    Graph.mkGraph nodes newedges
   
addConstructorsTheorySpecification::
  TheorySpecification
  ->FFXInput
  ->AnnXMLN
  ->TheorySpecification
addConstructorsTheorySpecification
  ts
  ffxi
  axml
  =
  let
    theorycons = consXNWONFromXmlTheory ffxi axml
    tcset =
      foldl
        (\s (x, xl) ->
          Set.insert (x, Set.fromList xl) s
        )
        Set.empty
        theorycons
  in
    ts
      {
        ts_constructors = tcset
      }

processConstructors::
  Map.Map String ([TheorySpecification], b, c, Set.Set AnnXMLN)
  ->Map.Map String FFXInput
  ->Map.Map String ([TheorySpecification], b, c, Set.Set AnnXMLN)
processConstructors
  tsmap
  ffximap
  =
  Map.mapWithKey
    (\k (tslist, b, c, axmls) ->
      let
        thisffxi =
          Map.findWithDefault
            (error "error finding ffxi!")
            k
            ffximap
        mappedspecs =
          map
            (\ts ->
              let
                thisaxml =
                  case
                    find (\axml -> axAnn axml == (ts_nodenum ts)) (Set.toList axmls)
                  of
                    Nothing -> error ("no xml for " ++ ts_name ts)
                    (Just x) -> x
              in
                if isRefSpec ts
                  then
                    ts
                  else
                    addConstructorsTheorySpecification ts thisffxi thisaxml
            )
            tslist
      in
        (mappedspecs, b, c, axmls)
    )
    tsmap

createGraphParts::
  Map.Map String ([TheorySpecification], [LinkSpecification], c, Set.Set AnnXMLN)
  ->Map.Map String FFXInput
  ->Map.Map String ([Graph.LNode DGNodeLab], [Graph.LEdge DGLinkLab])
createGraphParts
  tsmap
  ffximap
  =
  Map.mapWithKey
    (\k (tslist, lslist, _, axmls) ->
      let
        thisffxi =
          Map.findWithDefault
            (error "error finding ffxi!")
            k
            ffximap
        nodes =
          map
            (\ts ->
              let
                thisaxml =
                  case
                    find (\axml -> axAnn axml == (ts_nodenum ts)) (Set.toList axmls)
                  of
                    Nothing -> error ("no xml for " ++ ts_name ts)
                    (Just x) -> x
              in
                createNodeFromSpec
                  thisffxi
                  thisaxml
                  ts
            )
            tslist
        edges =
          map
            (\ls ->
              let
                fromts =
                  case
                    filter (\ts -> ts_name ts == ls_fromname ls) tslist
                  of
                    [] -> error ("Unable to find source node " ++ (ls_fromname ls))
                    (n:_) -> n
                tots =
                  case
                    filter (\ts -> ts_name ts == ls_toname ls) tslist
                  of
                    [] -> error ("Unable to find target node " ++ (ls_toname ls))
                    (n:_) -> n
              in
                createDGLinkFromLinkSpecification
                  fromts
                  ls
                  tots
            )
            lslist
      in
        (nodes, edges)
    )
    tsmap

importGraphToLibEnv::
    GlobalOptions
  ->ImportGraph (HXT.XmlTrees)
  ->(ASL.LIB_NAME, DGraph, LibEnv)
importGraphToLibEnv
  go
  ig
  =
  let
    specMap = createSpecMap go ig
    processedSpecMap = processSpecMap specMap
    ffxiMap =
      createFFXIMap
        go
        (Map.map (\(a, _, c, _) -> (a, c)) processedSpecMap)
    conProcSpecMap = processConstructors processedSpecMap ffxiMap
    partMap = createGraphParts conProcSpecMap ffxiMap 
    graphMap =
      Map.map
        (\(nodes, edges) ->
          createFinalDGraph nodes edges
        )
        partMap
    libenv =
      Map.fromList
        $
        map
          (\(sn, dg) ->
            (
                (ASL.Lib_id (ASL.Indirect_link sn Id.nullRange)) 
              , emptyGlobalContext { devGraph = dg }
            )
          )
          (Map.toList graphMap)
    firstSourceNode = Data.Maybe.fromMaybe (error "!") $ Graph.lab ig 1
    firstSource = (\(S (sn, _) _) -> sn) firstSourceNode
    asKey = (ASL.Lib_id (ASL.Indirect_link firstSource Id.nullRange)) 
    firstDG = lookupDGraph asKey libenv
  in
    (asKey, firstDG, libenv)

data LinkSpecification =
  LinkSpecification 
    {
        ls_type :: DGLinkType
      , ls_origin :: DGOrigin
      , ls_fromname :: XmlName
      , ls_toname :: XmlName
      --, ls_id :: Maybe XmlName
      , ls_hreql :: Hets.HidingAndRequationList
    }
  deriving (Show, Eq)

data TheorySpecification =
  TheorySpecification
    {
        ts_name :: XmlName
      , ts_source :: String
      , ts_nodename :: NODE_NAME
      , ts_nodenum :: Graph.Node
      , ts_sorts :: Set.Set XmlNamedWONSORT
      , ts_sortrelation :: Rel.Rel XmlNamedWONSORT
      , ts_predicates :: Set.Set (XmlNamedWONId, PredTypeXNWON)
      , ts_operators :: Set.Set (XmlNamedWONId, OpTypeXNWON)
      , ts_constructors :: Set.Set (XmlNamedWONId, Set.Set (XmlNamedWONId, OpTypeXNWON)) -- made from sentences on writeout to OMDoc
    }
  | ReferenceSpecification
    {
        ts_name :: XmlName
      , ts_source :: String
      , ts_nodename :: NODE_NAME
      , ts_nodenum :: Graph.Node
      , ts_realnodenum :: Graph.Node
      , ts_sorts :: Set.Set XmlNamedWONSORT
      , ts_sortrelation :: Rel.Rel XmlNamedWONSORT
      , ts_predicates :: Set.Set (XmlNamedWONId, PredTypeXNWON)
      , ts_operators :: Set.Set (XmlNamedWONId, OpTypeXNWON)
      , ts_constructors :: Set.Set (XmlNamedWONId, Set.Set (XmlNamedWONId, OpTypeXNWON)) -- made from sentences on writeout to OMDoc
    }
  deriving (Show, Eq)

isRefSpec::TheorySpecification->Bool
isRefSpec (ReferenceSpecification {}) = True
isRefSpec _ = False

createLinkSpecifications::
  GlobalOptions
  ->HXT.XmlTrees
  ->TheoryXNSet
  ->Set.Set AnnXMLN
  ->[LinkSpecification]
createLinkSpecifications {-go-}_ omdoc theoryxnset axtheoryset =
  let
    imports' = importsFromAnnXMLSet theoryxnset axtheoryset
    glTheoIncs = glThmsFromXmlLS (applyXmlFilter getChildren omdoc)
    lsedges =
      foldl
        (\lsle (nodename, nodeimports) ->
          (foldl (\lsle' ({-tagnum-}_, (ni, {-mmm-}_, hreq, isGlobal)) ->
            let
              hreqmorph = Hets.emptyCASLMorphism
              hreqgmorph = 
                Hets.makeCASLGMorphism hreqmorph 
              isHiding = not $ Hets.isNonHidingHidAndReqL hreq
              ddgl =
                (if isGlobal
                  then 
                    if isHiding
                      then
                        defaultDGLinkLab { dgl_type = Static.DevGraph.HidingDef }
                      else
                        defaultDGLinkLab
                  else
                    defaultDGLinkLab { dgl_type = Static.DevGraph.LocalDef }
                ) {
                      dgl_morphism = hreqgmorph
                    , dgl_origin =
                      if Hets.isEmptyHidAndReqL hreq
                        then
                          dgl_origin defaultDGLinkLab
                        else
                          DGTranslation
                  }
            in
              lsle' ++
                  [
                    LinkSpecification
                      {
                          ls_type = dgl_type ddgl
                        , ls_fromname = ni
                        , ls_toname = nodename
                        , ls_hreql = hreq
                        , ls_origin = dgl_origin ddgl
                      }
                  ]
                
            ) lsle $ Set.toList nodeimports)
        ) -- ledges fold end
        []
        $
        Map.toList imports'
    gledges =
      foldl
        (\lsle (_, nodename, (from, hreq, cons, isGlobal)) ->
          let
            hreqmorph = Hets.emptyCASLMorphism
            hreqgmorph = 
              Hets.makeCASLGMorphism hreqmorph 
            isHiding = not $ Hets.isNonHidingHidAndReqL hreq
            ddgl =
              (if isGlobal
                then 
                  if isHiding
                    then
                      defaultDGLinkLab
                        {
                          dgl_type =
                            Static.DevGraph.HidingThm
                              Hets.emptyCASLGMorphism
                              Static.DevGraph.LeftOpen
                        }
                    else
                      defaultDGLinkLab
                        {
                          dgl_type =
                            Static.DevGraph.GlobalThm
                              Static.DevGraph.LeftOpen
                              cons
                              Static.DevGraph.LeftOpen
                        }
                else
                  defaultDGLinkLab
                    {
                      dgl_type =
                        Static.DevGraph.LocalThm
                          Static.DevGraph.LeftOpen
                          cons
                          Static.DevGraph.LeftOpen
                    }
              ) {
                    dgl_morphism = hreqgmorph
                  , dgl_origin =
                    if Hets.isEmptyHidAndReqL hreq
                      then
                        dgl_origin defaultDGLinkLab
                      else
                        DGTranslation
                }
          in
            lsle ++
                [
                  LinkSpecification
                    {
                        ls_type = dgl_type ddgl
                      , ls_fromname = from
                      , ls_toname = nodename
                      , ls_hreql = hreq
                      , ls_origin = dgl_origin ddgl
                    }
                ]
                
        ) -- ledges fold end
        []
        $
        glTheoIncs
  in
    (lsedges ++ gledges)

getCatalogueInformation::HXT.XmlTrees->(Map.Map String String)
getCatalogueInformation t =
  let
    catalogue = applyXmlFilter (getChildren .> isTag "catalogue") t
    locs = applyXmlFilter (getChildren .> isTag "loc") catalogue
    list = foldl (\l loc ->
      l ++ [ (xshow $ applyXmlFilter (getValue "theory") [loc],
              xshow $ applyXmlFilter (getValue "omdoc") [loc])
           ]
      ) [] locs
  in
    Map.fromList list
              

-- | theory name, theory source (local)
data TheoryImport = TI (String, String)

instance Show TheoryImport where
  show (TI (tn, ts)) = ("Import of \"" ++ tn ++ "\" from \"" ++ ts ++ "\".")

-- | source name, source (absolute)
--data Source a = S { nameAndURI::(String, String), sContent::a } 
data Source a = S (String, String) a

instance Show (Source a) where
  show (S (sn, sf) _) = ("Source \"" ++ sn ++ "\" File : \"" ++ sf ++ "\".");

type ImportGraph a = CLGraph.Gr (Source a) TheoryImport 


maybeGetXml::String->IO (Maybe HXT.XmlTrees)
maybeGetXml source =
  do
    xml <- HXT.run' $
      HXT.parseDocument
        [
            (HXT.a_source, source)
          , (HXT.a_issue_errors, HXT.v_0)
          , (HXT.a_check_namespaces, HXT.v_1)
          , (HXT.a_validate, HXT.v_0)
        ]
        HXT.emptyRoot
    return
      (let
        status = (read $ HXT.xshow $ getValue "status" (head xml))::Int
        result = if status < HXT.c_err then (Just xml) else Nothing
      in
        result)
                                
maybeFindXml::String->[String]->IO (Maybe HXT.XmlTrees)
maybeFindXml source includes =
  let
    muri = URI.parseURIReference source
    uri = fromMaybe (error "cannot parse URIReference") muri
    isFile = (length (URI.uriScheme $ uri)) == 0
    filePath = URI.uriPath uri
    isAbsolute = (isFile && ( (head filePath) == '/')) || (URI.isAbsoluteURI source)
    possibilities = source:(if not isAbsolute then map (++"/"++source) includes else [])
  in
    do
      case muri of
        Nothing -> return Nothing
        _ -> firstSuccess (map maybeGetXml possibilities)
  where
    firstSuccess::(Monad m)=>[(m (Maybe a))]->(m (Maybe a))
    firstSuccess [] = return Nothing
    firstSuccess (l:r) =
      do
        res <- l
        case res of
          Nothing -> firstSuccess r
          _ -> return res
                                  


getImportedTheories::HXT.XmlTrees->Map.Map String String
getImportedTheories xml =
  let
    omdoc = applyXmlFilter (getChildren .> isTag "omdoc") xml
    catmap = getCatalogueInformation omdoc
    timports = map (\n -> xshow [n]) $
      applyXmlFilter
        (getChildren .> isTag "theory" .>
                getChildren .> isTag "imports" .> getValue "from")
        omdoc
    tincs = map (\n -> xshow [n]) $
      applyXmlFilter
        (getChildren .>
          (isTag "theory-inclusion" +++ isTag "axiom-inclusion") .>
          getValue "from"
        )
        omdoc
    tincsrefs = map (\n -> xshow [n]) $
      applyXmlFilter
        (getChildren .>
          (isTag "theory-inclusion" +++ isTag "axiom-inclusion") .>
          getValue "to"
        )
        omdoc
    externalImports = foldl (\eI i ->
      let
        muri = URI.parseURIReference i
        uri = fromMaybe (error "cannot parse URIReference") muri
        path = URI.uriPath uri
        fragment = drop 1 $ URI.uriFragment uri
      in
        if ((length path) > 0) && ((length fragment) > 0)
          then
            Map.insert fragment path eI
          else
            eI
      ) Map.empty (timports ++ tincs ++ tincsrefs)
  in
    Map.union catmap externalImports
        
                                        
makeImportGraphFullXml::GlobalOptions->String->(IO (ImportGraph HXT.XmlTrees))
makeImportGraphFullXml go source =
  do
    curdirs <- System.Directory.getCurrentDirectory
    -- trick the uri parser into faking a document to make a relative path later
    mcduri <- return $ URI.parseURIReference ("file://"++curdirs++"/a")
    alibdir <- return $ case mcduri of
      Nothing -> (fixLibDir (libdir (hetsOpts go)))
      (Just cduri) -> relativeSource cduri (fixLibDir (libdir (hetsOpts go)))
    putIfVerbose (hetsOpts go) 0 ("Loading " ++ source ++ "...") 
    mdoc <- maybeFindXml source [alibdir]
    case mdoc of
      Nothing -> ioError $ userError ("Unable to find \"" ++ source ++ "\"")
      (Just doc) ->
        (let
          omdoc = applyXmlFilter (getChildren .> isTag "omdoc") doc
          omdocid = xshow $ applyXmlFilter (getQualValue "xml" "id") omdoc
          mturi =
            URI.parseURIReference
              $
              xshow
                $
                getValue "transfer-URI" (head doc)
          turi = fromMaybe (error "Cannot parse URIReference...") mturi
          muriwithoutdoc =
            URI.parseURIReference
              $
              (reverse $ dropWhile (/='/') $ reverse (show turi))
          uriwithoutdoc =
            fromMaybe
              (error "Cannot create path to document...")
              muriwithoutdoc
          docmap = getImportedTheories doc
          rdocmap = Map.toList docmap -- Map.toList $ Map.map (\s -> relativeSource turi s) docmap
          initialgraph = Graph.mkGraph [(1, S (omdocid, (show turi)) omdoc)] []
        in
          foldl
            (\gio (itname, ituri)  ->
              gio >>= \g -> buildGraph g 1 uriwithoutdoc (TI (itname, ituri)) alibdir
            ) (return initialgraph) rdocmap
        )
  where

  fixLibDir::FilePath->FilePath
  fixLibDir fp =
    case fp of 
      [] -> fp
      _ ->
        if last fp == '/'
          then
            init fp
          else
            fp

  buildGraph::
    ImportGraph HXT.XmlTrees
    ->Graph.Node
    ->URI.URI
    ->TheoryImport
    ->String
    ->IO (ImportGraph HXT.XmlTrees)
  buildGraph ig n frompath ti@(TI (theoname, theouri)) alibdir =
    let
      includes = [alibdir, (show frompath)]
      possources =
        theouri:(
          map
            (\s -> s ++ (if (last s)=='/' then "" else "/") ++ theouri)
            includes
          )
      mimportsource =
        find
          (\(_, (S (_, suri) _)) -> any (\s -> suri == s) possources)
          (Graph.labNodes ig)
      (S (curid, _) _) =
        case Graph.lab ig n of
          Nothing -> error "!"
          (Just x) -> x
    in
    do
      case mimportsource of
        (Just (inum, (S (isn,_) _))) ->
            do
              putIfVerbose
                (hetsOpts go)
                0
                ("Loading " ++ theoname ++ " from "
                  ++ theouri ++ " (cached) for " ++ curid ++ "..." 
                )
              return 
                (if inum == n then
                   debugGO
                    go
                    "mIGFXbG"
                    ("Back-reference in " ++ isn ++ " to " ++ theoname)
                    ig
                 else
                   (Graph.insEdge (n, inum, ti) ig)
                )
        Nothing ->
          do
            putIfVerbose
              (hetsOpts go)
              0
              ("Loading " ++ theoname ++ " from " ++ theouri ++ " for " ++ curid ++ "...")
            mdocR <- maybeFindXml theouri includes
            mdoc <- case mdocR of
              Nothing ->
                do
                  putIfVerbose
                    (hetsOpts go)
                    0
                    ("error at loading from " ++ (show includes))
                  ioError
                    $
                    userError
                      ("Unable to find \"" ++ theouri
                        ++ "\" (looked in " ++ (show includes) ++ ")"
                      )
              _ -> return mdocR
            (newgraph, nn, importimports, newbase) <-
              return $
                (
                  let
                    doc =
                      fromMaybe
                        (error
                          ("Unable to import \""++ theoname 
                            ++ "\"from \"" ++ theouri ++ "\"")
                        )
                        mdoc
                    omdoc = applyXmlFilter (getChildren .> isTag "omdoc") doc
                    omdocid =
                      xshow
                        $
                        applyXmlFilter (getQualValue "xml" "id") omdoc
                    imturi =
                      URI.parseURIReference
                        $
                        xshow $ getValue "transfer-URI" (head doc)
                    ituri = fromMaybe (error "Cannot parse URIReference...") imturi
                    miuriwithoutdoc =
                      URI.parseURIReference
                        $
                        (reverse $ dropWhile (/='/') $ reverse (show ituri))
                    iuriwithoutdoc =
                      fromMaybe
                        (error "Cannot create path to document...")
                        miuriwithoutdoc
                    iimports = getImportedTheories doc
                    irimports = Map.toList iimports
                    newnodenum = (Graph.noNodes ig) + 1
                    newsource = S (omdocid, (show ituri)) omdoc
                    newgraph =
                      Graph.insEdge
                        (n, newnodenum, ti)
                        $
                        Graph.insNode (newnodenum, newsource) ig
                  in
                    (newgraph, newnodenum, irimports, iuriwithoutdoc)
                )
            foldl
              (\nigio (itheoname, itheouri) ->
                nigio >>= \nig ->
                  buildGraph nig nn newbase (TI (itheoname, itheouri)) alibdir
              )
              (return newgraph)
              importimports
  relativeSource::URI.URI->String->String
  relativeSource uri s =
    let
      msuri = URI.parseURIReference s
      suri = fromMaybe (error "Cannot parse URIReference") msuri
      mreluri = URI.relativeTo suri uri
      reluri = fromMaybe (error "Cannot create relative URI...") mreluri
    in
      case msuri of
        Nothing -> s
        _ -> case mreluri of
          Nothing -> s
          _ -> URI.uriToString id reluri ""
                                                
{- |
  After merging all sentences for a target-node, the morphisms still
  point to the old signature. This function updates the target-
  signatures of all morphisms.
-}
{-
fixMorphisms::DGraph->DGraph
fixMorphisms dg =
  let
    labnodes = Graph.labNodes dg
    labedges = Graph.labEdges dg
    newedges =
      foldl
        (\ne (from, to, dgl) ->
          let
            caslmorph = Hets.getCASLMorphLL dgl
            tonode =
              fromMaybe
                (error "!")
                $
                Graph.lab dg to
            fromnode =
              fromMaybe
                (error "!")
                $
                Graph.lab dg from
            tonodesign =
              Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign tonode)
            fromnodesign =
              Hets.getJustCASLSign $ Hets.getCASLSign (dgn_sign fromnode)
            newmorph =
              if
                case dgl_type dgl of
                  HidingDef -> True
                  HidingThm {} -> True
                  _ -> False
                then
                  -- swap source and target for hiding...
                  caslmorph
                    {
                        msource = tonodesign
                      , mtarget = fromnodesign
                    }
                else
                  caslmorph
                    {
                        msource = fromnodesign
                      , mtarget = tonodesign
                    }
          in
            ne ++
              [
                (
                  from
                  , to
                  , dgl { dgl_morphism = Hets.makeCASLGMorphism newmorph }
                )
              ]
        )
        []
        labedges
  in
    Graph.mkGraph labnodes newedges
-}

createQuasiMappedLists::Eq a=>[(a,a)]->[(a,[a])]
createQuasiMappedLists = foldl (\i x -> insert x i) []
  where 
  insert::(Eq a, Eq b)=>(a,b)->[(a,[b])]->[(a,[b])]
  insert (a,b) [] = [(a,[b])]
  insert (a,b) ((a' ,l):r) =
    if a == a'
      then
        (a' , l++[b]):r
      else
        (a', l) : insert (a,b) r
        
isTrueAtom::(FORMULA ())->Bool
isTrueAtom (True_atom _) = True
isTrueAtom _ = False

-- X M L -> FORMULA

unwrapFormulasXNWON::FFXInput->AnnXMLN->[(XmlNamed Hets.SentenceWO)]
unwrapFormulasXNWON ffxi anxml =
  let
    axioms =
      applyXmlFilter (getChildren .> isTag "axiom") (axXml anxml)
  in
    foldl
      (\unwrapped axxml ->
        let
          ansen = unwrapFormulaXNWON ffxi (AXML (axAnn anxml) [axxml])
          ansenname = Ann.senName ansen
          anpress = getPresentationString ansenname (axXml anxml)
          anname =
            case anpress of
              [] ->
                debugGO
                  (ffxiGO ffxi)
                  "uFXNWON"
                  ("F-Name: " ++ ansenname)
                  ansenname
              _ ->
                debugGO
                  (ffxiGO ffxi)
                  "uFXNWON"
                  ("F-Pres: " ++ anpress)
                  anpress
        in
          (
            unwrapped
            ++ [
                XmlNamed
                  (Hets.mkWON (ansen { Ann.senName = anname }) (axAnn anxml))
                  ansenname
               ]
          )
      )
      []
      axioms

unwrapFormulaXNWON::FFXInput->AnnXMLN->(Ann.Named CASLFORMULA)
unwrapFormulaXNWON ffxi anxml =
  let
    axname =
      xshow
        $
        applyXmlFilter
          (getQualValue axiomNameXMLNS axiomNameXMLAttr)
          (axXml anxml)
    formtree =
      applyXmlFilter
        (getChildren .> isTag "FMP" .> getChildren
          .> isTag "OMOBJ" .> getChildren)
        (axXml anxml)
  in
    Ann.NamedSen
      (axname)
      True
      False
      (formulaFromXmlXN ffxi (AXML (axAnn anxml) formtree))

data FFXInput = FFXInput {
         ffxiGO :: GlobalOptions
        ,xnTheorySet :: TheoryXNSet -- set of theorys (xmlnames + origin in graph)
        ,xnSortsMap :: Map.Map XmlName (Set.Set XmlNamedWONSORT) -- theory -> sorts mapping
        ,xnRelsMap :: Map.Map XmlName (Rel.Rel XmlNamedWONSORT) -- theory -> rels
        ,xnPredsMap :: Map.Map XmlName (Set.Set (XmlNamedWONId, PredTypeXNWON)) -- theory -> preds
        ,xnOpsMap :: Map.Map XmlName (Set.Set (XmlNamedWONId, OpTypeXNWON)) -- theory -> ops
        }
  deriving Show
        
        
emptyFFXInput::FFXInput
emptyFFXInput =
        FFXInput
                emptyGlobalOptions
                Set.empty
                Map.empty
                Map.empty
                Map.empty
                Map.empty

stripFragment::String->String
stripFragment s =
  let
    (file, theo) = span (/='#') s
  in
    case theo of
      [] -> file
      _ -> drop 1 theo
                
formulaFromXmlXN::FFXInput->AnnXMLN->FORMULA ()
formulaFromXmlXN ffxi anxml =
  if (applyXmlFilter (isTag "OMBIND") (axXml anxml)) /= [] then -- it's a quantifier...
    let
      quantTree = singleitem 1 (applyXmlFilter (isTag "OMBIND") (axXml anxml))
      quant =
        quantFromName $ xshow $
          applyXmlFilter
            (getChildren .> isTag "OMS" .> withValue "cd" (\s -> (stripFragment s) == caslS) .>
              getValue "name")
            quantTree
      -- first element is the quantification-OMS
      formula =
        drop
          1
          ((applyXmlFilter
            (getChildren .> (isTag "OMA" +++ isTag "OMATTR"
              +++ isTag "OMBIND" +++ isTag "OMS"))
            quantTree)::[HXT.XmlTree]
          ) 
      vardeclS =
        getVarDecls
          (applyXmlFilter
            (getChildren .> isTag "OMBVAR")
            quantTree
          )
      vardeclS2 = createQuasiMappedLists vardeclS
    in
      Quantification
        quant
        (map
          (\(s, vl) ->
            Var_decl
              (map Hets.stringToSimpleId vl)
              (case findByNameAndOrigin
                      (stripFragment s)
                      (axAnn anxml)
                      (mapSetToSet $ xnSortsMap ffxi) of
                 Nothing -> error ("No Sort for " ++ s)
                 (Just x) -> xnWOaToa x
              )
              --(Hets.stringToId s)
              Id.nullRange
          )
          vardeclS2
        )
        (formulaFromXmlXN
          ffxi
          (AXML (axAnn anxml) formula)
        )
        Id.nullRange
  else if (applyXmlFilter (isTag "OMA") (axXml anxml)) /= [] then -- the case begins...
    let
      formTree = applyXmlFilter (isTag "OMA") (axXml anxml)
      applySymXml =
        singleitem 1 (applyXmlFilter (getChildren .> isTag "OMS") formTree)
      applySym = xshow $ applyXmlFilter (getValue "name") applySymXml
      --applySymCD = xshow $ applyXmlFilter (getValue "cd") applySymXml
    in
      let
        formulas =
          map
            (\n -> formulaFromXmlXN ffxi (AXML (axAnn anxml) [n]))
            (
              (applyXmlFilter
                (getChildren .>
                  (isTag "OMA" +++ isTag "OMATTR" +++ isTag "OMBIND")
                )
                formTree
              )::[HXT.XmlTree]
            )
        terms =
          map
            (\n -> termFromXmlXN ffxi (AXML (axAnn anxml) [n]))
            (tail
              (
                (applyXmlFilter
                  (getChildren .>
                    (isTag "OMV" +++ isTag "OMATTR" +++ isTag "OMA"
                      +++ isTag "OMS")
                  )
                  formTree
                )::[HXT.XmlTree]
              )
            )
      in
        -- 'case applySym' does not work if case-strings are non fixed
        -- (above definition is not fixed enough...) 
        --case applySym of
        if applySym == caslConjunctionS then
          Conjunction formulas Id.nullRange
          else
            if applySym == caslDisjunctionS then
              Disjunction formulas Id.nullRange
              else
                if applySym `elem` [caslImplicationS, caslImplication2S] then
                  let
                    boolF =
                      formulaFromXmlXN
                        ffxi
                        (AXML
                          (axAnn anxml)
                          (applyXmlFilter
                            (processChildren (isTag "OMS") .> getChild 2)
                            formTree)
                          ) 
                  in
                    if (length formulas) < 2
                      then
                        Debug.Trace.trace
                          ("Impossible to create implication...")
                          (False_atom Id.nullRange)
                      else
                        Implication
                          (formulas!!0)
                          (formulas!!1)
                          (isTrueAtom(boolF))
                          Id.nullRange
                  else
                    if applySym `elem` [caslEquivalenceS, caslEquivalence2S]
                      then
                        if (length formulas) < 2
                          then
                            Debug.Trace.trace
                              ("Impossible to create equivalence...")
                              (False_atom Id.nullRange)
                          else
                            Equivalence
                              (formulas!!0)
                              (formulas!!1)
                              Id.nullRange
                      else
                        if applySym == caslNegationS
                          then
                            if formulas == []
                              then
                                Debug.Trace.trace
                                  ("Impossible to create negation...")
                                  (False_atom Id.nullRange)
                              else
                                Negation
                                  (formulas!!0)
                                  Id.nullRange
                          else
                            if applySym == caslPredicationS
                              then
                                let
                                   --predxml = applyXmlFilter (processChildren (isTag "OMS" +++ isTag "OMATTR") .> getChild 2) (axXml anxml)
                                  predxml =
                                    applyXmlFilter
                                      (processChildren
                                        (isTag "OMS" +++ isTag "OMATTR") .>
                                          getChild 2
                                      )
                                      formTree
                                  pred' =
                                    (\x ->
                                      if (contains (show x) "predication")
                                        then
                                          debugGO
                                            (ffxiGO ffxi)
                                            "fFXXNm2"
                                            ("predication created! from : "
                                              ++ (xshow predxml)) x
                                        else
                                          x
                                    ) $
                                      (\x ->
                                        debugGO
                                          (ffxiGO ffxi)
                                          "fFXXNm"
                                          ("made pred : " ++ show x)
                                          x
                                      ) $
                                        predicationFromXmlXN
                                          ffxi
                                          (AXML (axAnn anxml) predxml)
                                  --termxml = drop 2 $ (applyXmlFilter (getChildren .> (isTag "OMATTR" +++ isTag "OMA" +++ isTag "OMS")) (axXml anxml))
                                  termxml =
                                    drop 2 $
                                      (applyXmlFilter
                                        (getChildren .>
                                          (isTag "OMATTR" +++ isTag "OMA"
                                            +++ isTag "OMS")
                                        )
                                        formTree
                                      )
                                  predterms =
                                    map
                                      (\tx ->
                                        termFromXmlXN
                                          ffxi
                                          (debugGO
                                            (ffxiGO ffxi)
                                            "fFXXN"
                                            ("will create term(1) from : "
                                              ++ (take 200 $ xshow [tx])
                                            )
                                            (AXML (axAnn anxml) [tx])
                                          )
                                      )
                                      termxml
                                in
                                  if predxml == []
                                    then
                                      Debug.Trace.trace
                                        ("Impossible to create predication...")
                                          (False_atom Id.nullRange)
                                    else
                                      Predication
                                        pred'
                                        predterms
                                        Id.nullRange 
                              else
                                if applySym == caslDefinednessS
                                  then
                                    Definedness
                                      (termFromXmlXN
                                        ffxi
                                        (debugGO
                                          (ffxiGO ffxi)
                                          "fXXN"
                                          ((++) "About to create Definedness from "
                                            $ take 300 $ xshow $ axXml anxml
                                          )
                                          (AXML
                                            (axAnn anxml)
                                            (drop 1 $
                                              (applyXmlFilter
                                                (getChildren .>
                                                  (isTag "OMV" +++ isTag "OMATTR"
                                                    +++ isTag "OMA" +++ isTag "OMS" )
                                                )
                                                (axXml anxml)
                                              )
                                            )
                                          )
                                        )
                                      )
                                      Id.nullRange
                                  else
                                    if applySym == caslExistl_equationS
                                      then
                                        if (length terms) < 2
                                          then
                                            Debug.Trace.trace
                                              ("Impossible to create existl_equation...")
                                              (False_atom Id.nullRange)
                                          else
                                            Existl_equation
                                              (terms!!0)
                                              (terms!!1)
                                              Id.nullRange
                                      else
                                        if applySym == caslStrong_equationS
                                          then
                                            if (length terms) < 2
                                              then
                                                Debug.Trace.trace
                                                  ("Impossible to create strong_equation... ("
                                                    ++ (xshow formTree) ++ ")"
                                                  )
                                                  (False_atom Id.nullRange)
                                              else
                                                Strong_equation
                                                  ((\x ->
                                                    if (contains (show x) "predication")
                                                      then
                                                        debugGO
                                                          (ffxiGO ffxi)
                                                          "fFXXNse"
                                                          ("predication created! from : (0)")
                                                          x
                                                      else
                                                        x
                                                    ) (terms!!0)
                                                  )
                                                  ((\x ->
                                                    if (contains (show x) "predication")
                                                      then
                                                        debugGO
                                                          (ffxiGO ffxi)
                                                          "fFXXNse"
                                                          ("predication created! from : (1)")
                                                          x
                                                      else
                                                        x
                                                      ) (terms!!1)
                                                  )
                                                  Id.nullRange
                                          else
                                            if applySym == caslMembershipS
                                              then
                                                let
                                                  sortxml =
                                                    lastorempty
                                                      (applyXmlFilter
                                                        (getChildren .> isTag "OMS")
                                                        formTree
                                                      )
                                                  sort = xshow $ applyXmlFilter (getValue "name") sortxml
                                                  sortcd =
                                                    stripFragment
                                                      $
                                                      xshow
                                                        $
                                                        applyXmlFilter
                                                          (getValue "cd")
                                                          sortxml
                                                  theosorts =
                                                    Map.findWithDefault
                                                      Set.empty
                                                      sortcd
                                                      (xnSortsMap ffxi) 
                                                  sortxn =
                                                    case findByName sort theosorts of
                                                      Nothing ->
                                                        error
                                                          ("Sort not found in theory!"
                                                            ++ "(" ++ sort ++ ", "
                                                              ++ (show theosorts) ++ ")" 
                                                          )
                                                      (Just x) -> x
                                                in
                                                  if terms == []
                                                    then
                                                      Debug.Trace.trace
                                                        ("Impossible to create Membership...")
                                                        (False_atom Id.nullRange)
                                                    else
                                                      Membership
                                                        (head terms)
                                                        (debugGO
                                                           (ffxiGO ffxi)
                                                           "fFXXN"
                                                           ("Making sort for membership "
                                                            ++ (show $ xnWOaToa sortxn)
                                                            ++ " from " ++ sort
                                                           )
                                                           (xnWOaToa sortxn)
                                                        )
                                                        Id.nullRange
                                              else
                                                if applySym == caslSort_gen_axS
                                                  then
                                                    let
                                                      freeType =
                                                        if (xshow $
                                                          applyXmlFilter
                                                            (getValue "name")
                                                            [(applyXmlFilter
                                                              (getChildren .> isTag "OMS")
                                                              formTree)!!1
                                                            ]
                                                            ) == caslSymbolAtomFalseS
                                                          then
                                                            False
                                                          else
                                                            True
                                                      constraintsx =
                                                        applyXmlFilter
                                                          (
                                                          --getChildren .> isTag "OMBVAR" .> -- removed (see generation)
                                                          getChildren .> isTag "OMBIND"
                                                          )
                                                          formTree
                                                      constraints =
                                                        xmlToConstraintsXN
                                                          ffxi
                                                          (AXML (axAnn anxml) constraintsx)
                                                    in
                                                      Sort_gen_ax constraints freeType
                                                  else
                                                    if applySym /= []
                                                      then
                                                        Debug.Trace.trace
                                                          ("No matching casl-application found! Trying to find predicate...") $ let
                         predterms =
                          map (\n -> termFromXmlXN ffxi (AXML (axAnn anxml) [n])) $ ((applyXmlFilter (getChildren .> (isTag "OMATTR" +++ isTag "OMA")) (axXml anxml))::[HXT.XmlTree])
                         possibilities = findAllByNameWithAnd id fst applySym (mapSetToSet (xnPredsMap ffxi))
                         withThisOrigin = filter (\i -> (xnWOaToO $ fst i) == (axAnn anxml)) possibilities
                      in
                        case (case withThisOrigin of [] -> possibilities; _ -> withThisOrigin) of
                          (i:_) ->
                            Predication (Qual_pred_name (xnWOaToa (fst i)) (Hets.cv_PredTypeToPred_type $ predTypeXNWONToPredType (snd i)) Id.nullRange) predterms Id.nullRange
                          [] ->
                            error ("Could not find predicate for \"" ++ applySym ++ "\"")
                                                      else
                                                        error ("Expected a casl application symbol, but \"" ++ applySym ++ "\" was found!")
  else if (applyXmlFilter (isTag "OMS") (axXml anxml)) /= []
    then
      let
        trueOrFalse =
          xshow $
            singleitem
              1
              (applyXmlFilter
                (isTag "OMS" .> withValue "cd" (\s -> (stripFragment s) == caslS) .>
                  getValue "name"
                )
                (axXml anxml)
              )
      in
        if trueOrFalse == caslSymbolAtomTrueS
          then
            True_atom Id.nullRange
          else
            if trueOrFalse == caslSymbolAtomFalseS
              then
                False_atom Id.nullRange
              else
                Debug.Trace.trace
                  (caslSymbolAtomTrueS ++ " or "
                    ++ caslSymbolAtomFalseS ++ " expected, but \""
                    ++ trueOrFalse ++ "\" found!"
                  )
                  (False_atom Id.nullRange)
  else
    error ("Impossible to create formula from \"" ++ xshow (axXml anxml)++ "\"") 


xmlToConstraintsXN::FFXInput->AnnXMLN->[ABC.Constraint]
xmlToConstraintsXN ffxi anxml =
  map
    (\n ->
      xmlToConstraintXN
        ffxi
        (AXML (axAnn anxml) [n])
    )
    ((applyXmlFilter (isTag "OMBIND") (axXml anxml))::[HXT.XmlTree])
        

xmlToConstraintXN::FFXInput->AnnXMLN->ABC.Constraint
xmlToConstraintXN ffxi anxml =
  let
    sortsx =
      applyXmlFilter
        (getChildren .> isTag "OMS" .> getValue "name")
        (axXml anxml)
    newsort = Hets.stringToId $ xshow $ [sortsx!!0]
    origsort = Hets.stringToId $ xshow $ [sortsx!!0]
    indiopsx =
      applyXmlFilter
        (getChildren .> isTag "OMBVAR" .> getChildren .> isTag "OMATTR")
        (axXml anxml)
    conslist =
      foldl
        (\cl cx ->
          let
            indices =
              xshow
                $
                applyXmlFilter
                  (getChildren .> isTag "OMATP" 
                    .> getChildren .> isTag "OMSTR" .> getChildren
                  )
                  [cx]
            op =
              operatorFromXmlXN
                ffxi
                $
                (\n -> AXML (axAnn anxml) n)
                  $
                  applyXmlFilter
                    (getChildren .> (isTag "OMBIND" +++ isTag "OMS"))
                    [cx]
            il =
              makeIndexList indices
          in
            cl ++ [(op, il)]
        )
        ([]::[(OP_SYMB,[Int])])
        (indiopsx::[HXT.XmlTree])
  in
    ABC.Constraint newsort conslist origsort
          
                
-- An IndexList is constructed from a String like 'n1|n2|n3...nk|'              
makeIndexList::String->[Int]
makeIndexList [] = []
makeIndexList s =
  let
    (number, rest) =
      (takeWhile (\x -> x /= '|') s, dropWhile (\x -> x /= '|') s)
  in
    [read number] ++ (makeIndexList (drop 1 rest))


predicationFromXmlXN::FFXInput->AnnXMLN->PRED_SYMB
predicationFromXmlXN ffxi anxml = 
  let
    symbolXml = applyXmlFilter (isTag "OMS") (axXml anxml)
    sxname = xshow $ applyXmlFilter (getValue "name") symbolXml
    sxcd = stripFragment $ xshow $ applyXmlFilter (getValue "cd") symbolXml
    {-
    theonode = case getNodeForTheoryName (xnTheorySet ffxi) sxcd of
            Nothing -> error ("No Theory for used predicate (Node) !" ++ sxname)
            (Just n) -> n
    -}
    theoxn = case findByName sxcd (xnTheorySet ffxi) of
            Nothing ->
              error
                (
                  "No Theory (" ++ sxcd ++ ") for used predicate (Name) !"
                  ++ sxname ++ " in " ++ show (xnPredsMap ffxi)
                )
            (Just theoxn' ) -> theoxn'
    theopreds = Map.findWithDefault Set.empty (xnName theoxn) (xnPredsMap ffxi) 
    predxnid = case findByName sxname (map fst $ Set.toList theopreds) of
            Nothing ->
              error
                ("No such predicate in Theory! (" ++ show sxname 
                  ++ " in " ++ (show theopreds) ++ ")") 
            (Just predxnid' ) -> predxnid'
    predXNWON = case lookup predxnid $ Set.toList theopreds of
            Nothing -> error "Predicate not found!"
            (Just pxnwon) -> pxnwon
  in
    Qual_pred_name
      (xnWOaToa predxnid)
      (Hets.cv_PredTypeToPred_type $ predTypeXNWONToPredType predXNWON)
      Id.nullRange
                
-- String to Quantifiert...
quantFromName::String->QUANTIFIER
quantFromName s
        | (s == caslSymbolQuantUniversalS) = Universal
        | (s == caslSymbolQuantExistentialS) = Existential
        | (s == caslSymbolQuantUnique_existentialS) = Unique_existential
        | otherwise = error (s++": no such quantifier...")


-- get var decls
getVarDecls::HXT.XmlTrees->[(String, String)]
getVarDecls vt =
  map
    (\t ->
      (
          xshow
            $
            applyXmlFilter
              (getChildren .> isTag "OMATP" .> getChildren .>
                isTag "OMS" .> withValue "name" (/=typeS) .>
                getValue "name"
              )
              [t]
       , xshow
          $
            applyXmlFilter
              (getChildren .> isTag "OMV" .> getValue "name")
              [t]
      )
    )
    (
      (applyXmlFilter (isTag "OMBVAR" .> getChildren .> isTag "OMATTR") vt)
        ::[HXT.XmlTree]
    )


isTermXml::HXT.XmlFilter
isTermXml = isTag "OMV" +++ isTag "OMATTR" +++ isTag "OMA"


isOperatorXml::HXT.XmlFilter
isOperatorXml = isTag "OMATTR" +++ isTag "OMS"


termFromXmlXN::FFXInput->AnnXMLN->(TERM ())
termFromXmlXN ffxi anxml =
  if (applyXmlFilter (isTag "OMV") (axXml anxml)) /= []
    then
      Debug.Trace.trace
        ("Warning: Untyped variable (TERM) from \"" 
          ++ (xshow (axXml anxml))
        ) 
        $
        Simple_id 
          $
          Hets.stringToSimpleId $ xshow 
            $
            applyXmlFilter
              (isTag "OMV" .> getValue "name")
              (axXml anxml)
    else
      if (applyXmlFilter (isTag "OMATTR") (axXml anxml)) /= []
        then
          if
            applyXmlFilter
              (isTag "OMATTR" .> getChildren .>
                isTag "OMATP" .> getChildren .>
                isTag "OMS" .> withSValue "name" "funtype"
              )
              (axXml anxml)
            /= []
            then
              Application (operatorFromXmlXN ffxi anxml) [] Id.nullRange
            else
              Qual_var
                (Hets.stringToSimpleId
                  $
                  xshow
                    $
                    applyXmlFilter
                      (isTag "OMATTR" .> getChildren .>
                        isTag "OMV" .> getValue "name"
                      )
                      (axXml anxml)
                )
                (
                  let
                    varxnsort =
                      xshow
                        $
                        applyXmlFilter
                          (isTag "OMATTR" .> getChildren .>
                            isTag "OMATP" .> getChildren .>
                            isTag "OMS" .> withValue "name" (/=typeS) .>
                            getValue "name"
                          )
                          (axXml anxml)
                    varsort =
                      case
                        findByNameAndOrigin
                          varxnsort
                          (axAnn anxml)
                          (mapSetToSet $ xnSortsMap ffxi)
                      of
                        Nothing ->
                          error
                            ("Cannot find defined sort for \""
                              ++ varxnsort ++"\"" )
                        (Just x) -> xnWOaToa x
                  in
                     varsort
                )
                Id.nullRange
        else
          if (applyXmlFilter (isTag "OMA") (axXml anxml) ) /= []
            then
              let
                operator =
                  operatorFromXmlXN
                    ffxi
                    (AXML
                      (axAnn anxml)
                      ([head
                        $
                        applyXmlFilter
                          (getChildren .> isOperatorXml)
                          (axXml anxml)
                       ]
                      )
                    )
                terms =
                  map
                    (\n -> termFromXmlXN ffxi (AXML (axAnn anxml) [n]))
                    $
                    drop 1
                      $ -- drop out operator
                      applyXmlFilter
                        (getChildren .> isTermXml)
                        (axXml anxml) -- removed 'OrOp'
              in
                if (opName operator) == "PROJ"
                  then
                    Cast
                      (head terms)
                      (Hets.stringToId $ show (head $ tail terms))
                      Id.nullRange
                  else
                    if (opName operator) == "IfThenElse"
                      then
                        let
                          iteChildsX =
                            applyXmlFilter
                              (getChildren .> 
                                (isTag "OMS" +++ isTag "OMATTR" 
                                  +++ isTag "OMA" +++ isTag "OMV")
                              )
                              (axXml anxml)
                          iteCondX = singleitem 2 iteChildsX
                          iteThenX = singleitem 3 iteChildsX
                          iteElseX = singleitem 4 iteChildsX
                          iteCond =
                            formulaFromXmlXN
                              ffxi
                              $
                              debugGO
                                (ffxiGO ffxi)
                                "tFXXNformula"
                                ("Creating Formula for IfThenElse from : "
                                  ++ (xshow iteCondX)
                                )
                                (AXML (axAnn anxml) iteCondX)
                          iteThen = termFromXmlXN ffxi (AXML (axAnn anxml) iteThenX)
                          iteElse = termFromXmlXN ffxi (AXML (axAnn anxml) iteElseX)
                        in
                          debugGO
                            (ffxiGO ffxi)
                            "tFXXN"
                            ("IfThenElse creation...")
                            $ 
                            Conditional
                              iteThen
                              iteCond
                              iteElse
                              Id.nullRange 
                      else
                        Application operator terms Id.nullRange
            else
              if (applyXmlFilter (isTag "OMS") (axXml anxml) ) /= []
                then
                  let
                    operator = 
                      (\x -> debugGO (ffxiGO ffxi)
                        "tFXXNo"
                        ("operator : " ++ (show x))
                        x
                      )
                      $
                      operatorFromXmlXN
                        ffxi
                        anxml
                  in
                    Application operator [] Id.nullRange
                else
                    error
                      ("Impossible to create term from \"" 
                        ++ xshow (axXml anxml) ++"\""
                      ) 
                        

operatorFromXmlXN::FFXInput->AnnXMLN->OP_SYMB
operatorFromXmlXN ffxi anxml =
  let
    symbolXml = applyXmlFilter (isTag "OMS") (axXml anxml)
    sxname = xshow $ applyXmlFilter (getValue "name") symbolXml
    scd = xshow $ applyXmlFilter (getValue "cd") symbolXml
    stheoid =
      case scd of
        ('#':r) -> r
        _ -> scd
    {-
    theonode = case getNodeForTheoryName (xnTheorySet ffxi) scd of
            Nothing -> error ("No Theory for used operator! (" ++ scd ++ ")")
            (Just n) -> n
    -}
    theoxn =
      case findByName stheoid (xnTheorySet ffxi) of
        Nothing ->
          error
            ("No Theory for used operator! (\"" 
              ++ sxname ++ "\" in \"" ++ scd ++ "\" Context : \""
              ++ (take 200 $ xshow (axXml anxml)) ++ "\")"
            )
        (Just theoxn' ) -> theoxn'
    theoops = Map.findWithDefault Set.empty (xnName theoxn) (xnOpsMap ffxi) 
    opxnid = case findByName sxname (map fst $ Set.toList theoops) of
      Nothing ->
        error
          ("No such operator in Theory! (" ++ sxname ++ " in "
            ++ (show theoops) ++ ")")
      (Just opxnid' ) -> opxnid'
    opXNWON = case lookup opxnid $ Set.toList theoops of
      Nothing -> error ("Operator not found!")
      (Just oxnwon) -> oxnwon
  in
    if (stheoid==caslS) 
      then -- eventually there should be an aux. casl-theory while processing...
        Op_name
          $
          debugGO
            (ffxiGO ffxi)
            "oFXXN"
            ("creating casl operator for : " ++ sxname)
            $
            Hets.stringToId sxname
      else
        Qual_op_name
          ((\x ->
            debugGO
              (ffxiGO ffxi)
              "oFXXN"
              ("creating operator for : " ++ sxname ++ " (" ++ (show x) ++ ")")
              x
           )
           (xnWOaToa opxnid)
          )
          (Hets.cv_OpTypeToOp_type $ opTypeXNWONToOpType opXNWON)
          Id.nullRange

opName::OP_SYMB->String
opName (Op_name op) = (show op)
opName (Qual_op_name op _ _) = (show op)

-- this reads back an encapsulated node_name
idToNodeName::Id.Id->NODE_NAME
idToNodeName (Id.Id toks _ _) =
  if (length toks) < 3
    then
      error ("Malformed NODE_NAME-Id : " ++ (show toks))
    else
      (toks!!0, show (toks!!1), read (show (toks!!2)))

