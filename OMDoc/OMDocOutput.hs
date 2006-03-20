{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

  Output-methods for writing OMDoc
-}
module OMDoc.OMDocOutput
  (
     showOMDoc
    ,showOMDocDTD
    ,writeOMDoc
    ,writeOMDocDTD
    ,devGraphToOMDocCMPIOXN
    ,dGraphGToXmlGXN
		,devGraphToOMDoc
    ,writeXmlG
    ,defaultDTDURI
    ,libEnvToDGraphG
  )
  where

import qualified OMDoc.HetsInterface as Hets
import CASL.Sign
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
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
import Data.List (isPrefixOf, find)

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
        HXTT.XDTD HXTT.DOCTYPE [
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

devGraphToOMDoc::HetcatsOpts->(ASL.LIB_NAME, GlobalContext)->FilePath->IO ()
devGraphToOMDoc hco (ln, ge) file =
	devGraphToOMDocCMPIOXN
		(emptyGlobalOptions { hetsOpts = hco })
		(devGraph ge)
		(show ln)
	>>= \omdoc -> writeOMDocDTD defaultDTDURI omdoc file >> return ()
								
-- | Convert a DevGraph to OMDoc-XML with given xml:id attribute
-- will also scan used (CASL-)files for CMP-generation
devGraphToOMDocCMPIOXN::GlobalOptions->Static.DevGraph.DGraph->String->IO HXT.XmlTrees
devGraphToOMDocCMPIOXN go dg name' =
        do
                dgx <- devGraphToXmlCMPIOXmlNamed go dg
                return (
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
                nodexmlnameset = Set.fromList (onlynodexmlnamelist ++ onlyrefxmlnamelist)
                --nodenamemap = Map.fromList $ Set.toList nodenameset
                sortswomap = Hets.getSortsWOWithNodeDGNamesWO dg
                relswomap= Hets.getRelationsWOWithNodeDGNamesWOSMDGWO dg sortswomap
                predswomap = Map.map mapToSetToTupelList $ Hets.getPredMapsWOWithNodeDGNamesWO dg
                opswomap = Map.map mapToSetToTupelList $ Hets.getOpMapsWOWithNodeDGNamesWO dg
                senswomap = (\smap -> debugGO go "dGTXCMPIOXNsens" ("Sentences : " ++ (showSensWOMap smap)) smap) $ Hets.getSentencesWOWithNodeDGNamesWO dg
                importsmap = Hets.getNodeImportsNodeDGNames dg
                -- sorts
--              (xmlnamedsortswomap, xmlnames_sm) =
                (xmlnamedsortswomap, _) =
                        (processSubContents
                                (\xmlnames c -> uniqueXmlNamesContainerWONExt
                                        xmlnames
                                        show
                                        c
                                        (pSCStrip id)
                                        (\(k, swo) xname -> (k,XmlNamed swo xname))
                                )
                                xmlnames_orxnl
                                sortswomap)::(Map.Map Hets.NODE_NAMEWO (Set.Set (XmlNamed Hets.SORTWO)), XmlNameList)
                -- relations -- maybe not needed with xmlnames...
                --xmlnames_rm = xmlnames_sm
                {- xmlnamedrelswomap =
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
                        -}
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
--                              opswomap)::(Map.Map Hets.NODE_NAMEWO (Map.Map (XmlNamed Hets.IdWO) (Set.Set OpType)), XmlNameList)
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
                                -- imports/morphisms
                                timports = Map.findWithDefault Set.empty nodename importsmap
                                importsxn = Set.map
                                        (\(inodename, mmm) ->
                                                let
                                                        ((itheonum, itheoname), itheoxmlname) = case find (\x -> (snd (xnItem x)) == inodename) (Set.toList nodexmlnameset) of
                                                                Nothing -> error "Unknown Origin of Morphism!"
                                                                (Just x) -> (xnItem x, xnName x)
                                                        itheosorts = Map.findWithDefault Set.empty (Hets.mkWON itheoname itheonum) xmlnamedsortswomap
                                                        itheopreds = (Map.findWithDefault [] (Hets.mkWON itheoname itheonum) xmlnamedpredswomap)
                                                        itheoops = (Map.findWithDefault [] (Hets.mkWON itheoname itheonum) xmlnamedopswomap)
                                                        mmapandset = case mmm of
                                                                Nothing -> Nothing
                                                                -- order is sort, ops, preds, hiding...
                                                                (Just (sm,om,pm,hs)) ->
                                                                        let
                                                                                mmsorts = map (\(a,b) ->
                                                                                        (
                                                                                                case find (\i -> (xnWOaToa i) == a) (Set.toList itheosorts) of
                                                                                                        Nothing -> error ("Unable to find imported sort " ++ (show a) ++ " in source-sorts : " ++ (show itheosorts)) 
                                                                                                        (Just x) -> xnName x,
                                                                                                case find (\i -> (xnWOaToa i) == b) (Set.toList theosorts) of
                                                                                                        Nothing -> error ("Unable to find imported sort " ++ (show b) ++ " in target-sorts : " ++ (show theosorts))
                                                                                                        (Just x) -> xnName x
                                                                                        )
                                                                                        )
                                                                                        (Map.toList sm)
--                                                                              mmpreds = map (\((ai,ap), (bi,bp)) ->
                                                                                mmpreds = map (\((ai,_), (bi,_)) ->
                                                                                        (
                                                                                                case find (\(ii,_) -> (xnWOaToa ii) == ai) itheopreds of
                                                                                                        Nothing -> error ("Unable to find import predication " ++ (show ai) ++ " in source-preds : " ++ (show itheopreds)) 
                                                                                                        (Just (ii,_)) -> show $ (xnWOaToa ii), -- xnName ii,
                                                                                                case find (\(ii,_) -> (xnWOaToa ii) == bi) theopreds of
                                                                                                        Nothing -> error ("Unable to find import predication " ++ (show bi) ++ " in target-preds : " ++ (show theopreds))
                                                                                                        (Just (ii,_)) -> xnName ii
                                                                                        )
                                                                                        )
                                                                                        (Map.toList pm)
--                                                                              mmops = map (\((ai,ao), (bi,bo)) ->
                                                                                mmops = map (\((ai,_), (bi,_)) ->
                                                                                        (
                                                                                                case find (\(ii,_) -> (xnWOaToa ii) == ai) itheoops of
                                                                                                        Nothing -> error ("Unable to find import operator " ++ (show ai) ++ " in source-ops : " ++ (show itheoops))
                                                                                                        (Just (ii,_)) -> xnName ii,
                                                                                                case find (\(ii,_) -> (xnWOaToa ii) == bi) theoops of
                                                                                                        Nothing -> error ("Unable to find import operator " ++ (show bi) ++ " in target-ops : " ++ (show theoops))
                                                                                                        (Just (ii,_)) -> xnName ii
                                                                                        )
                                                                                        )
                                                                                        (Map.toList om)
                                                                        in
                                                                                Just (Map.fromList (mmsorts ++ mmpreds ++ mmops), Set.map show hs)
                                                                        
                                                in
                                                        (itheoxmlname, mmapandset)
                                        )
                                        timports
                                theopreds = Map.findWithDefault [] (Hets.mkWON nodename nodenum) xmlnamedpredswomap
                                realtheopreds = filter (\(idxnwon, _) -> (xnWOaToO idxnwon) == nodenum) theopreds
                                theoops = (\x -> debugGO go "dGTXCMPIOXNo" ("Ops in \"" ++ (show nodename) ++ "\" : " ++ show x) x) $ Map.findWithDefault [] (Hets.mkWON nodename nodenum) xmlnamedopswomap
                                realtheoops = filter (\(idxnwon, _) -> (xnWOaToO idxnwon) == nodenum) theoops
                                theosens = Map.findWithDefault Set.empty (Hets.mkWON nodename nodenum) xmlnamedsenswomap
                                realtheosens = Set.filter (\i -> (xnWOaToO i) == nodenum) theosens
                                (axiomxn, sortgenxn) = partitionSensSortGenXN (Set.toList realtheosens)
--                              (constructors, xmlnames_cons)
                                (constructors, _) = makeConstructorsXN theosorts xmlnames_senm sortgenxn
                                adtsorts = Map.keys insortmap ++ (map (\(a,_) -> xnItem a) (Map.toList constructors))
                                --theoimports = Map.findWithDefault Set.empty nodename importsmap
                                theopredsxn = map (\(k,p) -> (k, predTypeToPredTypeXNWON theosorts p)) theopreds
                                theoopsxn = map (\(k,op) -> (k, opTypeToOpTypeXNWON theosorts op)) theoops
                                sensxmlio =
                                        wrapFormulasCMPIOXN
                                                (PFInput
                                                        go
                                                        nodexmlnameset
                                                        theosorts
                                                        theopredsxn
                                                        theoopsxn
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
                                        -- I still need to find a way of modelling Hets-libraries
                                        -- in OMDoc-Imports...
--                                      (foldl (\x' (nodename' , mmm) ->
                                        (foldl (\x' (nodenamex , mmm) ->
                                                let
                                                        --nodenamex = case Set.toList $ Set.filter (\i -> (snd (xnItem i)) == nodename' ) nodexmlnameset of
                                                        --      [] -> error "Import from Unknown node..."
                                                        --      (l:_) -> xnName l
                                                in
                                                        x' +++
                                                        HXT.etag "imports" += (
                                                                (HXT.sattr "from" ("#" ++ nodenamex)) +++
                                                                (
                                                                        case mmm of
{-                                                                              (Just mm) ->
                                                                                        morphismMapToXml mm nodenamex theoname
                                                                                        morphismMapToXml mm nodenamex theoname -}
                                                                                (Just (sm, hs)) -> morphismMapToXmlXN sm hs nodenamex theoname
                                                                                Nothing -> HXT.txt ""
                                                                )
                                                                ) +++
                                                        xmlNL
                                                ) (HXT.txt "") (Set.toList importsxn) --(Set.toList theoimports)
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
                                                (HXT.txt "")
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
                                                (HXT.txt "")
                                                realtheoops
                                        ) +++
                                        -- sentences
                                        sensxml
                                        )
                                        -- this constructs Hets-internal links as private data (but uses xmlnames for reference)
                                        +++ xmlNL +++ (inDGToXmlXN dg nodenum nodexmlnameset) +++ xmlNL
                                        )
                                        -- when constructing the catalogues a reference to the xmlname used in _this_ document is used
                                        -- it is very likely possible, that this theory has another name in real life (unless there are no name-collisions)
                        ) (return $ refsToCatalogueXN dg nodexmlnameset +++ xmlNL) onlynodexmlnamelist 
                                
        where
        nodeTupelToNodeName::(a, NODE_NAME)->String
        nodeTupelToNodeName = nodeToNodeName . snd
        
        nodeToNodeName::NODE_NAME->String
        nodeToNodeName = (\nn ->
                                                        let
                                                                nodename = showName nn
                                                        in
                                                                if (length nodename) == 0
                                                                        then
                                                                                "AnonNode_"
                                                                        else
                                                                                nodename
                                                        )
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
                                ) (HXT.txt "") refs
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
                        ) (HXT.txt "") $ Set.toList ss)
                        +++ xmlNL
                        ) +++ xmlNL
                )
        )
        
createAllConstructorsXN::TheoryXNSet->[(XmlNamedWON Id.Id, Set.Set OpTypeXNWON)]->HXT.XmlFilter
createAllConstructorsXN theoryset cs = foldl (\cx c ->  
        cx +++ createConstructorsXN theoryset c +++ xmlNL ) (HXT.txt "") cs
                
createConstructorsXN::TheoryXNSet->(XmlNamedWON Id.Id, Set.Set OpTypeXNWON)->HXT.XmlFilter
createConstructorsXN theoryset (cidxn, opxnset) = foldl (\cx opxn -> cx +++ createConstructorXN theoryset cidxn opxn +++ xmlNL) (HXT.txt "") $ Set.toList opxnset
                
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
                        ) (HXT.txt "") opargsxn
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
                                                ) (HXT.txt "") predArgsXN )
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
-- NAME -> ID
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
                                                ) (HXT.txt "") opArgsXN )
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
        HXT.etag "morphism" += (
                (HXT.sattr "hiding" (implode " " $ Set.toList hidings))
                +++
                (foldl
                        (\sx (ss, st) -> 
                                sx +++
                                        requation
                                                (inOMOBJ (HXT.etag "OMS" += (HXT.sattr "cd" source +++ HXT.sattr "name" ss)))
                                                (inOMOBJ (HXT.etag "OMS" += (HXT.sattr "cd" target +++ HXT.sattr "name" st)))
                        )
                        (HXT.txt "")
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
                                        HXT.txt "") +++
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
                                        ) (HXT.txt "") $ Map.toList funmap)
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
                                        ) (HXT.txt "") $ Map.toList predmap)
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
                
-- | creates constructors from a list of 'CASLFORMULA's (see : 'partitionSensSortGen')
makeConstructorsXN::Set.Set XmlNamedWONSORT->XmlNameList->[XmlNamedWON (Ann.Named CASLFORMULA)]->(Map.Map (XmlNamedWON Id.Id) (Map.Map (XmlNamedWON Id.Id) (Set.Set OpTypeXNWON)), XmlNameList)
makeConstructorsXN sortxnwoset xmlnames sortgenaxxnlist =
        foldl (\(mapping, xmlnames' ) sortgenaxxn ->
                let
                        (conidxnwo, conmap, xmlnames'' ) =
                                makeConstructorMapXN sortxnwoset xmlnames' sortgenaxxn
                in
                        (Map.insertWith (\a b -> Map.union a b) conidxnwo conmap mapping, xmlnames'' )
                        ) (Map.empty, xmlnames) sortgenaxxnlist
                                        
-- | creates constructors from a 'CASLFORMULA'
makeConstructorMapXN::Set.Set XmlNamedWONSORT->XmlNameList->XmlNamedWON (Ann.Named CASLFORMULA)->(XmlNamedWON Id.Id, (Map.Map (XmlNamedWON Id.Id) (Set.Set OpTypeXNWON)), XmlNameList)
makeConstructorMapXN sortxnwoset xmlnames sensxnwo =
        let
                sens = xnWOaToa sensxnwo
                (Ann.NamedSen senname _ _ (Sort_gen_ax cons _)) = sens
                origin = xnWOaToO sensxnwo
                sort = (drop (length "ga_generated_") senname)
                sortxn = case sortToXmlNamedWONSORT (Set.toList sortxnwoset) (Hets.stringToId sort) of
                        Nothing -> error ("Cannot find sort to make constructor for! (No \"" ++ sort ++ "\" in " ++ (show sortxnwoset) ++ ")")
                        (Just sortxn' ) -> sortxn'
                (constructormap, xmlnames' ) =
                        foldl(\(cmap, xmlnames'' ) (Constraint _ symbs _) ->
                                foldl (\(tcmap, xmlnames''' ) (Qual_op_name name' ot _) ->
                                        let
                                                opxmlname = createUniqueName xmlnames''' (adjustStringForXmlName (show name' ))
                                        in
                                                (Map.insertWith (Set.union) (XmlNamed (Hets.mkWON name' origin) opxmlname) (Set.singleton (opTypeToOpTypeXNWON sortxnwoset (cv_Op_typeToOpType ot))) tcmap, xmlnames''' )
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
        if length inLinks == 0 then HXT.txt "" else
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
        if length inLinks == 0 then HXT.txt "" else
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

unwrapLinkSource::ASL.LIB_NAME->String
unwrapLinkSource
        (ASL.Lib_id (ASL.Indirect_link src _)) = src
unwrapLinkSource _ = error "Wrong application of unwrapLinkSource!"
                
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
                        _ -> joinWith '.' $ init filenameparts 
        
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
                                _ -> ( joinWith '.' $ init filenameparts, Just (last filenameparts)) 
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

fileSandbox::String->String->String
fileSandbox [] file = file
fileSandbox sb file =
        sb ++ "/" ++ case head file of
                '/' -> tail file
                _ -> file

-- | writes an XmlTrees-Graph to disk relative to a given directory
-- will create directory-structures from libnames
writeXmlG::String->(ImportGraph (HXT.XmlTrees))->String->IO ()
writeXmlG dtduri ig sandbox =
        let
                nodes = map snd $ Graph.labNodes ig
        in
                (mapM (\(S (name' ,file) x) ->
                        let
                                omfile = fileSandbox sandbox $ asOMDocFile file
                        in
                                putStrLn ("Writing \"" ++ name' ++ "\" to \"" ++ omfile ++ "\"") >>
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
                                importswithproofsteps = applyXmlFilter (getChildren .> (isTag "axiom-inclusion" +++ isTag "theory-inclusion")) t
                                proofsteps = applyXmlFilter (getChildren .> isTag "proof-object") t
                          in
                            foldl (\newdg importx ->
                                        let     isLocalThm = applyXmlFilter (isTag "axiom-inclusion") [importx] /= []
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
validImports = (isTag "imports" +++ isTag "axiom-inclusion" +++ isTag "theory-inclusion")

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
                return $ foldl (\wrapped f -> wrapped +++ (wrapFormulaCMPXN pfinput f poslinemap) ) (HXT.txt "") fs
                
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
                        [       (axiomNameXMLNS,
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
                        ,theoryPreds::[(XmlNamedWONId, PredTypeXNWON)]
                        ,theoryOps::[(XmlNamedWONId, OpTypeXNWON)]
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
                        (createSymbolForPredicationXN (theorySet pfinput) (theoryPreds pfinput) p) +++
                        (foldl (\term t ->
                                term +++
                                (processTermXN pfinput t) +++
                                xmlNL
                                ) (HXT.txt "") tl
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
    TheoryXNSet
    -> [(XmlNamedWONId, PredTypeXNWON)]
    -> PRED_SYMB -- ^ the predication to process
    -> (HXT.XmlTree -> HXT.XmlTrees) 
         -- ^ a xml-representation of the predication
-- Pred_name
createSymbolForPredicationXN theoryset theorypreds
        (Pred_name pr) =
                let
                        (xnpid, _) = case find (\(xnpid' , _) ->
                                (xnWOaToa xnpid' ) == pr ) theorypreds of 
                                        Nothing -> error "Cannot find Spredicate in theory!"
                                        (Just x' ) -> x'
                in
                        HXT.etag "OMS" += 
                                (HXT.sattr "cd" (fromMaybe "unknown" $
                                        getTheoryXmlName theoryset (xnWOaToO xnpid)) +++
                                HXT.sattr "name" (xnName xnpid)
                                )
-- Qual_pred_name
createSymbolForPredicationXN theoryset theorypreds
        (Qual_pred_name pr pt _) =
                let
                        (xnpid, _) = case find (\(xnpid' , xnpt' ) ->
                                (xnWOaToa xnpid' ) == pr &&
                                (cv_PredTypeToPred_type $ predTypeXNWONToPredType xnpt' ) == pt ) theorypreds of
                                        Nothing -> error ("Cannot find Qpredicate in theory!" ++ "(" ++ (show pr) ++ ", " ++ (show theorypreds) ++ ")")
                                        (Just x' ) -> x'
                in
                        HXT.etag "OMS" +=
                                ( HXT.sattr "cd" ( fromMaybe "unknown" $
                                        getTheoryXmlName theoryset (xnWOaToO xnpid)
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
processConstraintsXN _ [] = HXT.txt ""
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
                                ) (HXT.txt "") ops'
                        ) )
                +++ xmlNL
                +++ (HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" (show origs))))) +++ xmlNL

-- first newline needs pulling up because we have a list of lists...
processVarDeclXN :: TheoryXNSet -> Set.Set XmlNamedWONSORT -> [VAR_DECL] -> (HXT.XmlTree->HXT.XmlTrees)
processVarDeclXN theoryset theorysorts vdl =
        (HXT.etag "OMBVAR" += (xmlNL +++ (processVarDecls theoryset theorysorts vdl)) ) +++ xmlNL
        where
        processVarDecls :: TheoryXNSet -> Set.Set XmlNamedWONSORT -> [VAR_DECL] -> (HXT.XmlTree->HXT.XmlTrees)
        processVarDecls _ _ [] = HXT.txt ""
        processVarDecls theoryset' theorysorts' ((Var_decl vl s _):vdl' ) = (foldl (\decls vd -> decls +++
        -- <ombattr><omatp><oms>+</omatp><omv></ombattr>
                ( createTypedVarXN theoryset theorysorts' s (show vd) )
                        +++ xmlNL)
                        (HXT.txt "") vl ) -- end fold
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
                                                ) (HXT.txt "") termlist
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
                                case find
                                                (\(xnid, _) -> (xnWOaToa xnid) == op)
                                                (theoryOps pfinput)     of
                                                        Nothing -> error ("Operator is unknown! (" ++ (show op) ++ " in "++ (show (theoryOps pfinput)) ++")")
                                                        (Just x' ) -> x'
                in
                        HXT.etag "OMS" +=
                                (HXT.sattr "cd" 
                                        (fromMaybe "unknown" $
                                                getTheoryXmlName (theorySet pfinput) (xnWOaToO xnopid)) +++
                                        HXT.sattr "name" (xnName xnopid)
                                )
-- Qual_op_name
processOperatorXN pfinput
        (Qual_op_name op ot _) =
                let
                        (xnopid, _) =
                                case find
                                        (\(xnid, xnopt) ->
                                                (xnWOaToa xnid) == op
                                                && (cv_OpTypeToOp_type $ opTypeXNWONToOpType xnopt) == ot
                                        )
                                        (theoryOps pfinput) of
                                                Nothing -> error ("Operator is unknown! (" ++ (show op) ++ "("++ (show ot) ++ ") in "++ (show (theoryOps pfinput)) ++")")
                                                (Just x' ) -> x' 
                in
                        HXT.etag "OMS" +=
                                ( HXT.sattr "cd"
                                        ( fromMaybe "unknown" $
                                                getTheoryXmlName (theorySet pfinput) (xnWOaToO xnopid)
                                        ) +++
                                        HXT.sattr "name" (xnName xnopid)
                                )

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
