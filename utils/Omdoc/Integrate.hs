{- |
	The Integrate-Module aims at glueing together all needed modules
	for /Hets\<-\>Omdoc/-conversion.
-}
module Integrate where

import qualified HetsInterface as Hets
--import OmdocHXT
import OmdocDevGraph hiding (run)
import CASL.Sign
import CASL.Morphism
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import qualified Common.Id as Id
import qualified Syntax.AS_Library as ASL
import qualified CASL.AS_Basic_CASL as ABC

import qualified Data.Dynamic as Dyn
import qualified Common.Lib.Map as Map

import Static.DevGraph
--import qualified Graph as Graph
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Graph.Inductive.Tree as Tree
import qualified Logic.Grothendieck as Logic.Grothendieck
import CASL.Amalgamability(CASLSign)

import qualified Text.XML.HXT.Parser as HXT hiding (run)
import qualified Text.XML.HXT.DOM.XmlTreeTypes as HXTT

import qualified Comorphisms.CASL2PCFOL as Com

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import qualified Common.AS_Annotation as Ann

import qualified Logic.Logic as Logic

import Data.Maybe (fromMaybe)
import Data.List (nub, isPrefixOf, isSuffixOf)

import qualified Data.Typeable as Data.Typeable

import qualified Common.GlobalAnnotations as GA

import qualified Driver.Options as DOptions

import System.IO.Unsafe
import Control.Exception
import Debug.Trace (trace)

import Common.Utils (joinWith)

import qualified System.IO.Error as System.IO.Error
import qualified System.Directory as System.Directory

data ImportContext a = ImportContext {
						 importsMap :: Hets.ImportsMap
						,sortsMap :: Hets.SortsMap
						,relsMap :: Hets.RelsMap
						,predsMap :: Hets.PredsMap
						,opsMap :: Hets.OpsMap
						,sensMap :: Hets.SensMap
						,importGraph :: (ImportGraph a)
						}
						

theoryNameXMLNS
	,theoryNameXMLAttr :: String
theoryNameXMLNS = "xml"
theoryNameXMLAttr = "id"
						
sortNameXMLNS
	,sortNameXMLAttr :: String
sortNameXMLNS = "xml"
sortNameXMLAttr = "id"

predNameXMLNS
	,predNameXMLAttr :: String
predNameXMLNS = "xml"
predNameXMLAttr = "id"

opNameXMLNS
	,opNameXMLAttr :: String
opNameXMLNS = "xml"
opNameXMLAttr = "id"

-- | generate a DOCTYPE-Element for output
mkOmdocTypeElem::
	String -- ^ URI for DTD
	->HXTT.XNode -- ^ DOCTYPE-Element
mkOmdocTypeElem system =
	HXTT.XDTD HXTT.DOCTYPE [
		 (a_name, "omdoc")
		,(k_public, "-//OMDoc//DTD OMDoc V1.1//EN")
		,(k_system, system)
		]

-- | generate DOCTYPE-Element with \"omdoc.dtd\" as DTD-URI 
omdocDocTypeElem::HXTT.XNode
omdocDocTypeElem = mkOmdocTypeElem "omdoc.dtd"

-- | this function wraps trees into a form that can be written by HXT
writeableTrees::XmlTrees->XmlTree
writeableTrees t =
		(NTree
			((\(NTree a _) -> a) emptyRoot)
			((NTree omdocDocTypeElem [])
				:(NTree (XText "\n")[])
				:t)
			
		)
		
-- | this function shows Xml with indention
showOmdoc::XmlTrees->IO XmlTrees
showOmdoc t = HXT.run' $
	HXT.writeDocument
		[(a_indent, v_1), (a_issue_errors, v_1)] $
		writeableTrees t

-- | this function writes Xml with indention to a file
writeOmdoc::XmlTrees->String->IO XmlTrees
writeOmdoc t f = HXT.run' $
	HXT.writeDocument
		[(a_indent, v_1), (a_output_file, f)] $
		writeableTrees t

loadOmdoc::String->IO (Either IOError XmlTrees)
loadOmdoc f =
	do
		tree <- (
			HXT.run' $
			HXT.parseDocument
				[
					(a_source, f),
					(a_validate, v_0),
					(a_issue_errors, v_0),
					(a_process_dtd, v_0)
				]
				emptyRoot
			)
		status <- return ( ( read $ xshow $ applyXmlFilter (getValue "status") tree) :: Int )
		if status <= HXT.c_err
			then
				return (Right (applyXmlFilter (getChildren .> isTag "omdoc") tree ))
			else
				return (Left $ System.IO.Error.mkIOError System.IO.Error.userErrorType ("Error reading \"" ++ f ++ "\"...") Nothing (Just f))
		
-- | some operations to get CASL-Signs
getCASLSignFromDG::Static.DevGraph.DGraph->CASL.Amalgamability.CASLSign
getCASLSignFromDG dg =
	let (Just caslsign) = Hets.getCASLSign $ Hets.getFirstNodeSign dg
	in caslsign

getCASLSignF::FilePath->IO CASL.Amalgamability.CASLSign
getCASLSignF s = do Hets.getDG s >>= \dg -> return $ getCASLSignFromDG $ dg 

-- | Convert a DevGraph to OMDoc-XML with given xml:id attribute
devGraphToOmdoc::Static.DevGraph.DGraph->String->HXT.XmlTrees
devGraphToOmdoc dg name = (HXT.etag "omdoc" += ( qualattr "xml" "id" name
				+++ xmlNL +++ devGraphToXml dg )) emptyRoot

-- | Convert a DevGraph to an XML-Representation (without omdoc parent)				
devGraphToXml::Static.DevGraph.DGraph->(HXT.XmlTree->HXT.XmlTrees)
devGraphToXml dg =
		let
			(onlynodenameset, onlyrefnameset) = Hets.getNodeNamesNodeRef dg
			nodenameset = Set.union onlynodenameset onlyrefnameset
			nodenamemap = Map.fromList $ Set.toList nodenameset
			namenodemap = Map.fromList $ map (\(a,b) -> (b,a)) $ Map.toList nodenamemap
			nodenames = Set.fromList $ map (\(_,a) -> a) $ Set.toList nodenameset
			sorts = Hets.getSortsWithNodeNames dg
			rels = Hets.getRelationsWithNodeNames dg
			preds = Hets.getPredMapsWithNodeNames dg
			ops = Hets.getOpMapsWithNodeNames dg
			sens = Hets.getSentencesWithNodeNames dg
			mimports = Hets.getNodeImportsNodeNames dg
			imports = Map.map (Set.map fst) mimports
		in
		    foldl (\dgx (node, name) ->
		    	let
					nSorts = fromMaybe Set.empty $ Map.lookup name sorts 
					-- OMDocS 'insort' is opposite to CASL-Sort-Relation 
					nInsorts = Rel.transpose $ fromMaybe Rel.empty $ Map.lookup name rels
					nInsortMap = foldl (\m (a,b) -> 
						Map.insert a (Set.insert b (Map.findWithDefault Set.empty a m)) m
						) Map.empty $ Rel.toList nInsorts
					nPreds = fromMaybe Map.empty $ Map.lookup name preds  
					nOps = fromMaybe Map.empty $ Map.lookup name ops
					nSens = fromMaybe Set.empty $ Map.lookup name sens
					(axioms, sortgen) = partitionSensSortGen $ Set.toList nSens
					constructors = makeConstructors sortgen
					
					-- sort-imports (not all imports)
					nImports = fromMaybe Set.empty $ Map.lookup name mimports
					-- what adts are needed (insort, cons or both)
					adtsorts = nub $ (map (\ (a,_) -> a) $ Map.toList nInsortMap) ++
						(map (\(a,_) -> a) $ Map.toList constructors)
					(realSorts, realOps, realPreds) = foldl (\(rs, ro, rp) (_,mmm) ->
						case mmm of
							Nothing -> (rs, ro, rp)
							(Just mm) -> (Hets.removeMorphismSorts mm rs,
								Hets.removeMorphismOps mm ro,
								Hets.removeMorphismPreds mm rp)
							) (nSorts, nOps, nPreds) $ Set.toList nImports
				in
					dgx +++
					(HXT.etag "theory" += (qualattr "xml" "id" name))
					+= (
					   (foldl (\ix (i,_) -> ix +++ xmlNL +++ importToXml i += (xmlNL +++
					   -- morphism-generation-hack ... ugly. needs more work.
						(caslMorphismToXml mimports sorts preds ops i name $
							Hets.getCASLMorph $ head $
							( \e ->
								let
									thisnode = Map.findWithDefault (error $ "No such node N " ++ name) name namenodemap
									inode = Map.findWithDefault (error $ "No such node I " ++ i) i namenodemap
								in
									filter (\(n,m,_) -> n == inode && m == thisnode) e
							)
							(Graph.labEdges dg)
							)) +++ xmlNL 
						) (HXT.txt "") $ Set.toList nImports)
					   +++
					   (foldl (\sx s -> sx +++ xmlNL +++ sortToXml s) (HXT.txt "") $ Set.toList realSorts) --nSorts)
					   +++
					   -- adt-generation needs some optimization...
					   (foldl (\adtx sort -> adtx +++ xmlNL
						+++ (
							let 	sortrelation = (\a -> (sort, a)) $ fromMaybe Set.empty $ lookup sort $ Map.toList nInsortMap
								cons = createAllConstructors $ Map.toList $ Map.findWithDefault Map.empty sort constructors
							in
								createADT sortrelation cons
							)
						) (HXT.txt "") adtsorts)
					   +++
					   (foldl (\px p -> px +++ xmlNL +++ predicationToXml mimports sorts name p)
						(HXT.txt "") $ Map.toList realPreds) --nPreds)
					   +++
					   (foldl (\px o -> px +++ xmlNL +++ operatorToXml mimports sorts name o)
						(HXT.txt "") $ Map.toList realOps) --nOps)
					   +++
					   (wrapFormulas mimports sorts preds ops name $ Set.toList nSens)
					   +++ xmlNL
					   )
					+++ xmlNL
					-- make private data for all incoming links
					+++ inDGToXml dg node nodenamemap 
					+++ xmlNL
				) (refsToCatalogue dg +++ xmlNL) $ Set.toList onlynodenameset
				
adjustLOCOmdoc::String->String
adjustLOCOmdoc s =
	let
		woExt = reverse $ takeWhile (/='.') $ reverse s
	in
		if woExt == ""
			then
				s ++ ".omdoc"
			else
				woExt ++ ".omdoc"

refsToCatalogue::DGraph->HXT.XmlFilter
refsToCatalogue dg =
	let refs = filter isDGRef $ map snd $ Graph.labNodes dg
	in
		HXT.etag "catalogue" += 
		(
		xmlNL +++
		foldl (\cx r ->
			cx +++
			HXT.etag "loc" +=
				( HXT.sattr "theory" (getDGNodeName r) +++ HXT.sattr "omdoc" (adjustLOCOmdoc (show $ dgn_libname r)) ) +++
				xmlNL
				) (HXT.txt "") refs
		)
		
-- | newline in XML
xmlNL::(HXT.XmlTree->HXT.XmlTrees)
xmlNL = HXT.txt "\n"

-- | create an imports-tag for a given source
importToXml::String->(HXT.XmlTree->HXT.XmlTrees)
importToXml i = HXT.etag "imports" += (HXT.sattr "from" ("#"++i))

-- | create a xml-representation for a SORT
sortToXml::SORT->(HXT.XmlTree->HXT.XmlTrees)
-- NAME -> ID
sortToXml s = HXT.etag "symbol" += ( HXT.sattr "kind" "sort" +++ qualattr "xml" "id" (show s) )

-- | create an ADT for a SORT-Relation and constructor information (in xml)
createADT::(SORT, Set.Set SORT)->HXT.XmlFilter->HXT.XmlFilter
createADT (s,ss) constructors =
	HXT.etag "adt" += (qualattr "xml" "id" ((show s)++"-adt")) 
	+= (
	    xmlNL +++
	    (HXT.etag "sortdef" += (HXT.sattr "name" (show s) +++ HXT.sattr "type" "free") )
	    +++
	    constructors
	    +++
	    (foldl (\isx is ->
	    	isx +++ xmlNL +++ (HXT.etag "insort" += (HXT.sattr "for" ("#"++(show is))))
	    ) (HXT.txt "") $ Set.toList ss)
	    +++ xmlNL
	)

-- | creates a xml-representation for a list of constructors	
createAllConstructors::[(Id.Id, Set.Set OpType)]->HXT.XmlFilter
createAllConstructors cs = foldl (\cx c ->
	cx +++ createConstructors c +++ xmlNL ) (HXT.txt "") cs 
	
-- | creates a xml-representation for all types of a constructor
createConstructors::(Id.Id, Set.Set OpType)->HXT.XmlFilter
createConstructors (cid, opset) = foldl (\cx op -> cx +++ createConstructor cid op +++ xmlNL) (HXT.txt "") $ Set.toList opset
	
-- | create a xml-representation for one type of a constructor
createConstructor::Id.Id->OpType->HXT.XmlFilter
createConstructor cid (OpType fk args res) =
	HXT.etag "constructor" += (
		HXT.sattr "name" (show cid) +++
		xmlNL +++
		foldl (\argx arg ->
			argx +++ xmlNL +++
			(HXT.etag "argument" += (HXT.sattr "sort" (show arg)))
			) (HXT.txt "") args
		)
		
initOrEmpty::[a]->[a]
initOrEmpty [] = []
initOrEmpty l = init l

extractConsFromADT::HXT.XmlTrees->(Id.Id, [(Id.Id, OpType)])
extractConsFromADT t =
	let
		sort = Hets.stringToId $ reverse $ drop (length "-adt") $ reverse $
				xshow $ applyXmlFilter (isTag "adt" .> getQualValue "xml" "id") t
		cons = applyXmlFilter (getChildren .> isTag "constructor") t
	in
		(sort, map (\t -> extractCon [t] sort) cons)
		
	where
		extractCon::HXT.XmlTrees->Id.Id->(Id.Id, OpType) -- empty list on error
		extractCon t sort =
			let
				name = xshow $ applyXmlFilter (getValue "name") t
				args = map (\t -> Hets.stringToId $ xshow [t]) $ applyXmlFilter (getChildren .> isTag "argument" .> getValue "sort") t
			in
				(Hets.stringToId name, OpType Total args sort)
				
consToSens::Id.Id->[(Id.Id, OpType)]->(Ann.Named CASLFORMULA)
consToSens sort conlist =
	Ann.NamedSen
		("ga_generated_" ++ show sort)
		True
		(Sort_gen_ax
			(
			foldl (\constraints (id, ot) ->
				constraints ++
				[ Constraint
					sort
					[(Qual_op_name id (cv_OpTypeToOp_type ot) Id.nullRange , [0])] 
					sort
				]
				) [] conlist
			)
			True
		)
	
-- | creates a xml-representation for a predication
-- needs a map of imports, sorts, the name of the current theory and the predication
predicationToXml::Hets.ImportsMap->Hets.SortsMap->String->(Id.Id, (Set.Set PredType))->(HXT.XmlTree->HXT.XmlTrees)
predicationToXml imports sorts name (predId, ptSet) =
-- NAME -> ID
	(HXT.etag "symbol" += (qualattr predNameXMLNS predNameXMLAttr (show predId) +++ HXT.sattr "kind" "object"))
	+= ( 
		foldl (\tx (PredType predArgs) ->
		tx +++ xmlNL
		+++
		(HXT.etag "type" += (HXT.sattr "system" "casl"))
		+= (	xmlNL +++
			HXT.etag "OMOBJ"
			+= (
				xmlNL +++
				HXT.etag "OMA"
				+= (
					xmlNL +++
					(HXT.etag "OMS" += (HXT.sattr "cd" "casl" +++ HXT.sattr "name" "predication" ))
					+++
					(foldl (\px s ->
						px +++ xmlNL
						+++
						(HXT.etag "OMS" += (HXT.sattr "cd" (fromMaybe "unknownOrigin" (Hets.findNodeNameForSort imports sorts s name)) +++ HXT.sattr "name" (show s)))
						) (HXT.txt "") predArgs)
					+++ xmlNL
				)
				+++ xmlNL
			)
			+++ xmlNL
		)
		+++ xmlNL
		) (HXT.txt "") $ Set.toList ptSet
	)
	
-- | creates a xml-representation for an operator
-- needs a map of imports, sorts, the name of the current theory and the operator
operatorToXml::Hets.ImportsMap->Hets.SortsMap->String->(Id.Id, (Set.Set OpType))->(HXT.XmlTree->HXT.XmlTrees)
operatorToXml imports sorts name (opId, otSet) =
-- NAME -> ID
	(HXT.etag "symbol" += (qualattr opNameXMLNS opNameXMLAttr (show opId) +++ HXT.sattr "kind" "object"))
	+= ( 
		foldl (\tx (OpType fk opArgs opRes) ->
		tx +++ xmlNL
		+++
		(HXT.etag "type" += (HXT.sattr "system" "casl"))
		+= (	xmlNL +++
			HXT.etag "OMOBJ"
			+= (
				xmlNL +++
				HXT.etag "OMA"
				+= (
					xmlNL +++
					(HXT.etag "OMS" += (HXT.sattr "cd" "casl" +++ HXT.sattr "name" (if fk==Total then "function" else "partial-function") ))
					+++
					(foldl (\px s ->
						px +++ xmlNL
						+++
						createSymbolForSort imports sorts s name
						) (HXT.txt "") opArgs)
					+++ xmlNL +++
					createSymbolForSort imports sorts opRes name
					+++ xmlNL
				)
				+++ xmlNL
			)
			+++ xmlNL
		)
		+++ xmlNL
		) (HXT.txt "") $ Set.toList otSet
	)
	
sortToOM::Hets.ImportsMap->Hets.SortsMap->String->SORT->HXT.XmlFilter
sortToOM imports sorts name s =
	HXT.etag "OMS" +=
		(
		HXT.sattr "cd" (fromMaybe "unknown" $ Hets.findNodeNameForSort imports sorts s name) +++
		HXT.sattr "name" (show s)
		)
		
opToOM::Hets.ImportsMap->Hets.OpsMap->String->Id.Id->HXT.XmlFilter
opToOM imports ops name id =
	HXT.etag "OMS" +=
		(
		HXT.sattr "cd" (fromMaybe "unknown" $ Hets.findNodeNameForOperator imports ops id name) +++
		HXT.sattr "name" (show id)
		)
	
inOMOBJ::HXT.XmlFilter->(HXT.XmlTree->HXT.XmlTrees)
inOMOBJ x = HXT.etag "OMOBJ" += x

transformMorphOp::(Id.Id, OpType)->OP_SYMB
transformMorphOp (id, ot) = Qual_op_name id (cv_OpTypeToOp_type ot) Id.nullRange

transformMorphPred::(Id.Id, PredType)->PRED_SYMB
transformMorphPred (id, pt) = Qual_pred_name id (cv_PredTypeToPred_type pt) Id.nullRange

createHidingString::CASLSign->String
createHidingString (Sign sortset _ opmap _ predmap _ _ _ _) =
	let hidden = map show (Set.toList sortset) ++
			 map show (Map.keys opmap) ++
			 map show (Map.keys predmap)
	in	joinWith ',' hidden
	
createHidingString2::(Hets.Sorts, Hets.Rels, Hets.Preds, Hets.Ops)->String
createHidingString2 (sorts, rels, preds, ops) =
	let	hidden = map show (Set.toList sorts) ++
			map show (Map.keys preds) ++
			map show (Map.keys ops)
	in	joinWith ',' hidden
	


caslMorphismToXml::Hets.ImportsMap->Hets.SortsMap->Hets.PredsMap->Hets.OpsMap->String->String->(CASL.Morphism.Morphism () () ())->HXT.XmlFilter
caslMorphismToXml imports sorts preds ops sourcename targetname (CASL.Morphism.Morphism ssource starget sortmap funmap predmap _) =
	let
		hides = createHidingString $ diffSig ssource starget
{-		hides = createHidingString2 $ (\(a,b,c,d,_) -> (a,b,c,d)) $
			Hets.diffMaps
				(Hets.lookupMaps sorts Map.empty preds ops Map.empty sourcename)
				(Hets.lookupMaps sorts Map.empty preds ops Map.empty targetname) -}
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
							(inOMOBJ $ sortToOM imports sorts sourcename ss)
							)
						 +++
						HXT.etag "value" +=
							(
							xmlNL +++
							(inOMOBJ $ sortToOM imports sorts targetname st)
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
									imports
									ops
									sourcename
		-- using a qualified OP_SYMB does not work correctly.
		-- for example the reference to Sample/Simple in 
		-- Advancend/Architectural has a morphism with a
		-- Partial Operator while the Operator is defined as Total...
		--							(transformMorphOp
		--								(ids, ots)
		-- workaround :
		-- try both variants for function kind...
								(
									let	op = transformMorphOp (ids, ots)
										-- get cd for original optype
										cd = Hets.findNodeNameForOperatorWithSorts
												imports
												ops
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
												imports
												ops
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
							( let	otset = Set.filter (\(OpType fk _ _) -> fk == fkt) $
										Map.findWithDefault Set.empty idt $
											Map.findWithDefault Map.empty targetname ops
								ott = if Set.null otset
									then
										error "Cannot find Operator for Morphism..."
									else
										head $ Set.toList otset
							  in 
								inOMOBJ $
									processOperator
										imports
										ops
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
								createSymbolForPredication imports preds sourcename
									(transformMorphPred (ids, pts))
							) +++
						HXT.etag "value" +=
							( let	ptset = Map.findWithDefault Set.empty idt $
										Map.findWithDefault Map.empty targetname preds
							
								ptt = if Set.null ptset
										then
											error "Cannot find Predication for Morphism..."
										else
											head $ Set.toList ptset
							  in
								inOMOBJ $
									createSymbolForPredication imports preds targetname
										(transformMorphPred (idt, ptt))
							) +++
						xmlNL
						)
					+++ xmlNL
					) (HXT.txt "") $ Map.toList predmap)
				)
			in
				morphx -- maybe some postprocessing ?
	

processXmlMorphism::
	Hets.ImportsMap->
	Hets.SortsMap->
	Hets.PredsMap->
	Hets.OpsMap->
	String->
	String->
	HXT.XmlTrees->
	(
		Hets.ImportsMap,
		Hets.SortsMap,
		Hets.PredsMap,
		Hets.OpsMap,
		(Morphism () () ())
	)
processXmlMorphism
	imports
	sorts
	preds
	ops
	sourcename
	targetname
	t
	=
		let
			sourcesorts = Map.findWithDefault Set.empty sourcename sorts
			targetsorts = Map.findWithDefault Set.empty targetname sorts
			hides = xshow $ applyXmlFilter (isTag "morphism" .> getQualValue "" "hiding") t
			pattern = isTag "requation" .> getChildren .> isTag "pattern"
			value = isTag "requation" .> getChildren .> isTag "value"
			vsymbol = value .> getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMS" .> getQualValue "" "name" 
			requations = applyXmlFilter (isTag "morphism" .> getChildren .> isTag "requation") t
			newSymbolsSet = foldl (\ns ts ->
				case applyXmlFilter (value .> getChildren .> isTag "OMATTR") [ts] of
					[] ->	let
								symbolname = xshow $ applyXmlFilter vsymbol [ts]
							in
								if symbolname /= [] then
									Set.union ns (Set.singleton (Hets.stringToId $ symbolname))
									else
									ns
					_ -> ns
					) Set.empty requations
			newOpsMap = foldl (\np tp ->
				case xshow $ applyXmlFilter (
					pattern .> getChildren .> 
					isTag "OMOBJ" .> getChildren .>
					isTag "OMATTR" .> getChildren .>
					isTag "OMATP" .> getChildren .>
					isTag "OMS" .> withSValue "cd" "casl" .> withSValue "name" "funtype" .> getQualValue "" "name") [tp] of
					"funtype" ->
						let	satp = applyXmlFilter (
								pattern .> getChildren .>
								isTag "OMOBJ" .> getChildren .>
								isTag "OMATTR" .> getChildren .>
								isTag "OMATP") [tp]
							tatp = applyXmlFilter (
								value .> getChildren .>
								isTag "OMOBJ" .> getChildren .>
								isTag "OMATTR" .> getChildren .>
								isTag "OMATP") [tp]
							satpsym = applyXmlFilter (getChildren .> isTag "OMS") satp
							satpstr = applyXmlFilter (getChildren .> isTag "OMSTR") satp
							satpmap = Map.fromList $ zip
								(map (\t -> xshow $ applyXmlFilter (getQualValue "" "name") [t]) satpsym)
								(map (\t -> xshow $ applyXmlFilter (getChildren) [t]) satpstr) 
							tatpsym = applyXmlFilter (getChildren .> isTag "OMS") tatp
							tatpstr = applyXmlFilter (getChildren .> isTag "OMSTR") tatp
							tatpmap = Map.fromList $ zip
								(map (\t -> xshow $ applyXmlFilter (getQualValue "" "name") [t]) tatpsym)
								(map (\t -> xshow $ applyXmlFilter (getChildren) [t]) tatpstr)
							ssymbolname = xshow $ applyXmlFilter (
								pattern .> getChildren .>
								isTag "OMOBJ" .> getChildren .>
								isTag "OMATTR" .> getChildren .> 
								isTag "OMS" .> getValue "name" ) [tp]
							tsymbolname = xshow $ applyXmlFilter (
								value .> getChildren .>
								isTag "OMOBJ" .> getChildren .>
								isTag "OMATTR" .> getChildren .> 
								isTag "OMS" .> getValue "name" ) [tp]
							sorts = explode "-\\" $ Map.findWithDefault "" "type" tatpmap
							newOp = Op_type
								(funKindFromName $ Map.findWithDefault "Total" "funtype" tatpmap)
								(map Hets.stringToId ( if (length sorts) == 1 then [] else init sorts ))
								(Hets.stringToId $ last sorts) Id.nullRange
						in
							np
					x -> Debug.Trace.trace x np
					) Map.empty requations
		in
			(imports, (Map.adjust (Set.union (Debug.Trace.trace ("new symbol set : "++(show newSymbolsSet)) newSymbolsSet)) targetname sorts), preds, newOpsMap, Hets.emptyCASLMorphism)
				

			
xmlToMorphismMap::
	HXT.XmlTrees->
	Hets.MorphismMap
xmlToMorphismMap
	t
	=
		let
			hides = xshow $ applyXmlFilter (isTag "morphism" .> getQualValue "" "hiding") t
			pattern = isTag "requation" .> getChildren .> isTag "pattern"
			value = isTag "requation" .> getChildren .> isTag "value"
			vsymbol = value .> getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMS" .> getQualValue "" "name" 
			psymbol = pattern .> getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMS" .> getQualValue "" "name" 
			requations = applyXmlFilter (isTag "morphism" .> getChildren .> isTag "requation") t
			sortmap = foldl (\sm ts ->
				case applyXmlFilter (value .> getChildren .> isTag "OMATTR") [ts] of
					[] ->	let
								psymbolname = xshow $ applyXmlFilter psymbol [ts]
								vsymbolname = xshow $ applyXmlFilter vsymbol [ts]
							in
								if (psymbolname /= []) && (vsymbolname /= []) then
									Map.insert (Hets.stringToId psymbolname) (Hets.stringToId vsymbolname) sm
									else
									sm
					_ -> sm
					) Map.empty requations
			(opsmap, predsmap) = foldl (\(om,pm) tp ->
				let
					satp = applyXmlFilter (
						pattern .> getChildren .>
						isTag "OMOBJ" .> getChildren .>
						isTag "OMATTR" .> getChildren .>
						isTag "OMATP") [tp]
					tatp = applyXmlFilter (
						value .> getChildren .>
						isTag "OMOBJ" .> getChildren .>
						isTag "OMATTR" .> getChildren .>
						isTag "OMATP") [tp]
					satpsym = applyXmlFilter (getChildren .> isTag "OMS") satp
					satpstr = applyXmlFilter (getChildren .> isTag "OMSTR") satp
					satpmap = Map.fromList $ zip
						(map (\t -> xshow $ applyXmlFilter (getQualValue "" "name") [t]) satpsym)
						(map (\t -> xshow $ applyXmlFilter (getChildren) [t]) satpstr) 
					tatpsym = applyXmlFilter (getChildren .> isTag "OMS") tatp
					tatpstr = applyXmlFilter (getChildren .> isTag "OMSTR") tatp
					tatpmap = Map.fromList $ zip
						(map (\t -> xshow $ applyXmlFilter (getQualValue "" "name") [t]) tatpsym)
						(map (\t -> xshow $ applyXmlFilter (getChildren) [t]) tatpstr)
					ssymbolname = xshow $ applyXmlFilter (
						pattern .> getChildren .>
						isTag "OMOBJ" .> getChildren .>
						isTag "OMATTR" .> getChildren .> 
						isTag "OMS" .> getValue "name" ) [tp]
					tsymbolname = xshow $ applyXmlFilter (
						value .> getChildren .>
						isTag "OMOBJ" .> getChildren .>
						isTag "OMATTR" .> getChildren .> 
						isTag "OMS" .> getValue "name" ) [tp]
					ssorts = explode "-\\" $ Map.findWithDefault "" "type" satpmap
					tsorts = explode "-\\" $ Map.findWithDefault "" "type" tatpmap
					sOp = OpType
						-- The lookup-mechanism for displaying the morphism needs
						-- 'Partial' entries...
						Partial -- (funKindFromName $ Map.findWithDefault "Total" "funtype" satpmap)
						(map Hets.stringToId ( if (length ssorts) == 1 then [] else init ssorts ))
						(Hets.stringToId $ last ssorts)
					sPred = PredType
						(map Hets.stringToId ssorts)
					tOp = OpType
						(funKindFromName $ Map.findWithDefault "Total" "funtype" tatpmap)
						(map Hets.stringToId ( if (length tsorts) == 1 then [] else init tsorts ))
						(Hets.stringToId $ last tsorts)
					tPred = PredType
						(map Hets.stringToId tsorts)
				in
					case xshow $ applyXmlFilter (
							pattern .> getChildren .> 
							isTag "OMOBJ" .> getChildren .>
							isTag "OMATTR" .> getChildren .>
							isTag "OMATP" .> getChildren .>
							isTag "OMS" .> withSValue "cd" "casl" .>
							withSValue "name" "funtype" .>
							getQualValue "" "name") [tp] of
						"funtype" ->
								(Map.insert (Hets.stringToId ssymbolname, sOp) (Hets.stringToId tsymbolname, tOp) om, pm)
						"" ->
							if (ssymbolname /= []) && (tsymbolname /= [])
								then
									(om,
										Map.insert
											(Hets.stringToId ssymbolname, sPred)
											(Hets.stringToId tsymbolname, tPred)
											pm
									)
								else
									(om, pm)
						x ->
							Debug.Trace.trace ("Unknown Symbol : \"" ++ x ++ "\"") (om,pm)
					) (Map.empty, Map.empty) requations
		in
			(sortmap, opsmap, predsmap)

			
--helper
getAll::DGraph->(Hets.ImportsMap, Hets.SortsMap, Hets.RelsMap, Hets.PredsMap, Hets.OpsMap, Hets.SensMap)
getAll dg =
	(
		Hets.getNodeImportsNodeNames dg,
		Hets.getSortsWithNodeNames dg,
		Hets.getRelationsWithNodeNames dg,
		Hets.getPredMapsWithNodeNames dg,
		Hets.getOpMapsWithNodeNames dg,
		Hets.getSentencesWithNodeNames dg
	)
			
-- | this function partitions a list of CASLFORMULAS into two lists of
-- 'CASLFORMULA's : the first list contains 'normal' CFs and the second
-- all CFs that generate sorts (constructors)
partitionSensSortGen::[Ann.Named CASLFORMULA]->([Ann.Named CASLFORMULA],[Ann.Named CASLFORMULA])
partitionSensSortGen sens =
	foldl (\(sens,sortgen) s@(Ann.NamedSen name isaxiom sentence) ->
		if isPrefixOf "ga_generated_" name then
			case sentence of
				(Sort_gen_ax _ True) -> (sens, sortgen++[s])
				_ -> (sens++[s],sortgen)
		else
			(sens++[s],sortgen)
		) ([],[]) sens

-- | creates constructors from a list of 'CASLFORMULA's (see : 'partitionSensSortGen')
makeConstructors::[Ann.Named CASLFORMULA]->(Map.Map Id.Id (Map.Map Id.Id (Set.Set OpType)))
makeConstructors sortgenaxlist =
	Map.fromList $ map makeConstructorMap sortgenaxlist

-- | creates constructors from a 'CASLFORMULA'
makeConstructorMap::(Ann.Named CASLFORMULA)->(Id.Id, (Map.Map Id.Id (Set.Set OpType)))
makeConstructorMap (Ann.NamedSen senname _ (Sort_gen_ax cons _)) =
	let	sort = drop (length "ga_generated_") senname
		constructormap = foldl(\cmap (Constraint _ symbs _) ->
			foldl(\tcmap (Qual_op_name name ot _) ->
				Map.insertWith (Set.union) name (Set.singleton (cv_Op_typeToOpType ot)) tcmap) cmap $ map fst symbs
				) Map.empty cons
	in (Hets.stringToId sort, constructormap)

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

-- | creates a Conservativity from a String or fails with error
stringToConservativity::String->Conservativity
stringToConservativity "None" = None
stringToConservativity "Cons" = None
stringToConservativity "Mono" = None
stringToConservativity "Def" = None
stringToConservativity s = error ("Unknown Conservativity : \"" ++ s ++ "\"") 

-- | creates a String-representation of a DGLinkLab
linkToString::DGLinkLab->String
linkToString dgl =
	"Type:" ++ (linkTypeToString $ dgl_type dgl) ++ " Origin:" ++ (show $ dgl_origin dgl)

-- | stringToLinkType returns a list with at most one DGLinkType
-- Unknown links result in empty list
-- Currently this does not work very well because of some formatting issues...
stringToLinkType::String->[DGLinkType]
stringToLinkType s =
	if (length $ words s) == 0 then [] -- error "Cannot determine DGLinkType from empty string!"
	else
	let firstword = (words s)!!0
	in
	case firstword of
		"LocalDef" -> [LocalDef]
		"GlobalDef" -> [GlobalDef]
		"HidingDef" -> [HidingDef]
		"LocalThm" ->
			if (length $ words s) < 3 then Debug.Trace.trace ("No data for Conservativity in \"" ++ s ++ "\"") []
			else
			[LocalThm LeftOpen (stringToConservativity $ (words s)!!2) LeftOpen] 
		"GlobalThm" ->
			if (length $ words s) < 3 then Debug.Trace.trace ("No data for Conservativity in \"" ++ s ++ "\"") []
			else
			[GlobalThm LeftOpen (stringToConservativity $ (words s)!!2) LeftOpen]
		"HidingThm" ->
			[HidingThm Hets.emptyCASLGMorphism LeftOpen]
		"FreeDef" ->
			[FreeDef (EmptyNode (Logic.Logic CASL))]
		"CofreeDef" ->
			[CofreeDef (EmptyNode (Logic.Logic CASL))]
		_ -> Debug.Trace.trace ("Unknown DGLinkType : \"" ++ firstword ++ "\"") []
		
defaultDGLinkType::DGLinkType
defaultDGLinkType = GlobalDef

defaultDGOrigin::DGOrigin
defaultDGOrigin = DGExtension

defaultDGLinkLab::DGLinkLab
defaultDGLinkLab = DGLink Hets.emptyCASLGMorphism defaultDGLinkType defaultDGOrigin

headorempty::[[a]]->[a]
headorempty [] = []
headorempty x = head x

-- | stringToLink returns a list with at most one DGLinkLab (empty on error)
-- error when string is empty (or whitespace only)
stringToLink::String->[DGLinkLab]
stringToLink s =
	let	swords = words s
		ltype = drop (length "Type:") $ headorempty $ filter (isPrefix "Type:") swords
		linktypel = stringToLinkType ltype
		lorigin = drop (length "Origin:") $ headorempty $ filter (isPrefix "Origin:") swords
	in
		if (length swords == 0) then [] -- error "Cannot determine DGLinkLab from empty string!"
		else
			if linktypel == [] then [] else
			[DGLink Hets.emptyCASLGMorphism (head linktypel) (stringToOrigin lorigin)]

-- | stringToLEdge returns a list with at most one LEdge
-- empty on error, error on unknown link origins (nodes)
stringToLEdge::(Map.Map String Graph.Node)->Graph.Node->String->[(Graph.LEdge DGLinkLab)]
stringToLEdge nameNodeMap targetnode linkstring =
	let	swords = words linkstring
		lfrom = drop (length "From:") $ head $ filter (isPrefix "From:") swords
		linklabl = stringToLink linkstring
		sourcenode = Map.findWithDefault (error ("Unknown Node : \"" ++ lfrom ++ "\"")) lfrom nameNodeMap
	in
		if linklabl == [] then [] else
		[(sourcenode, targetnode, head linklabl)]
		
inDGToXml::DGraph->Graph.Node->(Map.Map Graph.Node String)->HXT.XmlFilter
inDGToXml dg n nodenames =
	let 	inLinks = map (\ (from,_,a) -> (from, a) ) $ Graph.inn dg n
		named = map ( \ (from, a) -> (Map.findWithDefault "unknownNode" from nodenames, a)) inLinks  
	in
	if length inLinks == 0 then HXT.txt "" else
	(HXT.etag "private" += (HXT.sattr "for" (Map.findWithDefault "unknownNode" n nodenames)))
	+= ((HXT.etag "data" += (HXT.sattr "format" "Hets-Imports" +++ HXT.sattr "pto" "Hets"))
		+= HXT.cdata (
		foldl (\ins (from, dgl) ->
			ins ++ ("From:"++ from ++ " " ++ (linkToString dgl) ++ "\n")
			) "\n" named)
		)

-- | retrieves a qualified value (prefix:localpart) from xml
-- but tries also without prefix, if no such value can be found...
getQualValue::String->String->XmlFilter
getQualValue "" localpart = getValue localpart
getQualValue prefix localpart =
	(\t -> if hasAttr (prefix ++ ":" ++ localpart) t /= []
		then
			getValue (prefix ++ ":" ++ localpart) t
		else
			getValue localpart t
	)
	

	
theoryNameFilter::HXT.XmlFilter
theoryNameFilter = (getQualValue theoryNameXMLNS theoryNameXMLAttr)
	
nodeNamesFromXml::HXT.XmlTrees->(Set.Set String)
nodeNamesFromXml t = 
	Set.fromList $ map (\n -> xshow [n]) $ applyXmlFilter ( isTag "theory" .> theoryNameFilter ) t
	
sortsFromXmlTheory::HXT.XmlTrees->(Set.Set SORT)
sortsFromXmlTheory t =
	Set.fromList $ map Hets.stringToId $ map (\n -> xshow [n]) $
		applyXmlFilter (
			getChildren .> isTag "symbol" .>
			withSValue "kind" "sort" .> getQualValue sortNameXMLNS sortNameXMLAttr) t
	
sortsFromXml::HXT.XmlTrees->Hets.SortsMap
sortsFromXml t =
	foldl (\map theory ->
		let	name = xshow $ applyXmlFilter theoryNameFilter [theory]
			sorts = sortsFromXmlTheory [theory]
		in
			Map.insert name sorts map
		) Map.empty $ applyXmlFilter (isTag "theory") t

relsFromXmlTheory::HXT.XmlTrees->(Rel.Rel SORT)
relsFromXmlTheory t =
	let	adts = applyXmlFilter (getChildren .> isTag "adt") t
		relations = concat $ map relsFromXmlADT adts
	in
		Rel.fromList relations
	where
	relsFromXmlADT::HXT.XmlTree->[(SORT, SORT)]
	relsFromXmlADT t =
		let	sort = Hets.stringToId $ xshow $ applyXmlFilter (getChildren .> isTag "sortdef" .> withSValue "type" "free" .> getValue "name") [t]
			insorts = map (\n -> Hets.stringToId $ drop 1 $ xshow [n]) $ applyXmlFilter (getChildren .> isTag "insort" .> getValue "for") [t]
			-- note that we restore 'CASL-Order' here
		in	map (\n -> (n, sort)) insorts
		
relsFromXml::HXT.XmlTrees->Hets.RelsMap
relsFromXml t =
	foldl (\map theory ->
		let	name = xshow $ applyXmlFilter theoryNameFilter [theory]
			rels = relsFromXmlTheory [theory]
		in
			Map.insert name rels map
		) Map.empty $ applyXmlFilter (isTag "theory") t
		
predsFromXmlTheory::HXT.XmlTrees->(Map.Map Id.Id (Set.Set PredType))
predsFromXmlTheory t =
	let	objsymbols = applyXmlFilter (getChildren .> isTag "symbol" .> withSValue "kind" "object") t
		predsymbols = filter (\n -> applyXmlFilter (
				getChildren .> isTag "type" .>
				getChildren .> isTag "OMOBJ" .>
				getChildren .> isTag "OMA" .>
				getChildren .> isTag "OMS" .>
				withSValue "cd" "casl" .>
				withSValue "name" "predication") [n] /= []) objsymbols
	in
		foldl (\map (p, pt) ->
			Map.insert p (Set.insert pt $ Map.findWithDefault Set.empty p map) map
			) Map.empty $ map predFromXmlSymbol predsymbols
	where
		predFromXmlSymbol::HXT.XmlTree->(Id.Id, PredType)
		predFromXmlSymbol t =
			let	pId = Hets.stringToId $ xshow $ applyXmlFilter (getQualValue "xml" "id") [t]
				args = applyXmlFilter (
					getChildren .> isTag "type" .> withSValue "system" "casl" .>
					getChildren .> isTag "OMOBJ" .>
					getChildren .> isTag "OMA" .>
					getChildren .> isTag "OMS" .>
					withValue "name" (/="predication") .>
					getValue "name" ) [t]
			in	(pId, PredType $ map (\n -> Hets.stringToId $ xshow [n]) args)
		
predsFromXml::HXT.XmlTrees->Hets.PredsMap
predsFromXml t =
	foldl (\map theory ->
		let	name = xshow $ applyXmlFilter theoryNameFilter [theory]
			preds = predsFromXmlTheory [theory]
		in
			Map.insert name preds map
		) Map.empty $ applyXmlFilter (isTag "theory") t
		
opsFromXmlTheory::HXT.XmlTrees->(Map.Map Id.Id (Set.Set OpType))
opsFromXmlTheory t =
	let	objsymbols = applyXmlFilter (getChildren .> isTag "symbol" .> withSValue "kind" "object") t
		opsymbols = filter (\n -> applyXmlFilter (
				getChildren .> isTag "type" .>
				getChildren .> isTag "OMOBJ" .>
				getChildren .> isTag "OMA" .>
				getChildren .> isTag "OMS" .>
				withSValue "cd" "casl" .>
				withValue "name" (\n -> n == "function" || n == "partial-function") ) [n] /= []) objsymbols
	in
		foldl (\map (p, pt) ->
			Map.insert p (Set.insert pt $ Map.findWithDefault Set.empty p map) map
			) Map.empty $ map opFromXmlSymbol opsymbols 
	where
		opFromXmlSymbol::HXT.XmlTree->(Id.Id, OpType)
		opFromXmlSymbol t =
			let	oId = Hets.stringToId $ xshow $ applyXmlFilter (getQualValue "xml" "id") [t]
				isTotal = applyXmlFilter (
					getChildren .> isTag "type" .> withSValue "system" "casl" .>
					getChildren .> isTag "OMOBJ" .>
					getChildren .> isTag "OMA" .>
					getChildren .> isTag "OMS" .>
					withSValue "name" "function") [t] /= []
				argsall = applyXmlFilter (
					getChildren .> isTag "type" .> withSValue "system" "casl" .>
					getChildren .> isTag "OMOBJ" .>
					getChildren .> isTag "OMA" .>
					getChildren .> isTag "OMS" .>
					withValue "name" (\n -> n /= "function" && n /= "partial-function") .>
					getValue "name" ) [t]
				args = take (length(argsall)-1) argsall
				res = Hets.stringToId $ xshow $ [last (argsall)]
			in	(oId, OpType (if isTotal then Total else Partial) (map (\n -> Hets.stringToId $ xshow [n]) args) res)
			
	
opsFromXml::HXT.XmlTrees->Hets.OpsMap
opsFromXml t =
	foldl (\map theory ->
		let	name = xshow $ applyXmlFilter theoryNameFilter [theory]
			ops = opsFromXmlTheory [theory]
		in
			Map.insert name ops map
		) Map.empty $ applyXmlFilter (isTag "theory") t

-- | imports lead to edges but if the information is not stored in the
-- document there is no clue on what type of edge to create...
data ImportHint = FromStructure (String, DGLinkLab) | FromData (String, DGLinkLab)
	deriving (Eq, Show)
	
fromName::ImportHint->String
fromName (FromStructure (s,_)) = s
fromName (FromData (s, _)) = s

getIHLink::ImportHint->DGLinkLab
getIHLink (FromStructure (_,l)) = l
getIHLink (FromData (_,l)) = l

-- simple ord-relation to make Set happy...	
instance Ord ImportHint where
	(FromStructure _) <= (FromStructure _) = True
	(FromStructure _) <= (FromData _) = True
	(FromData _) <= (FromData _) = True
	(FromData _) <= (FromStructure _) = False

-- | create information about the imports from the private fields...
createImportHints::HXT.XmlTrees->(Map.Map String (Set.Set ImportHint))
createImportHints t =
	let	privates = applyXmlFilter (isTag "private") t
		theonames = map (\t -> xshow [t]) $ applyXmlFilter (getQualValue "" "for") privates
	in
		foldl (\hints name ->
			let	pdata = xshow $ applyXmlFilter (
					withSValue "for" name .> getChildren .>
					isTag "data" .> withSValue "pto" "Hets" .>
					withSValue "format" "Hets-Imports" .> getChildren) privates
				ldata = lines pdata
			in
				if ldata == [] then -- empty lines create no hints...
					hints
					else
					foldl (\h l ->
						let
							lablink = stringToLink l
							fromname = drop (length "From:") $ headorempty $ filter (isPrefix "From:") $ words l
						in
							if l == [] then h -- empty lines create no hints...
								else
								if lablink == [] then -- error processing the line -> still create structure hint...
									Map.insert
										name
										(Set.union
											(Map.findWithDefault Set.empty name h)
											(Set.singleton (FromStructure (fromname, defaultDGLinkLab)) )
										)
										h
									else -- create a hint with the parsed lablink
									Map.insert
										name
										(Set.union
											(Map.findWithDefault Set.empty name h)
											(Set.singleton (FromData (fromname, (head lablink))))
										)
										h
							) hints ldata
				) Map.empty theonames
		
importsFromXmlTheory::HXT.XmlTrees->Hets.Imports
importsFromXmlTheory t =
	let
		imports = applyXmlFilter (getChildren .> isTag "imports") t
	in
		foldl (\imps i ->
			let
				from = drop 1 $ xshow $ applyXmlFilter (getValue "from") [i]
				mm = foldl (\(mmsm, mmfm, mmpm) m ->
					let
						(nmmsm, nmmfm, nmmpm) = xmlToMorphismMap [m]
					in
						(Map.union mmsm nmmsm, Map.union mmfm nmmfm, Map.union mmpm nmmpm)
					) (Map.empty, Map.empty, Map.empty) $ applyXmlFilter (getChildren .> isTag "morphism") [i]
			in
				Set.union imps (Set.singleton (from, (Just mm)))
		) Set.empty imports
	
importsFromXml::HXT.XmlTrees->Hets.ImportsMap
importsFromXml t =
	foldl (\map theory ->
		let	name = xshow $ applyXmlFilter (getQualValue "xml" "id") [theory]
			imports = importsFromXmlTheory [theory]
		in
			Map.insert name imports map
		) Map.empty $ applyXmlFilter (isTag "theory") t
		
sensFromXmlTheory::FormulaContext->HXT.XmlTrees->(Set.Set (Ann.Named CASLFORMULA))
sensFromXmlTheory fc t = Set.fromList $ unwrapFormulas fc $ applyXmlFilter (getChildren .> isTag "axiom") t

sensFromXml::FormulaContext->HXT.XmlTrees->Hets.SensMap
sensFromXml fc t = 
	foldl (\map theory ->
		let	name = xshow $ applyXmlFilter theoryNameFilter [theory]
			sens = sensFromXmlTheory (fc { currentName = name } ) [theory]
			consens = conSensFromXmlTheory [theory]
		in
			Map.insert name (Set.union sens consens) map
		) Map.empty $ applyXmlFilter (isTag "theory") t
		
conSensFromXmlTheory::HXT.XmlTrees->(Set.Set (Ann.Named CASLFORMULA))
conSensFromXmlTheory t =
	let
		adts = applyXmlFilter (getChildren .> isTag "adt") t
	in
		Set.fromList $ map (\t -> uncurry consToSens $ extractConsFromADT [t]) adts 
	

-- | recreate non-incremental (full) mappings from the received mappings and the imports-information
createFullMaps::Hets.SortsMap->Hets.RelsMap->Hets.PredsMap->Hets.OpsMap->Hets.SensMap->Hets.ImportsMap->String->
	(Set.Set SORT, Rel.Rel SORT, Map.Map Id.Id (Set.Set PredType), Map.Map Id.Id (Set.Set OpType), Set.Set (Ann.Named CASLFORMULA))
createFullMaps sortsmap relsmap predsmap opsmap sensmap importsmap nodename =
	let
		imports = getImports importsmap nodename
		sorts = foldl (\ss i -> Set.union ss (Map.findWithDefault Set.empty i sortsmap))
				(Map.findWithDefault Set.empty nodename sortsmap) $ Set.toList $ Set.map fst imports
		rels = foldl (\rl i -> Rel.union rl (Map.findWithDefault Rel.empty i relsmap))
				(Map.findWithDefault Rel.empty nodename relsmap) $ Set.toList $ Set.map fst imports
		preds = foldl (\rl i -> Map.union rl (Map.findWithDefault Map.empty i predsmap))
				(Map.findWithDefault Map.empty nodename predsmap) $ Set.toList $ Set.map fst imports
		ops = foldl (\rl i -> Map.union rl (Map.findWithDefault Map.empty i opsmap))
				(Map.findWithDefault Map.empty nodename opsmap) $ Set.toList $ Set.map fst imports
		sens = foldl (\rl i -> Set.union rl (Map.findWithDefault Set.empty i sensmap))
				(Map.findWithDefault Set.empty nodename sensmap) $ Set.toList $ Set.map fst imports
		msorts = foldl(\ms mmm ->
			case mmm of
				Nothing -> ms
				(Just mm) -> Hets.addMorphismSorts mm ms
				) sorts $ Set.toList $ Set.map snd imports 
		mpreds = foldl(\mp mmm ->
			case mmm of
				Nothing -> mp
				(Just mm) -> Hets.addMorphismPreds mm mp
				) preds $ Set.toList $ Set.map snd imports 
		mops = foldl(\mo mmm ->
			case mmm of
				Nothing -> mo
				(Just mm) -> Hets.addMorphismOps mm mo
				) ops $ Set.toList $ Set.map snd imports 
	in
		(msorts, rels, mpreds, mops, sens)
	
mapsToG_theory::(Set.Set SORT, Rel.Rel SORT, Map.Map Id.Id (Set.Set PredType), Map.Map Id.Id (Set.Set OpType), Set.Set (Ann.Named CASLFORMULA))->G_theory
mapsToG_theory (sortset, rels, predmap, opmap, sensmap) =
	G_theory
		CASL
		(Sign sortset rels opmap Map.empty predmap Map.empty [] [] ()) 
		(toThSens $ Set.toList sensmap)
		
mapsToDGNodeLab::(Set.Set SORT, Rel.Rel SORT, Map.Map Id.Id (Set.Set PredType), Map.Map Id.Id (Set.Set OpType), Set.Set (Ann.Named CASLFORMULA))->String->DGNodeLab
mapsToDGNodeLab maps nodename =
	DGNode
		(makeName $ Hets.stringToSimpleId nodename)
		(mapsToG_theory maps)
		Nothing
		Nothing
		DGBasic
		None
		LeftOpen
		
xmlToDGNodes::HXT.XmlTrees->(ImportGraph (HXT.XmlTrees, Maybe DGraph))->[DGNodeLab]
xmlToDGNodes t ig =
	let	nodenames = nodeNamesFromXml t
		importsMap = importsFromXml t
		sortsMap = sortsFromXml t
		relsMap = relsFromXml t
		predsMap = predsFromXml t
		opsMap = opsFromXml t
		sensMap = sensFromXml (FC importsMap sortsMap relsMap predsMap opsMap "") t
		ic = ImportContext importsMap sortsMap relsMap predsMap opsMap sensMap ig
	in	map
			(\n -> mapsToDGNodeLab
				(createFullMaps sortsMap relsMap predsMap opsMap sensMap importsMap n)
				n
			)
			$ Set.toList nodenames
			
importGraphToDGNodes::(ImportGraph (HXT.XmlTrees, Maybe DGraph))->Graph.Node->[DGNodeLab]
importGraphToDGNodes ig n =
	let
		mnode = Graph.lab ig n
		node = case mnode of
			Nothing -> error "node error!"
			(Just n) -> n
		omdoc = (\(S _ (omdoc' , _)) -> applyXmlFilter (isTag "omdoc" .> getChildren) omdoc' ) node
		nodenames = nodeNamesFromXml omdoc
		importsMap = importsFromXml omdoc
		sortsMap = sortsFromXml omdoc
		relsMap = relsFromXml omdoc
		predsMap = predsFromXml omdoc
		opsMap = opsFromXml omdoc
		sensMap = sensFromXml (FC importsMap sortsMap relsMap predsMap opsMap "") omdoc
		refimports = filter ( \(_,from,_) -> from /= n) $ Graph.out ig n
		refs = map ( \(to, from, (TI (theoname, theosource))) ->
			let
				moriginnode = Graph.lab ig from
				(S (sname, ssrc) (_,modg)) = case moriginnode of
					Nothing -> error "node error (import)!"
					(Just n) -> n
					-- the DG should have been created before accessing it
				odg = case modg of
					Nothing -> error "dg error"
					(Just d) -> d
				onodenum = case filter (\(_,node) -> (getDGNodeName node) == theoname ) $ Graph.labNodes odg of
					[] -> error "no such node in origin..."
					l -> fst $ head l
			in
				DGRef
					(Hets.stringToSimpleId theoname, "", 0)
					(ASL.Lib_id (ASL.Indirect_link ssrc Id.nullRange))
					onodenum
					Nothing
					Nothing
					) refimports
	in	
		(map
			(\n -> mapsToDGNodeLab
				(createFullMaps sortsMap relsMap predsMap opsMap sensMap importsMap n)
				n
			)
			$ Set.toList nodenames) ++ refs
		

		

cleanNodeName::DGNodeLab->DGNodeLab
cleanNodeName (node@(DGNode { })) =
	if isPrefix "AnonNode" (getDGNodeName node)
		then
			node { dgn_name = emptyNodeName }
		else
			node
cleanNodeName ref = ref

xmlToDGraph::HXT.XmlTrees->(ImportGraph (HXT.XmlTrees, Maybe DGraph))->DGraph
xmlToDGraph t ig =
	let	nodes = xmlToDGNodes t ig
		lnodes = (zip [1..] nodes)::[(Graph.Node, DGNodeLab)]
		nodegraph = (Graph.mkGraph lnodes [])::DGraph
		nameNodeMap = Map.fromList $ map ( \(n, node) -> (getDGNodeName node, n) ) $ lnodes
		imports = importsFromXml t
		importhints = createImportHints t
		ledges = foldl (
			\le (nodename, nodeimports) ->
				let	
					nodenum = Map.findWithDefault 0 nodename nameNodeMap
				in
					foldl (\le' ni ->
						let
							importnodenum = case Map.findWithDefault 0 ni nameNodeMap of
								0 -> Debug.Trace.trace ("Cannot find node for \"" ++ ni ++ "\"!") 0
								x -> x
							filteredimporthints = Set.filter (\h -> (fromName h) == ni) $ Map.findWithDefault Set.empty nodename importhints
						in	
							le' ++
							if Set.null filteredimporthints
								then
									[(importnodenum, nodenum, defaultDGLinkLab)]
								else
									map (\ih -> (importnodenum, nodenum, getIHLink ih)) $ Set.toList filteredimporthints
						) le $ Set.toList nodeimports
				) [] $ Map.toList $ Map.map (Set.map fst) imports
		validedges = foldl (\e newe@(n,m,_) ->
			if (n==0) || (m==0) then
				Debug.Trace.trace ("Invalid Edge found from " ++ (show n) ++ " to " ++ (show m) ++ "...") e
				else
				e++[newe]
				) [] ledges
		cleannodes = map (\(n,node) -> (n, cleanNodeName node)) lnodes  
	in
		Graph.mkGraph cleannodes validedges
		
getNodeSignature::(ImportGraph (HXT.XmlTrees, Maybe DGraph))->(Maybe DGNodeLab)->CASLSign
getNodeSignature igdg mnode =
	case mnode of
		Nothing -> Hets.emptyCASLSign
		(Just node@(DGNode {})) ->
			case Hets.getCASLSign $ dgn_sign node of
				Nothing -> Hets.emptyCASLSign
				(Just sign) -> sign
		(Just ref@(DGRef { dgn_libname = lname, dgn_node = rnode})) ->
			let
				libnode = filter (\(_, (S (_,src) (_,mdg))) -> src == (show lname)) $ Graph.labNodes igdg
			in
				case libnode of
					(l:r) ->
						case l of
							(_, (S (_,_) (_,(Just ldg)))) -> getNodeSignature igdg $ Graph.lab ldg rnode 
							_ -> Hets.emptyCASLSign
					_ -> Hets.emptyCASLSign

importGraphToDGraph::(ImportGraph (HXT.XmlTrees, Maybe DGraph))->Graph.Node->DGraph
importGraphToDGraph ig n =
	let
		mnode = Graph.lab ig n
		node = case mnode of
			Nothing -> error "node error!"
			(Just n) -> n
		omdoc = (\(S _ (omdoc' , _)) -> applyXmlFilter (isTag "omdoc" .> getChildren) omdoc' ) node
		nodes = importGraphToDGNodes ig n
		lnodes = (zip [1..] nodes)::[(Graph.Node, DGNodeLab)]
		nodegraph = (Graph.mkGraph lnodes [])::DGraph
		nameNodeMap = Map.fromList $ map ( \(n, node) -> (getDGNodeName node, n) ) $ lnodes
		imports = importsFromXml omdoc
		importhints = createImportHints omdoc
		ledges = foldl (
			\le (nodename, nodeimports) ->
				let	
					nodenum = Map.findWithDefault 0 nodename nameNodeMap
					tnode = case map snd $ filter (\(n,_) -> n == nodenum) lnodes of
						(l:r) -> l
						_ -> error "node error!"
					targetsign = getNodeSignature ig (Just tnode)
				in
					foldl (\le' (ni, mmm) ->
						let
							importnodenum = case Map.findWithDefault 0 ni nameNodeMap of
								0 -> Debug.Trace.trace ("Cannot find node for \"" ++ ni ++ "\"!") 0
								x -> x
							snode = case map snd $ filter (\(n,_) -> n == importnodenum) lnodes of
								(l:r) -> l
								_ -> error "node error!"
							sourcesign = getNodeSignature ig (Just snode)
							filteredimporthints = Set.filter (\h -> (fromName h) == ni) $ Map.findWithDefault Set.empty nodename importhints
							ddgl = case mmm of
								Nothing -> defaultDGLinkLab
								(Just mm) -> defaultDGLinkLab { dgl_origin = DGTranslation, dgl_morphism = (Hets.makeCASLGMorphism $ (Hets.morphismMapToMorphism mm) { mtarget=targetsign, msource = sourcesign}) }
						in	
							le' ++
							if Set.null filteredimporthints
								then
									[(importnodenum, nodenum, ddgl)]
								else
									map (\ih ->
										let
											ihlink = getIHLink ih
											link = case dgl_origin ihlink of
											-- this is rather ugly, but else morphisms would be lost for now...
												DGTranslation -> ihlink { dgl_morphism = dgl_morphism ddgl }
												_ -> ihlink
										in
											(importnodenum, nodenum, link)
										) $ Set.toList filteredimporthints
						) le $ Set.toList nodeimports
				) [] $ Map.toList imports
		validedges = foldl (\e newe@(n,m,_) ->
			if (n==0) || (m==0) then
				Debug.Trace.trace ("Invalid Edge found from " ++ (show n) ++ " to " ++ (show m) ++ "...") e
				else
				e++[newe]
				) [] ledges
		cleannodes = map (\(n,node) -> (n, cleanNodeName node)) lnodes  
	in
		Graph.mkGraph cleannodes validedges
		
getOmdocID::HXT.XmlTrees->String
getOmdocID = xshow . applyXmlFilter (isTag "omdoc" .> getQualValue "xml" "id")
		
omdocToDevGraph::HXT.XmlTrees->(DGraph, String)
omdocToDevGraph t = (xmlToDGraph (applyXmlFilter (isTag "omdoc" .> getChildren) t) (Graph.mkGraph [] []), getOmdocID t) 

importOmdoc::String->(IO (DGraph, String))
importOmdoc file =
	do
		importGraph <- makeImportGraph file
		loadresult <- loadOmdoc file
		omdoc <- case loadresult of
					(Left error) -> putStrLn ("Error loading \"" ++ file ++ "\"") >> return (HXT.txt "" emptyRoot)
					(Right doc) -> return doc
		return (xmlToDGraph omdoc (Graph.mkGraph [] []), getOmdocID omdoc)
		
	
dgNameToLnDGLe::(DGraph, String)->(ASL.LIB_NAME,DGraph,LibEnv)
dgNameToLnDGLe (dg, name) =
	let
		libname = (ASL.Lib_id (ASL.Indirect_link name Id.nullRange))
		lenv = Map.fromList $ [ (libname, (GA.emptyGlobalAnnos, Map.empty, dg))  ]
	in
		(libname, dg, lenv)
		
showDGAndName::(DGraph, String)->(IO ())
showDGAndName (dg,name) =
	Hets.showGraph name DOptions.defaultHetcatsOpts $
		(\a -> (Just a) ) $
		(\(a,b,c) -> (a, "", b, c)) $
		dgNameToLnDGLe (dg, name)
		
getCatalogueInformation::HXT.XmlTrees->(Map.Map String String)
getCatalogueInformation t =
	let
		catalogue = applyXmlFilter (getChildren .> isTag "catalogue") t
		locs = applyXmlFilter (getChildren .> isTag "loc") catalogue
		list = foldl (\l loc ->
			l ++ [ (xshow $ applyXmlFilter (getValue "theory") [loc], xshow $ applyXmlFilter (getValue "omdoc") [loc]) ]
			) [] locs
	in
		Map.fromList list
		
-- | theory name, theory source (local)
data TheoryImport = TI (String, String)

instance Show TheoryImport where
	show (TI (tn, ts)) = ("Import von \"" ++ tn ++ "\" aus \"" ++ ts ++ "\".")

-- | source name, source (absolute)
data Source a = S (String, String) a 

instance Show (Source a) where
	show (S (sn, sf) _) = ("Quelle \"" ++ sn ++ "\" Datei : \"" ++ sf ++ "\".");

type ImportGraph a = Tree.Gr (Source a) TheoryImport 

getImportMapFG::String->(IO ((String,HXT.XmlTrees,String), (Map.Map String String)))
getImportMapFG filename =
	do
		curdir <- System.Directory.getCurrentDirectory
		cfn <- System.IO.Error.catch
			(System.Directory.canonicalizePath filename)
			(\_ -> putStrLn ("Error canonicalizing...") >> return filename)
		putStrLn ("Processing : " ++ filename ++ " (" ++ cfn ++ ")")
		cfp <- return ( reverse $ dropWhile (\c -> not $ elem c [ '/','\\' ]) $ reverse cfn)
		loadresult <- loadOmdoc cfn
		omdoc <- case loadresult of
			(Left error) -> putStrLn ("Error loading \"" ++ cfn ++ "\"...") >> return (HXT.txt "" emptyRoot)
			(Right doc) -> return doc
		omdocid <- return (getOmdocID omdoc)
		catmap <- return (getCatalogueInformation omdoc)
		if not $ null cfp 
			then
				putStrLn ("Changing Path to : \"" ++ cfp ++ "\"") >>
					System.IO.Error.catch (System.Directory.setCurrentDirectory cfp) (\_ -> putStrLn ("Could not change path to \"" ++ cfp ++  "\""))
			else
				return ()
		canimps <- mapM
					(\(tn, fp) ->
						System.Directory.canonicalizePath fp >>= \canifp ->
						return (tn, fp)) $ Map.toList catmap -- canon. off
		canimpmap <- return $ Map.fromList canimps
		System.Directory.setCurrentDirectory curdir
		return ((omdocid, omdoc, cfn), canimpmap)	
		
makeImportGraph::String->(IO (ImportGraph HXT.XmlTrees))
makeImportGraph filename =
	do
	((omdocid, omdoc, cfn), imap) <- getImportMapFG filename
	nodeone <- return (1, S (omdocid, cfn) omdoc)
	foldl (\gio imp ->
		do
			gio >>= \g ->
				extendImportGraph g 1 (TI imp)
			) (return (Graph.mkGraph [nodeone] [])) $ Map.toList imap
		
	
extendImportGraph::(ImportGraph HXT.XmlTrees)->Graph.Node->TheoryImport->(IO (ImportGraph HXT.XmlTrees))
extendImportGraph ig n (TI (thn, src)) =
	do
		curdir <- System.Directory.getCurrentDirectory 
		(S (name, source) _) <- return ((\(Just a) -> a) $ Graph.lab ig n)
		sourcepath <- return (reverse $ dropWhile (\c -> not $ elem c ['\\','/']) $ reverse source)
		if null sourcepath
			then
				return ()
			else
				System.IO.Error.catch
					(System.Directory.setCurrentDirectory sourcepath)
						(\_ -> putStrLn ("Could not change path to \"" ++ sourcepath ++  "\""))
		nodenum <- return (length $ Graph.nodes ig)
		((omdocid, omdoc, cfn), imap) <- getImportMapFG src
		matchingNodes <- return (filter (\(_, (S (iname, isrc) _)) -> iname == omdocid && isrc == cfn ) $ Graph.labNodes ig)
		newnode <- return
			(if null matchingNodes
				then
					Debug.Trace.trace ("Creating new node for \"" ++ omdocid ++ "\"") (nodenum+1, S (omdocid, cfn) omdoc)
				else
					Debug.Trace.trace ("Using existing node for \"" ++ omdocid ++ "\"") $ head matchingNodes
			)
		newnodenum <- return ( (\(n, _) -> n) newnode )
		newedge <- return (n, newnodenum, TI (thn, src))
		newgraph <- return (Graph.insEdge newedge $ if null matchingNodes then Graph.insNode newnode ig else ig)
		newig <- (foldl (\nigio (thname, thsrc) ->
			do
				nigio >>= \nig ->
					extendImportGraph nig newnodenum (TI (thname, thsrc))
				) (return newgraph) $ Map.toList imap)
		System.Directory.setCurrentDirectory curdir
		return newig

		
-- if there is a cycle in the imports this will fail because the algorithm
-- processes only omdoc's that do import from already processed omdoc's or do
-- not import at all.
processImportGraph::(ImportGraph HXT.XmlTrees)->(ImportGraph (HXT.XmlTrees, Maybe DGraph))
processImportGraph ig =
	let
		-- create hybrid graph containing already processed DGs (none at first)
		hybrid = Graph.mkGraph
			(map (\(n, S a b) -> (n, S a (b, Nothing))) $ Graph.labNodes ig)
			(Graph.labEdges ig) :: (ImportGraph (HXT.XmlTrees, (Maybe DGraph)))
		-- create all DG's
		processed = process hybrid
	in
		processed
	where
		-- transform one node's omdoc-content to a DGraph and proceed until
		-- no more transformations are possible
		process ::
			(ImportGraph (HXT.XmlTrees, (Maybe DGraph))) ->
			(ImportGraph (HXT.XmlTrees, (Maybe DGraph)))
		process igxmd =
			let
				-- which nodes have no DGraph ?
				unprocessed = filter (\(_, S _ (b, mdg)) ->
					case mdg of
						Nothing -> True
						_ -> False
					) $ Graph.labNodes igxmd
				-- targets are nodes that import only from processed nodes
				-- or do not import at all
				targets = filter (\(nodenum, _) ->
					let
						-- get the outgoing edges (imports) for this node
						imports = Graph.out ig nodenum
						-- for all these edges, check whether it points
						-- to a unprocessed node
						unprocessedimports = filter (\(_,from,_) ->
							-- but do not count a reference back to current node...
							if null (filter (\(n,_) -> (n/=nodenum) && (from == n)) unprocessed)
								then
									False
								else
									True
								) imports
					in
						-- the filter is just to check, if there
						-- is something unprocessed 'in the way'
						null unprocessedimports ) unprocessed
			in
				-- okay, have any nodes survived the filter ?
				if null targets
					then
						-- no targets left
						igxmd
					else
						-- okay, process a target
						let
							-- does not really matter what target to choose...
							changednode = head targets
							-- perform conversion
							--(dg, name) = omdocToDevGraph $
							--	(\(_, S _ (omdoc, _)) -> omdoc) changednode
							changednodenum =
								(\(nodenum, _) -> nodenum) changednode
							dg = importGraphToDGraph igxmd changednodenum
							-- name = (\(_, (S (nname,_) _)) -> nname) changednode
							-- create the altered node
							newnode = (\(nodenum, S a (omdoc,_)) ->
								(nodenum, S a (omdoc, Just dg))) changednode
							-- fetch all other nodes
							othernodes = filter
								(\(n,_) -> n /= changednodenum) $
									Graph.labNodes igxmd
						in
							-- start the next round with the new graph
							process $ Graph.mkGraph
								(newnode:othernodes)
								(Graph.labEdges igxmd)
								
hybridGToDGraphG::(ImportGraph (HXT.XmlTrees, Maybe DGraph))->(ImportGraph DGraph)
hybridGToDGraphG ig =
	Graph.mkGraph
		( map (\(n, (S a (_,mdg))) ->
			let
				dg = case mdg of
					Nothing -> error "Cannot convert hybrid with unresolved DGraphs..."
					(Just dg) -> dg
			in
				(n, (S a dg))
				) $ Graph.labNodes ig)
		(Graph.labEdges ig)
		
dGraphGToLibEnv::(ImportGraph DGraph)->(ASL.LIB_NAME, DGraph, LibEnv)
dGraphGToLibEnv ig =
	let
		nodes = map (\(_,n) -> n) $ Graph.labNodes ig
		firstnode = case nodes of
			[] -> error "empty graph..."
			l -> head l
		firstsrc = (\(S (_,src) _) -> src) firstnode
		firstdg = (\(S _ dg) -> dg) firstnode
		lenv = Map.fromList $ map ( \(S (_, src) dg) ->
					(
						(ASL.Lib_id (ASL.Indirect_link src Id.nullRange)),
						(GA.emptyGlobalAnnos, Map.empty, dg)
					)
					) nodes
	in
		(ASL.Lib_id (ASL.Indirect_link firstsrc Id.nullRange), firstdg, lenv)
			
showdg::(ASL.LIB_NAME, DGraph, LibEnv)->IO ()
showdg (ln,dg,lenv) =
	Hets.showGraph "" Hets.dho (Just (ln, "", dg, lenv))
	 
showLink::DGraph->Graph.Node->Graph.Node->String
showLink dg n1 n2 =
	(getDGNodeName $ (\(Just a) -> a) $ Graph.lab dg n1)
	++ " -> " ++
	(getDGNodeName $ (\(Just a) -> a) $ Graph.lab dg n2)
	
showLinkType::DGLinkType->String
showLinkType lt = case lt of 
        LocalDef -> "LocalDef"
        GlobalDef -> "GlobalDef"
        HidingDef -> "HidingDef"
        FreeDef _ -> "FreeDef"
        CofreeDef _ -> "CofreeDef"
	LocalThm _ _ _ -> "LocalThm"
	GlobalThm _ _ _ -> "GlobalThm"
	HidingThm _ _ -> "HidingThm"
        FreeThm _ _ -> "FreeThm"
	
showEdge::DGLinkLab->String
showEdge ll = showLinkType (dgl_type ll)
	
showLinks::DGraph->[String]
showLinks dg =
	map (\(a,b,edge) -> (showLink dg a b) ++ " (" ++ (showEdge edge) ++ ")") $ Graph.labEdges dg
	

-- | get all imports for a node (recursive)
-- note : this is used for acyclic imports only
getImports::Hets.ImportsMap->String->Hets.Imports
getImports importsmap nodename =
	let currentimports = Map.findWithDefault Set.empty nodename importsmap
	in
		foldl (\is (i,_) ->
			Set.union is (getImports importsmap i)
			) currentimports $ Set.toList currentimports


-- | this function just searches for an edge in the DGraph that matches a certain
-- edge and then returns it with the connecting node numbers...
getFullEdge::Static.DevGraph.DGraph->Static.DevGraph.DGLinkLab->(Maybe (Graph.Node, Graph.Node, Static.DevGraph.DGLinkLab))
getFullEdge dg ll = let edges = Graph.labEdges dg
		    in
		    findEdge edges ll where
		    findEdge::[(Graph.Node, Graph.Node, Static.DevGraph.DGLinkLab)]->Static.DevGraph.DGLinkLab->(Maybe (Graph.Node, Graph.Node, Static.DevGraph.DGLinkLab))
		    findEdge [] _ = Nothing
		    fingEdge ((labedge@(n1, n2, ll' )):rest) ll = if ll' == ll then (Just labedge) else findEdge rest ll
		    
-- | this is a more practical than mathmatical approach...
-- You cannot deny, it is readable...
processConservativity::Static.DevGraph.Conservativity->(HXT.XmlTree->HXT.XmlTrees)
processConservativity None = (HXT.etag "OMSTR" += HXT.txt "Conservativity: None") +++ xmlNL 
processConservativity Cons = (HXT.etag "OMSTR" += HXT.txt "Conservativity: Cons") +++ xmlNL
processConservativity Mono = (HXT.etag "OMSTR" += HXT.txt "Conservativity: Mono") +++ xmlNL
processConservativity Def = (HXT.etag "OMSTR" += HXT.txt "Conservativity: Def") +++ xmlNL


nodeNameForXml::String->Graph.Node->String
nodeNameForXml "" n = "anonnode:"++(show n)
nodeNameForXml s _ = s
				
libNameToXml::ASL.LIB_NAME->(HXT.XmlTree->HXT.XmlTrees)
libNameToXml (ASL.Lib_version lid lvs) = (HXT.etag "OMA" += (
					(HXT.etag "OMS" += (HXT.sattr "cd" "hets" +++ HXT.sattr "name" "lib-version"))
					+++
					(libIdToXml lid) +++ xmlNL +++ (libVsToXml lvs)
					)) +++ xmlNL
libNameToXml (ASL.Lib_id lid) = (HXT.etag "OMA" += (
					(HXT.etag "OMS" += (HXT.sattr "cd" "hets" +++ HXT.sattr "name" "lib-id"))
					+++
					libIdToXml lid)
					) +++ xmlNL

libIdToXml::ASL.LIB_ID->(HXT.XmlTree->HXT.XmlTrees)
libIdToXml (ASL.Direct_link url _) = (HXT.etag "OMA" += (
					(HXT.etag "OMS" += (HXT.sattr "cd" "hets" +++ HXT.sattr "name" "direct-link"))
					+++ (HXT.etag "OMSTR" += (HXT.txt url)))) +++ xmlNL
libIdToXml (ASL.Indirect_link path _) = (HXT.etag "OMA" += (
					(HXT.etag "OMS" += (HXT.sattr "cd" "hets" +++ HXT.sattr "name" "indirect-link"))
					+++ (HXT.etag "OMSTR" += (HXT.txt path)))) +++ xmlNL
					
libVsToXml::ASL.VERSION_NUMBER->(HXT.XmlTree->HXT.XmlTrees)
libVsToXml (ASL.Version_number sl _) = (HXT.etag "OMA" += (
					(HXT.etag "OMS" += (HXT.sattr "cd" "hets" +++ HXT.sattr "name" "version-number"))
					+++ ( foldl (\sx s -> sx +++ (HXT.etag "OMSTR" += (HXT.txt s)) +++ xmlNL) (HXT.txt "") sl )))
				+++ xmlNL
					
				
-- | this function takes care of 'rendering' the DGRef to Xml
makeRefTheory::String->Graph.Node->(HXT.XmlTree->HXT.XmlTrees)
makeRefTheory libname node =
	(HXT.etag "theory" += (
		HXT.sattr "id" "reference"
		+++ xmlNL
		+++ (HXT.etag "OMOBJ" += (
			HXT.etag "OMA" += (
				-- I defined a symbol for the fetching...
				-- maybe this should be done with metadata,
				-- as it is not at all mathmaticaly relevant...
				(HXT.etag "OMS" += (HXT.sattr "cd" "hets" +++ HXT.sattr "name" "getnode"))
				+++ (HXT.etag "OMSTR" += (HXT.txt libname))
				+++ (HXT.etag "OMI" += (HXT.txt (show node)))
				)
			))
		+++ xmlNL
			)) +++ xmlNL

-- DGNODELABTOXML END

-- We also need to build up a catalogue for all imported theories

-- BUILDCATALOGUE BEGIN
makeOmdocCatalogue::[(String, String, String)]->(HXT.XmlTree->HXT.XmlTrees)
makeOmdocCatalogue [] = HXT.txt ""
makeOmdocCatalogue t =	(HXT.etag "catalogue" += (
				foldl (\locs (t,o,c) ->
					(HXT.etag "loc" += (HXT.sattr "theory" t +++ HXT.sattr "omdoc" o +++ HXT.sattr "cd" c))
					+++ xmlNL) (HXT.txt "") t
				)
			) +++ xmlNL

buildCatalogue::Static.DevGraph.DGraph->[(String, String, String)]
buildCatalogue dg =	let	justlabnodes = map (\(_,a)->a) $ Graph.labNodes dg
				dgrefs = filter Static.DevGraph.isDGRef justlabnodes
			in
				foldl (\list (DGRef _ libname node _ _) ->
					list ++ [(show node, (getLibURI libname), caslS)])
					[] dgrefs
					
getLibURI::ASL.LIB_NAME->String
getLibURI (ASL.Lib_version libid libvs) = show libid
getLibURI (ASL.Lib_id libid) = show libid

-- BUILDCATALOGUE END

-- | sadly '_' is also valid in Names, so this functions tries to catch this
-- by assuming that the extension is the string after the last '_' but only
-- if there is a number at the end...
stringToNodeName ::String->Static.DevGraph.NODE_NAME
stringToNodeName s = let extNumS = reverse (takeWhile (\x -> x /= '_')  (reverse s))
		     in
		     if (length extNumS) == (length s) then (Hets.stringToSimpleId s, "", 0)
			else
			  let numS = reverse (takeWhile (\x -> elem x ['0'..'9']) (reverse extNumS))
			      realExt = take ((length extNumS)-(length numS)) extNumS
			  in
			  if (numS == "") then (Hets.stringToSimpleId s, "", 0) else
			  	(Hets.stringToSimpleId (take (((length s) - length (extNumS)) - 1) s), realExt, (read numS)::Int)
				
xmlToLibName::HXT.XmlTrees->ASL.LIB_NAME
xmlToLibName t = if applyXmlFilter (getChildren .> isTag "OMS" .> withSValue "cd" "hets" .> withSValue "name" "lib-version") t /= []
			then ASL.Lib_version (xmlToLibId [(applyXmlFilter (getChildren .> isTag "OMA") t)!!0]) (xmlToLibVs [(applyXmlFilter (getChildren .> isTag "OMA") t)!!1])
			else ASL.Lib_id (xmlToLibId $ applyXmlFilter (getChildren .> isTag "OMA") t)
			
xmlToLibId::HXT.XmlTrees->ASL.LIB_ID
xmlToLibId t = if applyXmlFilter (getChildren .> isTag "OMS" .> withSValue "cd" "hets" .> withSValue "name" "direct-link") t /= []
			then ASL.Direct_link (xshow $ applyXmlFilter (getChildren .> isTag "OMSTR" .> getChildren) t) Id.nullRange
			else ASL.Indirect_link (xshow $ applyXmlFilter (getChildren .> isTag "OMSTR" .> getChildren) t) Id.nullRange
			
xmlToLibVs::HXT.XmlTrees->ASL.VERSION_NUMBER
xmlToLibVs t = 	let	stringsx = applyXmlFilter (getChildren .> isTag "OMSTR" .> getChildren) t
		in
		   ASL.Version_number (foldl (\sl sx -> sl ++ [xshow [sx]]) [] stringsx) Id.nullRange

-- XMLTONODES END

-- | helper-function to get a node from a DGraph by Name
findNode::Static.DevGraph.DGraph->String->(Graph.LNode Static.DevGraph.DGNodeLab)
findNode dg name = findNode' name $ Graph.labNodes dg where
	findNode' ::String->[Graph.LNode Static.DevGraph.DGNodeLab]->(Graph.LNode Static.DevGraph.DGNodeLab)
	findNode' _ [] = error ("No such Node \"" ++ name ++ "\"")
	findNode' name ((n,node):rest) = if (Static.DevGraph.getDGNodeName node) == name then (n, node)
					else findNode' name rest

-- | backparsing of origin					
xmlToOrigin::HXT.XmlTrees->Static.DevGraph.DGOrigin
xmlToOrigin t = let orig_string = xshow $ applyXmlFilter (isTag "CMP" .> getChildren .> isTag "OMOBJ" .> getChildren .> isTag "OMSTR" .> getChildren) t
		in
		stringToOrigin orig_string
		
-- | create an origin from string.
stringToOrigin::String->Static.DevGraph.DGOrigin
stringToOrigin s
	| (s == "DGBasic") = DGBasic 
	| (s == "DGExtension") = DGExtension
	| (s == "DGTranslation") = DGTranslation 
	| (s == "DGUnion") = DGUnion
	| (s == "DGHiding") = DGHiding 
	| (s == "DGRevealing") = DGRevealing 
	| (s == "DGRevealTranslation") = DGRevealTranslation 
	| (s == "DGFree") = DGFree
	| (s == "DGCofree") = DGCofree
	| (s == "DGLocal") = DGLocal
	| (s == "DGClosed") = DGClosed
	| (s == "DGClosedLenv") = DGClosedLenv
	| (s == "DGLogicQual") = DGLogicQual
	| (s == "DGLogicQualLenv") = DGLogicQualLenv
	| (s == "DGData") = DGData
	| (s == "DGFormalParams") = DGFormalParams
	| (s == "DGImports") = DGImports
	| (s == "DGFitSpec") = DGFitSpec
	| (s == "DGProof") = DGProof
	| otherwise = if isPrefix "DGSpecInst " s then
				DGSpecInst (Hets.stringToSimpleId (drop (length "DGSpecInst ") s))
		      else
		      if isPrefix "DGView " s then
				DGView (Hets.stringToSimpleId (drop (length "DGView ") s))
		      else
		      if isPrefix "DGFitView " s then
				DGFitView (Hets.stringToSimpleId (drop (length "DGFitView ") s))
		      else
		      if isPrefix "DGFitViewImp " s then
				DGFitViewImp (Hets.stringToSimpleId (drop (length "DGFitViewImp ") s))
		      else
		      if isPrefix "DGFitViewA " s then
				DGFitViewA (Hets.stringToSimpleId (drop (length "DGFitViewA ") s))
		      else
		      if isPrefix "DGFitViewAImp " s then
				DGFitViewAImp (Hets.stringToSimpleId (drop (length "DGFitViewAImp ") s))
		      --else error ("No such origin \"" ++ s ++ "\"")
		      else DGBasic
		      
buildMaps::HXT.XmlTrees->(Map.Map SORT SORT, Map.Map (Id.Id, OpType) (Id.Id, FunKind), Map.Map (Id.Id, PredType) Id.Id)
buildMaps t = foldl (\(sm,fm,pm) x ->
			let	patternoo = applyXmlFilter (getChildren .> isTag "pattern" .> getChildren .> isTag "OMOBJ") [x]
				valueoo = applyXmlFilter (getChildren .> isTag "value" .> getChildren .> isTag "OMOBJ") [x]
			in
			if applyXmlFilter (getChildren .> isTag "OMS") patternoo /= []
				then
					let 	sort1 = Hets.stringToId $ xshow $ applyXmlFilter (getChildren .> isTag "OMS" .> getValue "name") patternoo
						sort2 = Hets.stringToId $ xshow $ applyXmlFilter (getChildren .> isTag "OMS" .> getValue "name") valueoo
					in
						(Map.insert (sort1) (sort2) sm, fm, pm)
			else
			if applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withSValue "name" "predication") patternoo /= []
				then
					let	id1 = Hets.stringToId $ xshow $ applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMS" .> withValue "name" (/="result") .> getValue "name") patternoo
						parx = applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMBVAR" .> getChildren) patternoo
						par = foldl (\pl px ->
								pl ++ [Hets.stringToId $ xshow $ applyXmlFilter (isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" (/=typeS) .> getValue "name") [px]]
								) [] parx
						id2 = Hets.stringToId $ xshow $ applyXmlFilter (isTag "OMATTR" .> getChildren .> isTag "OMS" .> withValue "name" (/="result") .> getValue "name") valueoo
					in
						(sm, fm, Map.insert (id1, (PredType par)) (id2) pm)
			else
			if applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" ( \s -> (s == "Total" || s == "Partial")) ) patternoo /= []
				then
					let	ft1S = xshow $ applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" ( \s -> (s == "Total" || s == "Partial") ) .> getValue "name") patternoo
						ft1 = if ft1S == "Partial" then Partial else Total
						id1 = Hets.stringToId $ xshow $ applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMS" .> withValue "name" (/="result") .> getValue "name") patternoo
						parx = applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMBVAR" .> getChildren) patternoo
						par = foldl (\pl px ->
								pl ++ [Hets.stringToId $ xshow $ applyXmlFilter (isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" (/=typeS) .> getValue "name") [px]]
								) [] parx
						res = Hets.stringToId $ xshow $ applyXmlFilter (getChildren .> isTag "OMBIND" .> getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> withValue "name" (\s -> (s /= typeS && s /= "Partial" && s /= "Total")) .> getValue "name") patternoo
						ft2S = xshow $ applyXmlFilter (getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" ( \s -> (s == "Total" || s == "Partial")) .> getValue "name") valueoo
						ft2 = if ft2S == "Partial" then Partial else Total
						id2 = Hets.stringToId $ xshow $ applyXmlFilter (getChildren .> isTag "OMATTR" .> getChildren .> isTag "OMS" .> getValue "name") valueoo
					in
						(sm, Map.insert (id1, (OpType ft1 par res)) (id2, ft2) fm, pm)
			else
				error ("Cannot build maps with : \"" ++ xshow [x] ++ "\"")
			) (Map.empty, Map.empty, Map.empty) t
						
-- XMLTOLINKS END
{-
-- FETCHPROOFSTEPS BEGIN

{-
What are proof-steps ?
Proof-steps are just lists of Edges.
After reading in all nodes and all edges we can go to collect proof-steps
Just came to my mind :
	When fetching proof-steps I do not have to consider replacing the
	links before finishing everything, because Proof-Steps will not
	link to other proof-steps...
-}

-- This function extracts proof-steps from Xml using an already constructed
-- DGraph for Information
fetchProofSteps::Static.DevGraph.DGraph->HXT.XmlTrees->Static.DevGraph.DGraph
fetchProofSteps dg t = let	theories = applyXmlFilter (isTag "theory") t
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
fetchProofStepsFor dg t = let	tnameS = xshow $ applyXmlFilter (getValue "id") t
				toNodeN = nodeNameToNodeNum (Graph.labNodes dg) tnameS
				importswithproofsteps = applyXmlFilter (getChildren .> (isTag "axiom-inclusion" +++ isTag "theory-inclusion")) t
				proofsteps = applyXmlFilter (getChildren .> isTag "proof-object") t
			  in
			    foldl (\newdg importx ->
			    		let	isLocalThm = applyXmlFilter (isTag "axiom-inclusion") [importx] /= []
						fromNameS = xshow $ applyXmlFilter (getValue "from") [importx]
						fromNodeN = nodeNameToNodeNum (Graph.labNodes dg) fromNameS
						(n, m, myedge) = getSpecialEdge (Graph.labEdges newdg) fromNodeN toNodeN (if isLocalThm then isLocalThmEdge else isGlobalThmEdge)
						-- every import has at most one proof-object...
						thisproofsteps = applyXmlFilter (withSValue "theory" fromNameS .> withSValue "for" tnameS) proofsteps
						(tls1, cons, tls2) = xmlToLinkStatus dg thisproofsteps
					in Graph.insEdge (n, m, (replaceThmLinkStati myedge (tls1, cons, tls2))) (Graph.delEdge (n,m) newdg)
					) dg importswithproofsteps

-}
-- Helper-function to get the Number of a Node in the DGraph given the Name
nodeNameToNodeNum::[Graph.LNode Static.DevGraph.DGNodeLab]->String->Graph.Node
nodeNameToNodeNum [] _ = error "no such node"
nodeNameToNodeNum ((n, node):rest) name = if name == (Static.DevGraph.getDGNodeName node) then n
						else nodeNameToNodeNum rest name
		

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
getEdgeByNodeNums ((theedge@(n,m,edge)):rest) n' m' = if ( n==n' ) && ( m == m' ) then theedge
							else getEdgeByNodeNums rest n' m'

-- To create proof-steps, all Edges have to be already in the DG
xmlToProofSteps::HXT.XmlTrees->Static.DevGraph.DGraph->[Static.DevGraph.DGLinkLab]
xmlToProofSteps t dg = map (\t -> xmlToProofStep [t] dg) $ ((applyXmlFilter (isTag "OMSTR") t)::[XmlTree])

-- create a single proof-step (find an edge)
xmlToProofStep::HXT.XmlTrees->Static.DevGraph.DGraph->Static.DevGraph.DGLinkLab
xmlToProofStep t dg = let	n1ton2S = xshow $ applyXmlFilter (getChildren) t
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
-- helper function
isPrefix::String->String->Bool
isPrefix [] _ = True
isPrefix _ [] = False
isPrefix (p:p' ) (s:s' ) = (p == s) && (isPrefix p' s')

-- finds a nodeNumber by Name (maybe)
findNodeNumFor::[(Graph.LNode Static.DevGraph.DGNodeLab)]->String->(Maybe Graph.Node)
findNodeNumFor [] name = Nothing
findNodeNumFor ((n, node):rest) name = if (name == Static.DevGraph.getDGNodeName node) then (Just n)
					else findNodeNumFor rest name
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
			  
-- FETCHPROOFSTEPS END

-- CLEANUP BEGIN
-- we need to clear the anonymous nodes after the whole graph creation
-- we needed the unique names to build the edges...

cleanup::Static.DevGraph.DGraph->Static.DevGraph.DGraph
cleanup dg =	let	labnodes = Graph.labNodes dg
			labedges = Graph.labEdges dg
			cleannodes = map (\(n,node) -> (n,cleannode node)) labnodes
		in Graph.mkGraph cleannodes labedges
		
cleannode::Static.DevGraph.DGNodeLab->Static.DevGraph.DGNodeLab
cleannode (Static.DevGraph.DGNode nam sgn arg sns nf sig org) = Static.DevGraph.DGNode (cleanname nam) sgn arg sns nf sig org  
cleannode (Static.DevGraph.DGRef nam ln n nf sig) = Static.DevGraph.DGRef (cleanname nam) ln n nf sig

cleanname::Static.DevGraph.NODE_NAME->Static.DevGraph.NODE_NAME
cleanname n = if isPrefix "anonnode:" (Static.DevGraph.showName n) then Static.DevGraph.emptyNodeName else n
		

-- CLEANUP END
			
{- I think the following functions are not used (anymore) -}

{-
To Create Edges we need to reparse theories while having already computed the
nodes. Because theories are refered to by their names we can build the real
edges by referring to the nodes (we need their signs...).
-}
fetchEdges::Static.DevGraph.DGraph->HXT.XmlTrees->Static.DevGraph.DGraph
fetchEdges dgwithnodes theories =
	-- each theorie can contain multiple imports from other theories (edges)
	let y = map (\t -> let
			(theoryName, imports, proofs) = getTheoryNameImportAndProof [t]
		   in Nothing ) theories
	in
	dgwithnodes	

-- to clear the code a bit	
validImports::HXT.XmlFilter
validImports = (isTag "imports" +++ isTag "axiom-inclusion" +++ isTag "theory-inclusion")

-- to clear the code a bit	
validProofs::HXT.XmlFilter
validProofs = (isTag "proofobject")

-- this function splits a theory-XmlTree into its name, imports and proof-steps
getTheoryNameImportAndProof::HXT.XmlTrees->(String, XmlTrees, XmlTrees)
getTheoryNameImportAndProof t = (
				 xshow $ applyXmlFilter (isTag "theory" .> getValue "id") t
				,applyXmlFilter (getChildren .> validImports) t
				,applyXmlFilter (getChildren .> validProofs) t
				)


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

		

-- for some wierd reason, 'lab' from Graph can't be used...
-- I don't get it... this function is almost a copy...
lab :: Static.DevGraph.DGraph-> Graph.Node -> Maybe DGNodeLab
lab g v = fst (Graph.match v g) >>= return . Graph.lab' 


-- I don't think this function is really used or I have found something else
-- for processing inclusions...
xmlToLinkType::HXT.XmlTrees->Static.DevGraph.DGLinkType
xmlToLinkType t = if applyXmlFilter (isTag "imports") t /= [] then
		 let	ltypeS = xshow $ applyXmlFilter(getValue "type") t
		 in
		 if ltypeS == "local" then LocalDef
		 else
		 if ltypeS == "global" then GlobalDef
		 else
		 if ltypeS == "hiding" then HidingDef -- not in Omdoc...
		 else
		   error ("Illegal Import-type in : \""++ xshow t ++"\"")
	      else
	        error ("Cannot create Link-Type from : \""++ xshow t ++"\"")



-- FORMULAS -> X M L 

-- Above ends the part for creating DGraphs
-- No we enter the fascinating world of Formula-Processing... (22:58)

-- Formulas as OMA
-- wrap in Theory-axiom-FMP.

wrapFormulas::Hets.ImportsMap->Hets.SortsMap->Hets.PredsMap->Hets.OpsMap->String->[(Ann.Named CASLFORMULA)]->(HXT.XmlTree->HXT.XmlTrees)
wrapFormulas imports sorts preds ops name fs = (\(a,_) -> a) $ foldl (\(wrapped, n) f -> (wrapped +++ (wrapFormula imports sorts preds ops name n f), n+1) ) (HXT.txt "", 1) fs

wrapFormula::Hets.ImportsMap->Hets.SortsMap->Hets.PredsMap->Hets.OpsMap->String->Int->(Ann.Named CASLFORMULA)->(HXT.XmlTree->HXT.XmlTrees)
wrapFormula imports sorts preds ops tname number ansen = ( (createQAttributed "axiom" [("xml", "id", let name = (Ann.senName ansen) in if name=="" then ("AnonAx"++(show number)) else name)])
			  += ( (xmlNL +++ (HXT.etag "FMP"
			  	+= ( xmlNL +++ (HXT.etag "OMOBJ" +++ xmlNL)
			  		+= (xmlNL +++ (processFormula imports sorts preds ops tname (Ann.sentence ansen)) ) +++ xmlNL ) ) +++ xmlNL ) ) ) +++ xmlNL
	
-- shortcut to create an attribute with a qualified name (but no namespace uri)
-- leave prefix (p) blank to just have a normal attribute
qualattr::String->String->String->XmlFilter
qualattr p a v = HXT.qattr (HXT.mkPrefixLocalPart p a) (HXT.mkXText v)
--qualattr p a v = HXT.qattr (HXT.mkPrefixLocalPart "" a) (HXT.mkXText v)

-- creates a tag with qualified attributes (p,a,v) (no namespace uri)
createQAttributed::String->[(String,String,String)]->XmlFilter
createQAttributed tagname attributes =
	foldl (\tag (p, a, v) -> tag += qualattr p a v) (HXT.etag tagname) attributes
					
-- creates a tag with unqualified attributes (a,v)
createAttributed::String->[(String,String)]->XmlFilter
createAttributed tagname attributes =
	createQAttributed tagname $ map (\(a, v) -> ("", a, v) ) attributes
					
--caslS :: String -- moved to OmdocDevGraph
--typeS :: String

--caslQuantificationS
caslConjunctionS
	,caslDisjunctionS
	,caslImplicationS
	,caslEquivalenceS
	,caslNegationS
	,caslPredicationS
	,caslDefinednessS
	,caslExistl_equationS
	,caslStrong_equationS
	,caslMembershipS
	,caslSort_gen_axS :: String

caslSymbolQuantUniversalS
	,caslSymbolQuantExistentialS
	,caslSymbolQuantUnique_existentialS
	,caslSymbolAtomFalseS
	,caslSymbolAtomTrueS :: String


unsupportedS :: String

--caslS = "casl"
--typeS = "type"

--caslQuantificationS = "quantification"
caslConjunctionS = "conjunction"
caslDisjunctionS = "disjunction"
caslImplicationS = "implication"
caslImplication2S = "implies"
caslEquivalenceS = "equivalence"
caslEquivalence2S = "equal"
caslNegationS = "neg"
caslPredicationS = "predication"
caslDefinednessS = "definedness"
caslExistl_equationS = "existial-equation"
caslStrong_equationS = "strong-equation"
caslMembershipS = "membership"
caslSort_gen_axS = "sort-gen-ax"

caslSymbolQuantUniversalS = "universal"
caslSymbolQuantExistentialS = "existential"
caslSymbolQuantUnique_existentialS = "unique-existential"

caslSymbolAtomFalseS = "false"
caslSymbolAtomTrueS = "true"

unsupportedS = "unsupported-formula"


createSymbolForSort::Hets.ImportsMap->Hets.SortsMap->SORT->String->(HXT.XmlTree->HXT.XmlTrees)
createSymbolForSort imports sorts sort name =
	HXT.etag "OMS" += ( HXT.sattr "cd" (fromMaybe "unknown" $ Hets.findNodeNameForSort imports sorts sort name) +++ HXT.sattr "name" (show sort) )

-- | create the xml-representation for a formula (in context of a theory)	
processFormula ::
	Hets.ImportsMap-> -- ^ the map of imports
	Hets.SortsMap-> -- ^ the map of sorts
	Hets.PredsMap-> -- ^ the map of predications
	Hets.OpsMap-> -- ^ the map of operators
	String-> -- ^ the name of the current theory
	(FORMULA f)-> -- ^ the formula to process
	(HXT.XmlTree->HXT.XmlTrees) -- ^ a xml-representation of the formula
-- Quantification
processFormula imports sorts preds ops name
	(Quantification q vl f _) =
		( HXT.etag "OMBIND" += (
			xmlNL +++
			(HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" (quantName q))
			) +++
			(xmlNL) +++
			(processVarDecl imports sorts name vl) +++
			(processFormula imports sorts preds ops name f) )
		) +++
		xmlNL
-- Conjunction
processFormula imports sorts preds ops name
	(Conjunction fl _) =
		(HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslConjunctionS)
			) +++
			(foldl (\forms f ->
				forms +++
				processFormula imports sorts preds ops name f
				) (xmlNL) fl)
		) ) +++
		xmlNL
-- Disjunction
processFormula imports sorts preds ops name
	(Disjunction fl _) =
		(HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslDisjunctionS)
			) +++
			(foldl (\forms f ->
				forms +++
				processFormula imports sorts preds ops name f
				) (xmlNL) fl)
		) ) +++
		xmlNL
-- Implication
processFormula imports sorts preds ops name
	(Implication f1 f2 b _) =
		( HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslImplicationS)
			) +++
			(xmlNL) +++
			(processFormula imports sorts preds ops name f1) +++
			(processFormula imports sorts preds ops name f2) +++
			(processFormula imports sorts preds ops name
				(if b then True_atom Id.nullRange else False_atom Id.nullRange))
		) ) +++
		xmlNL
-- Equivalence
processFormula imports sorts preds ops name
	(Equivalence f1 f2 _) =
		( HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslEquivalenceS)
			) +++
			(xmlNL) +++
			(processFormula imports sorts preds ops name f1) +++
			(processFormula imports sorts preds ops name f2)
		) ) +++
		xmlNL
-- Negation
processFormula imports sorts preds ops name
	(Negation f _) =
		( HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslNegationS)
			) +++
			(xmlNL) +++
			(processFormula imports sorts preds ops name f)
		) ) +++
		xmlNL
-- Predication
processFormula imports sorts preds ops name
	(Predication p tl _) =
		(HXT.etag "OMA" += (
			xmlNL +++
			(HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslPredicationS)
			) +++
			xmlNL +++
			(xmlNL) +++
			(createSymbolForPredication imports preds name p) +++
			(foldl (\term t ->
				term +++
				(processTerm imports sorts preds ops name t) +++
				xmlNL
				) (HXT.txt "") tl
			) +++
			(xmlNL)
		) ) +++
		xmlNL
-- Definedness
processFormula imports sorts preds ops name
	(Definedness t _ ) =
		(HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslDefinednessS)
			) +++
			(xmlNL) +++
			(processTerm imports sorts preds ops name t)
		) ) +++
		xmlNL
-- Existl_equation
processFormula imports sorts preds ops name
	(Existl_equation t1 t2 _) = 
		( HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslExistl_equationS)
			) +++
			(xmlNL) +++
			(processTerm imports sorts preds ops name t1) +++
			(processTerm imports sorts preds ops name t2)
		) ) +++
		xmlNL
-- Strong_equation
processFormula imports sorts preds ops name
	(Strong_equation t1 t2 _) = 
		( HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslStrong_equationS)
			) +++
			(xmlNL) +++
			(processTerm imports sorts preds ops name t1) +++
			(processTerm imports sorts preds ops name t2)
		) ) +++
		xmlNL
-- Membership
processFormula imports sorts preds ops name
	(Membership t s _) = 
		( HXT.etag "OMA" += (
			xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslMembershipS)
			) +++
			(xmlNL) +++
			(processTerm imports sorts preds ops name t) +++
			(createSymbolForSort imports sorts s name)
		) ) +++
		xmlNL
-- False_atom
processFormula imports sorts preds ops name
	(False_atom _) =
		(HXT.etag "OMS" +=
			(HXT.sattr "cd" caslS +++
			HXT.sattr "name" caslSymbolAtomFalseS)
		) +++
		xmlNL
-- True_atom
processFormula imports sorts preds ops name
	(True_atom _) =
		(HXT.etag "OMS" +=
			(HXT.sattr "cd" caslS +++
			HXT.sattr "name" caslSymbolAtomTrueS)
		) +++
		xmlNL
-- Sort_gen_ax
processFormula imports sorts preds ops name
	(Sort_gen_ax constraints freetype) =
		( HXT.etag "OMA" +=
			(xmlNL +++
			( HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" caslSort_gen_axS)
			) +++
			(xmlNL) +++
			(HXT.etag "OMBVAR" +=
				( xmlNL +++
				(processConstraints imports ops name constraints)
				)
			) +++
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
processFormula imports sorts preds ops name
	(Mixfix_formula _) =
		HXT.etag unsupportedS +++
		HXT.txt ( "<-- " ++ "Mixfix_formula" ++ " //-->")
-- Unparsed_formula
processFormula imports sorts preds ops name
	(Unparsed_formula s _) =
		HXT.etag unsupportedS +++
		HXT.txt ( "<-- " ++ "Unparsed_formula \"" ++ s ++ "\" //-->")
-- ExtFORMULA
processFormula imports sorts preds ops name
	(ExtFORMULA _) =
		HXT.etag unsupportedS +++
		HXT.txt ( "<-- " ++ "ExtFORMULA" ++ " //-->") 

-- | create an xml-representation for a predication
createSymbolForPredication::
	Hets.ImportsMap-> -- ^ the map of imports
	Hets.PredsMap-> -- ^ the map of predication
	String-> -- ^ the name of the current theory
	PRED_SYMB-> -- ^ the predication to process
	(XmlTree->XmlTrees) -- ^ a xml-representation of the predication
-- Pred_name
createSymbolForPredication imports preds name
	(Pred_name pr) =
		HXT.etag "OMS" +=
			(HXT.sattr "cd" (fromMaybe "unknown" $
				Hets.findNodeNameForPredication imports preds pr name) +++
			HXT.sattr "name" (show pr)
			)
-- Qual_pred_name
createSymbolForPredication imports preds name
	operator@(Qual_pred_name pr pt@(Pred_type args _) _) =
		HXT.etag "OMATTR" +=
			(xmlNL +++
			HXT.etag "OMATP" +=
				(xmlNL +++
				HXT.etag "OMS" +=
					(HXT.sattr "cd" "casl" +++ HXT.sattr "name" "type") +++
				xmlNL +++
				(HXT.etag "OMSTR" +=
					HXT.txt
						( (foldl
							(\t s -> t ++ "-\\" ++ (show s))
							(if args == [] then "" else (show $ head args))
							(drop 1 args)
						   )
						)
				)
				) +++
				xmlNL
			) +++
		xmlNL +++
		HXT.etag "OMS" +=
			( HXT.sattr "cd" ( fromMaybe "unknown" $
				Hets.findNodeNameForPredicationWithSorts
					imports	
					preds
					(pr, cv_Pred_typeToPredType pt)
					name) +++
			HXT.sattr "name" (show pr)
			) 

--data QUANTIFIER = Universal | Existential | Unique_existential
-- Quantifier as CASL Symbol
quantName :: QUANTIFIER->String
quantName Universal = caslSymbolQuantUniversalS
quantName Existential = caslSymbolQuantExistentialS
quantName Unique_existential = caslSymbolQuantUnique_existentialS

processConstraints::Hets.ImportsMap->Hets.OpsMap->String->[ABC.Constraint]->(HXT.XmlTree->HXT.XmlTrees)
processConstraints _ _ _ [] = HXT.txt ""
processConstraints importsmap opsmap name ((ABC.Constraint news ops origs):rest) =
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
					+++ processOperator importsmap opsmap name op
					) ) +++ xmlNL
				) (HXT.txt "") ops
			) )
		+++ xmlNL
		+++ (HXT.etag "OMS" += (HXT.sattr "cd" caslS +++ HXT.sattr "name" (show origs))))) +++ xmlNL

pairsToWhatIWant::Eq a=>[(a,a)]->[(a,[a])]
pairsToWhatIWant = foldl (\i x -> insert x i) [] where 
	insert::(Eq a, Eq b)=>(a,b)->[(a,[b])]->[(a,[b])]
	insert (a,b) [] = [(a,[b])]
	insert (a,b) ((a' ,l):r) = if a == a' then (a' , l++[b]):r else (a', l): insert (a,b) r
	
isTrueAtom::(FORMULA ())->Bool
isTrueAtom (True_atom _) = True
isTrueAtom _ = False

-- X M L -> FORMULA

unwrapFormulas::FormulaContext->HXT.XmlTrees->[(Ann.Named CASLFORMULA)]
unwrapFormulas fc t = map (\t -> unwrapFormula fc [t]) $ ((applyXmlFilter (isTag "axiom") t)::[XmlTree])

adjustFormulaName::String->String
adjustFormulaName s =
	if isPrefixOf "AnonAx" s then "" else
		s

data FormulaContext = FC {
	 imports :: Hets.ImportsMap
	,sorts :: Hets.SortsMap
	,rels :: Hets.RelsMap
	,preds :: Hets.PredsMap
	,ops :: Hets.OpsMap
	,currentName :: String
	}
	
emptyFormulaContext = FC Map.empty Map.empty Map.empty Map.empty Map.empty ""
		
unwrapFormula::FormulaContext->HXT.XmlTrees->(Ann.Named CASLFORMULA)
unwrapFormula fc t =
	let
		name = xshow $ applyXmlFilter (getQualValue "xml" "id") t
		formtree = applyXmlFilter (getChildren .> isTag "FMP" .> getChildren .> isTag "OMOBJ" .> getChildren) t
	in
		Ann.NamedSen (adjustFormulaName name) True (formulaFromXml fc formtree)

		  

formulaFromXml::FormulaContext->(HXT.XmlTrees)->(FORMULA ())
formulaFromXml fc t = if (applyXmlFilter (isTag "OMBIND") t) /= [] then -- it's a quantifier...
			let	quantTree = [head ((applyXmlFilter (isTag "OMBIND") t)::[XmlTree])]
				quant = quantFromName $ xshow $ applyXmlFilter (getChildren .> isTag "OMS" .> withSValue "cd" caslS .> getValue "name") quantTree
				-- first element is the quantification-OMS
				formula = drop 1 ((applyXmlFilter (getChildren .> (isTag "OMA" +++ isTag "OMATTR" +++ isTag "OMBIND" +++ isTag "OMS")) quantTree)::[XmlTree]) 
				vardeclS = getVarDecls (applyXmlFilter (getChildren .> isTag "OMBVAR") quantTree)
				vardeclS2 = pairsToWhatIWant vardeclS
			in
				Quantification quant (map (\(s, vl) -> Var_decl (map Hets.stringToSimpleId vl) (Hets.stringToId s) Id.nullRange) vardeclS2) (formulaFromXml fc formula) Id.nullRange
			else if (applyXmlFilter (isTag "OMA") t) /= [] then -- the case begins...
			  let
			  	formTree = applyXmlFilter (isTag "OMA") t
				applySym = xshow $ applyXmlFilter (getValue "name") [head (applyXmlFilter (getChildren .> isTag "OMS") formTree)]
				applySymCD = xshow $ applyXmlFilter (getValue "cd") [head (applyXmlFilter (getChildren .> isTag "OMS") formTree)]
			  in
				let	formulas = map (\t -> formulaFromXml fc [t]) ((applyXmlFilter (getChildren .> (isTag "OMA" +++ isTag "OMATTR" +++ isTag "OMBIND")) formTree)::[XmlTree])
					terms = map (\t -> termFromXml fc [t]) ((applyXmlFilter (getChildren .> (isTag "OMV" +++ isTag "OMATTR" +++ isTag "OMA")) formTree)::[XmlTree])
				in
				-- 'case applySym' does not work if case-strings are non fixed (above definition is not fixed enough...) 
			  	--case applySym of
					if applySym == caslConjunctionS then
						Conjunction formulas Id.nullRange
					else
					if applySym == caslDisjunctionS then
						Disjunction formulas Id.nullRange
					else
					if applySym `elem` [caslImplicationS, caslImplication2S] then
						let boolF = formulaFromXml fc [((applyXmlFilter (getChildren .> isTag "OMS") formTree)::[XmlTree])!!1] 
						in
						Implication (formulas!!0) (formulas!!1) (isTrueAtom(boolF)) Id.nullRange
					else
					if applySym `elem` [caslEquivalenceS, caslEquivalence2S] then
						Equivalence (formulas!!0) (formulas!!1) Id.nullRange
					else
					if applySym == caslNegationS then
						Negation (formulas!!0) Id.nullRange
					else
					if applySym == caslPredicationS then --- ! ! ! ! !
						let	pred = predicationFromXml $ [head $ tail $ applyXmlFilter (getChildren .> (isTag "OMS" +++ isTag "OMATTR")) t]
							predterms = map (\t -> termFromXml fc [t]) $ tail $ ((applyXmlFilter (getChildren .> (isTag "OMATTR" +++ isTag "OMA")) t)::[XmlTree])
						in
						Predication pred predterms Id.nullRange 
					else
					if applySym == caslDefinednessS then
						Definedness (termFromXml fc (applyXmlFilter (getChildren .> (isTag "OMV" +++ isTag "OMATTR" +++ isTag "OMA" )) t)) Id.nullRange
					else
					if applySym == caslExistl_equationS then
						Existl_equation (terms!!0) (terms!!1) Id.nullRange
					else
					if applySym == caslStrong_equationS then
						Strong_equation (terms!!0) (terms!!1) Id.nullRange
					else
					if applySym == caslMembershipS then
						let	sort = xshow $ [last $ ((applyXmlFilter (getChildren .> isTag "OMS" .> getValue "name") formTree)::[XmlTree])]
						in
						Membership (head terms) (Hets.stringToId sort) Id.nullRange
					else
					if applySym == caslSort_gen_axS then
						let	freeType = if (xshow $ applyXmlFilter (getValue "name") [(applyXmlFilter (getChildren .> isTag "OMS") formTree)!!1]) == caslSymbolAtomFalseS then False else True
							constraintsx = applyXmlFilter (getChildren .> isTag "OMBVAR" .> getChildren .> isTag "OMBIND") formTree
							constraints = xmlToConstraints constraintsx
						in
						Sort_gen_ax constraints freeType
					else
--					if applySym /= [] then
						Debug.Trace.trace ("No matching casl-application found! Trying to find predicate...") $
							let
								-- try to find the node for this predicate
								mprednodename = Hets.findNodeNameForPredication (imports fc) (preds fc) (Hets.stringToId applySym) (currentName fc)
								predsMap = case mprednodename of
									-- try to get predicate set via CD
									Nothing -> Map.findWithDefault (Debug.Trace.trace ("No Node found by CD...") Map.empty) applySymCD (preds fc)
									-- try to get predicate map from the node
									(Just prednodename) -> Map.findWithDefault (Debug.Trace.trace ("Node should contain predicate, but does not...") Map.empty) prednodename (preds fc)
								-- try to find the predicate set from the map
								mptset = Map.lookup (Hets.stringToId applySym) predsMap :: (Maybe (Set.Set PredType))
								-- terms to apply predication to...
								predterms = map (\t -> termFromXml fc [t]) $ tail $ ((applyXmlFilter (getChildren .> (isTag "OMATTR" +++ isTag "OMA")) t)::[XmlTree])
							in
								case mptset of
									Nothing -> error ("Could not find Predication for \"" ++ applySym ++ "\" from \"" ++ applySymCD ++ "\"")
									(Just ptset) ->
										if Set.null ptset
											then
												error ("Found mapping for predication \"" ++ applySym ++ "\" but no actual values... this is odd!")
											else
												Predication (Qual_pred_name (Hets.stringToId applySym) (cv_PredTypeToPred_type $ head $ Set.toList ptset) Id.nullRange) predterms Id.nullRange
--					else
--						error ("Expected a casl application symbol, but \"" ++ applySym ++ "\" was found!")
			  else if (applyXmlFilter (isTag "OMS") t) /= [] then
			  	let trueOrFalse = xshow $ [((applyXmlFilter (isTag "OMS" .> withSValue "cd" caslS .> getValue "name") t)::[XmlTree])!!0]
				in
				if trueOrFalse == caslSymbolAtomTrueS then
					True_atom Id.nullRange
					else
						if trueOrFalse == caslSymbolAtomFalseS then
							False_atom Id.nullRange
							else error (caslSymbolAtomTrueS ++ " or " ++ caslSymbolAtomFalseS ++ " expected, but \"" ++ trueOrFalse ++ "\" found!")
			  else
			  	error ("Impossible to create formula from \"" ++ xshow t++ "\"") 



xmlToConstraints::HXT.XmlTrees->[ABC.Constraint]
xmlToConstraints t =
	map (\t -> xmlToConstraint [t]) $ ((applyXmlFilter (isTag "OMBIND") t)::[XmlTree])
	
xmlToConstraint::HXT.XmlTrees->ABC.Constraint
xmlToConstraint t =
	let 	sortsx = applyXmlFilter (getChildren .> isTag "OMS" .> getValue "name") t
		newsort = Hets.stringToId $ xshow $ [sortsx!!0]
		origsort = Hets.stringToId $ xshow $ [sortsx!!0]
		indiopsx = applyXmlFilter (getChildren .> isTag "OMBVAR" .> getChildren .> isTag "OMATTR") t
		conslist = foldl (\cl cx ->
				let	indices = xshow $ applyXmlFilter (getChildren .> isTag "OMATP" .> getChildren .> isTag "OMSTR" .> getChildren) [cx]
					op = operatorFromXml $ applyXmlFilter (getChildren .> (isTag "OMBIND" +++ isTag "OMS")) [cx]
					il = makeIndexList indices
				in
					cl ++ [(op, il)]
				) ([]::[(OP_SYMB,[Int])]) (indiopsx::[XmlTree])
	in
		ABC.Constraint newsort conslist origsort

-- An IndexList is constructed from a String like 'n1|n2|n3...nk|' 		
makeIndexList::String->[Int]
makeIndexList [] = []
makeIndexList s = let (number, rest) = (takeWhile (\x -> x /= '|') s, dropWhile (\x -> x /= '|') s)
		  in [read number] ++ (makeIndexList (drop 1 rest))


predicationFromXml::XmlTrees->PRED_SYMB
predicationFromXml t =
	let	signature =
			if (applyXmlFilter (isTag "OMATTR") t) /= [] then
				xshow $ applyXmlFilter (
					getChildren .> isTag "OMATP" .>
					getChildren .> isTag "OMSTR" .>
					getChildren ) t
			else
				""
		types = explode "-\\" signature
		prtype = Pred_type (map Hets.stringToId types) Id.nullRange
		symbolXml = if signature == "" then
						applyXmlFilter (isTag "OMS") t
						else
						applyXmlFilter (
							isTag "OMATTR" .>
							getChildren .> isTag "OMS"
							) t
		from = xshow $ applyXmlFilter (getValue "cd") symbolXml
		name = xshow $ applyXmlFilter (getValue "name") symbolXml
	in
	if signature == [] then
		Pred_name $ Hets.stringToId name
	else
		Qual_pred_name (Hets.stringToId name) prtype Id.nullRange
						

-- String to Quantifiert...
quantFromName::String->QUANTIFIER
quantFromName caslSymbolQuantUniversalS = Universal
quantFromName caslSymbolQuantExistentialS = Existential
quantFromName caslSymbolQuantUnique_existentialS = Unique_existential
quantFromName s = error (s++": no such quantifier...")

funKindFromName::String->FunKind
funKindFromName "Total" = Total
funKindFromName "Partial" = Total
funKindFromName s = error ("No such function kind... \""++ s ++"\"")


-- first newline needs pulling up because we have a list of lists...
processVarDecl :: Hets.ImportsMap-> Hets.SortsMap-> String -> [VAR_DECL] -> (HXT.XmlTree->HXT.XmlTrees)
processVarDecl imports sorts name vdl = (HXT.etag "OMBVAR" += (xmlNL +++ (processVarDecls imports sorts name vdl)) ) +++ xmlNL where
	processVarDecls :: Hets.ImportsMap-> Hets.SortsMap-> String ->[VAR_DECL] -> (HXT.XmlTree->HXT.XmlTrees)
	processVarDecls imports sorts name [] = HXT.txt ""
	processVarDecls imports sorts name ((Var_decl vl s _):vdl) = (foldl (\decls vd -> decls +++
	-- <ombattr><omatp><oms>+</omatp><omv></ombattr>
		( createTypedVar imports sorts s name (show vd) )
			+++ xmlNL)
			(HXT.txt "") vl ) -- end fold
			+++ (processVarDecls imports sorts name vdl)
	
-- get var decls
getVarDecls::XmlTrees->[(String, String)]
getVarDecls vt = map (\t ->
		(xshow $ applyXmlFilter (getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" (/=typeS) .> getValue "name") [t],
		 xshow $ applyXmlFilter (getChildren .> isTag "OMV" .> getValue "name") [t]) ) ((applyXmlFilter (isTag "OMBVAR" .> getChildren .> isTag "OMATTR") vt)::[XmlTree])

createATP::Hets.ImportsMap->Hets.SortsMap->SORT->String->(XmlTree->XmlTrees)
createATP imports sorts sort name =
	etag "OMATP" +=
		((etag "OMS" += ( sattr "cd" caslS +++ sattr "name" typeS ) )
		 +++ createSymbolForSort imports sorts sort name
		 )
		 
createTypedVar::Hets.ImportsMap->Hets.SortsMap->SORT->String->String->(XmlTree->XmlTrees)
createTypedVar imports sorts sort name varname =
	etag "OMATTR" += ( (createATP imports sorts sort name) +++ (etag "OMV" += (sattr "name" varname) ) )
	
-- | create a xml-representation from a term (in context of a theory)
processTerm::
	Hets.ImportsMap-> -- ^ the imports-map
	Hets.SortsMap-> -- ^ the sorts-map
	Hets.PredsMap-> -- ^ the map of predicates
	Hets.OpsMap-> -- ^ the map of operators
	String-> -- ^ the name of the current theory
	(TERM f)-> -- ^ the term to process
	(HXT.XmlTree->HXT.XmlTrees) -- ^ xml-representation of the term
-- Simple_id
processTerm imports sorts preds ops name
	(Simple_id id) =
		HXT.etag "OMV" +=
			HXT.sattr "name" (show id) -- not needed
-- Qual_var
processTerm imports sorts preds ops name
	(Qual_var v s _) =
		( createTypedVar imports sorts s name (show v) ) +++
		xmlNL
-- Application
processTerm imports sorts preds ops name
	(Application op termlist _) =
		(etag "OMA" +=
			(xmlNL +++
			( processOperator imports ops name op ) +++
			(foldl (\terms t ->
				terms +++
				(processTerm imports sorts preds ops name t)
				) (HXT.txt "") termlist
			)
			) ) +++
			xmlNL
-- Cast
processTerm imports sorts preds ops name
	(Cast t s _) =
		processTerm imports sorts preds ops name
			(Application
				(Op_name $ Hets.stringToId "PROJ")
				[t, (Simple_id $ Id.mkSimpleId (show s))]
				Id.nullRange
			)
-- Conditional
processTerm imports sorts preds ops name
	(Conditional t1 f t2 _) =
		HXT.etag "OMA" +=
			(xmlNL +++
			(HXT.etag "OMS" +=
				(HXT.sattr "cd" caslS +++
				HXT.sattr "name" "IfThenElse"
				)
			) +++
			(processFormula imports sorts preds ops name f) +++
			(processTerm imports sorts preds ops name t1) +++
			(processTerm imports sorts preds ops name t2)
			)
-- Sorted_term is to be ignored in OMDoc (but could be modelled...) (Sample/Simple.casl uses it...)
processTerm imports sorts preds ops name
	(Sorted_term t s _) =
		processTerm imports sorts preds ops name t


isTermXml::XmlFilter
isTermXml = isTag "OMV" +++ isTag "OMATTR" +++ isTag "OMA"

isOperatorXml::XmlFilter
isOperatorXml = isTag "OMATTR" +++ isTag "OMS"

isTermOrOpXml::XmlFilter
isTermOrOpXml = isTermXml +++ isTag "OMS" -- never ever use double tags or get double results...

termFromXml::FormulaContext->XmlTrees->(TERM ())
termFromXml fc t = if (applyXmlFilter (isTag "OMV") t) /= [] then
			Simple_id $ Hets.stringToSimpleId $ xshow $ applyXmlFilter (isTag "OMV" .> getValue "name") t
		else
		if (applyXmlFilter (isTag "OMATTR") t) /= [] then
			Qual_var
				(Hets.stringToSimpleId $ xshow $ applyXmlFilter (isTag "OMATTR" .> getChildren .> isTag "OMV" .> getValue "name") t)
				(Hets.stringToId $ xshow $ applyXmlFilter (isTag "OMATTR" .> getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" (/=typeS) .> getValue "name") t)
				Id.nullRange
		else
		if (applyXmlFilter (isTag "OMA") t ) /= [] then
			let operator = operatorFromXml [head $ applyXmlFilter (getChildren .> isOperatorXml) t]
			    terms = map (\t -> termFromXml fc [t]) $
					applyXmlFilter isTermXml $
					drop 1 $ -- drop out operator
					applyXmlFilter (getChildren .> isTermOrOpXml) t
			in
			if (opName operator) == "PROJ" then
				Cast (head terms) (Hets.stringToId $ show (head $ tail terms)) Id.nullRange
			else
			if (opName operator) == "IfThenElse" then
				let	formula = formulaFromXml fc [head ((applyXmlFilter (getChildren .> (isTag "OMA" +++ isTag "OMBIND")) t)::[XmlTree])]
				in 
				Conditional (head terms) formula (head $ tail terms) Id.nullRange 
			else
				Application operator terms Id.nullRange
		else
			error ("Impossible to create term from \"" ++ xshow t++"\"") 

			
cv_Op_typeToOpType::OP_TYPE->OpType
cv_Op_typeToOpType (Op_type fk args res _) = OpType fk args res

cv_OpTypeToOp_type::OpType->OP_TYPE
cv_OpTypeToOp_type (OpType fk args res) = Op_type fk args res Id.nullRange

cv_Pred_typeToPredType::PRED_TYPE->PredType
cv_Pred_typeToPredType (Pred_type args _) = PredType args

cv_PredTypeToPred_type::PredType->PRED_TYPE
cv_PredTypeToPred_type (PredType args) = Pred_type args Id.nullRange


-- | create a xml-representation of an operator (in context of a theory)
processOperator::
	Hets.ImportsMap-> -- ^ the map of imports
	Hets.OpsMap-> -- ^ the map of operators
	String-> -- ^ the name of the current theory
	OP_SYMB-> -- ^ the operator to process
	(XmlTree->XmlTrees) -- ^ the xml-representation of the operator
-- Op_name
processOperator imports ops name
	(Op_name op) =
		HXT.etag "OMS" +=
			(HXT.sattr "cd" 
				(fromMaybe "unknown" $
					Hets.findNodeNameForOperator imports ops op name) +++
				HXT.sattr "name" (show op)
			)
-- Qual_op_name
processOperator imports ops name
	operator@(Qual_op_name op ot@(Op_type fk args res _) _) =
		HXT.etag "OMATTR" +=
			(xmlNL +++
			HXT.etag "OMATP" += -- create attribution for this operator (sign)
				(xmlNL +++
				HXT.etag "OMS" += -- type of operator
					(HXT.sattr "cd" "casl" +++
					HXT.sattr "name" "funtype"
					) +++
				xmlNL +++
				(HXT.etag "OMSTR" +=
					(HXT.txt (show fk)) -- 'Partial' or 'Total'
				) +++
				xmlNL +++
				HXT.etag "OMS" += -- signature of operator
					(HXT.sattr "cd" "casl" +++
					HXT.sattr "name" "type"
					) +++
				xmlNL +++
				(HXT.etag "OMSTR" += -- create a string t1-\\t2-\\...-\\tn
					(HXT.txt ( (foldl
						(\t s -> t ++ (show s) ++ "-\\")
						-- the function could be easier but we need different
						-- behaviour for functions without parameters...
						(if (length args > 0) then
								(show (head args)) ++ "-\\"
							else
								"" )
						(if (length args) > 0 then tail args else [])
						) ++ (show res) )
					)
				) +++
				xmlNL
				) +++
				xmlNL +++
				HXT.etag "OMS" += -- finally : the name of the operator
					( HXT.sattr "cd"
						( fromMaybe "unknown" $
							Hets.findNodeNameForOperatorWithSorts
								imports
								ops
								(op, cv_Op_typeToOpType ot) name
						) +++
						HXT.sattr "name" (show op)
					)
			)
		

-- explode byWhat list
-- TODO : this looks very slow...
explode::Eq a=>[a]->[a]->[[a]]
explode by list =
	(\(p,q) -> p++[q]) $ foldl (\(exploded, current) newchar ->
		let newcurrent = current ++ [newchar]
		in
		if isSuffixOf by newcurrent then
			(exploded ++ [ take ((length newcurrent)-length(by)) newcurrent ], [])
		else
			(exploded, newcurrent)
			) ([],[]) list


-- this function takes care of fetching the function-type information from an 
-- OMATTR-Tree (defaulting to Total but raising exception on 'explicit-wrong' type
-- usually the 'skipping-part' will not have to skip over many items (1-2) 
getFunKind::XmlTrees->FunKind
getFunKind t =
	if (applyXmlFilter (isTag "OMATTR") t) /= [] then
		(\ (a,_,_) -> a ) $ foldl (\(fk, found, skip) tc ->
			if skip then (fk, found, skip)
			else
				if not found then
					if (applyXmlFilter (isTag "OMS" .> withSValue "name" "funtype") [tc]) /= [] then
						(fk, True, skip)
					else
						(fk, found, skip)
				else
					if (applyXmlFilter (isTag "OMSTR") [tc]) /= [] then
						(funKindFromName $ xshow $ applyXmlFilter (getChildren) [tc], True, True)
					else
						(fk, found, skip)
					) (Total, False, False) $ applyXmlFilter (getChildren .> isTag "OMATP" .> getChildren) t
	else
		Total

-- fetches signature from XML (see getFunKind)		
getSignature::XmlTrees->([SORT], SORT)
getSignature t =
	if (applyXmlFilter (isTag "OMATTR") t) /= [] then
		(\ (a,_,_) -> a ) $ foldl (\(sig, found, skip) tc ->
			if skip then (sig, found, skip)
			else
				if not found then
					if (applyXmlFilter (isTag "OMS" .> withSValue "name" "type") [tc]) /= [] then
						(sig, True, skip)
					else
						(sig, found, skip)
				else
					if (applyXmlFilter (isTag "OMSTR") [tc]) /= [] then
						let args = map Hets.stringToId $ explode "-\\" $ xshow $ applyXmlFilter (getChildren) [tc]
						in
						((init args, last args), True, True)
					else
						(sig, found, skip)
					) (([],Hets.stringToId ""), False, False) $ applyXmlFilter (getChildren .> isTag "OMATP" .> getChildren) t
	else
		([], Hets.stringToId "")


operatorFromXml::XmlTrees->OP_SYMB
operatorFromXml t =
	let	funkind = getFunKind t
		(sig,res) = getSignature t
		optype = Op_type funkind sig res Id.nullRange
		symbolXml = if (res == (Hets.stringToId "")) then
						applyXmlFilter (isTag "OMS") t
						else
						applyXmlFilter (
							isTag "OMATTR" .>
							getChildren .> isTag "OMS"
							) t
		from = xshow $ applyXmlFilter (getValue "cd") symbolXml
		name = xshow $ applyXmlFilter (getValue "name") symbolXml
	in
	if (res == (Hets.stringToId "")) then
		Op_name $ Hets.stringToId name
	else
		Qual_op_name (Hets.stringToId name) optype Id.nullRange
		
getSorts::XmlTrees->[String]
getSorts st = map (\t -> xshow $ applyXmlFilter (getValue "name") [t]) ((applyXmlFilter (getChildren .> isTag "OMATP" .> getChildren .> isTag "OMS" .> withValue "name" (/=typeS)) st)::[XmlTree])

opName::OP_SYMB->String
opName (Op_name op) = (show op)
opName (Qual_op_name op _ _) = (show op)


