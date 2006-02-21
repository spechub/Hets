{- |
Stolen from HetCATS/hets.hs
Interface for accessing Hets-System
-}

module HetsInterface (module HetsInterface, module Driver.ReadFn, module Driver.WriteFn, module Static.AnalysisLibrary) where

import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Graph as Graph --

import Common.AS_Annotation
import Common.GlobalAnnotations (emptyGlobalAnnos)

import Syntax.AS_Library --(LIB_NAME(),LIB_DEFN()) 

import Driver.ReadFn
import Driver.WriteFn
import Driver.Options

import Logic.Grothendieck hiding (Morphism)

import Static.AnalysisLibrary
import Static.DevGraph
import Static.PrintDevGraph()

import CASL.AS_Basic_CASL
import CASL.Logic_CASL

import CASL.Sign
import CASL.Morphism
import qualified CASL.AS_Basic_CASL as CASLBasic
import Data.Typeable
import qualified Common.Id as Id
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Rel as Rel
import qualified Logic.Grothendieck as Gro
import qualified Common.AS_Annotation as Ann
import qualified Data.Maybe as Data.Maybe

import qualified GUI.ShowGraph as GUI

import qualified Logic.Prover as Prover

import qualified Common.OrderedMap as OMap

import qualified Debug.Trace as Debug.Trace

import qualified Data.List as Data.List

dtt::String->a->a
dtt = Debug.Trace.trace

showGraph::FilePath->HetcatsOpts->Maybe (LIB_NAME, LibEnv)->IO ()
showGraph file opt env =
	case env of
		Just (ln, libenv) -> do
			GUI.showGraph file opt (Just (ln, libenv))
		Nothing -> return ()

run :: FilePath -> IO (Maybe (LIB_NAME, LibEnv))
run file = anaLib dho file

runLib::FilePath->FilePath->IO (Maybe (LIB_NAME, LibEnv))
runLib lib file = anaLib (dho { libdir = lib }) file

dho::HetcatsOpts
dho = defaultHetcatsOpts

-- isAxiom was added... (a :: Bool)
transSen::[Ann.Named CASLFORMULA]->[(String, CASLFORMULA)]
transSen [] = []
transSen ((Ann.NamedSen n _ _ s):rest) = [(n, s)] ++ transSen rest

transSenBack::[(String, CASLFORMULA)]->[Ann.Named CASLFORMULA]
transSenBack [] = []
transSenBack ((n, s):rest) = (Ann.NamedSen n False False s):(transSenBack rest)

getPureFormulas::[(String, CASLFORMULA)]->[CASLFORMULA]
getPureFormulas [] = []
getPureFormulas ((_, f):rest) = [f] ++ getPureFormulas rest

getDG::FilePath->IO DGraph
getDG f = do
	(Just (ln,lenv)) <- run f
	case Map.lookup ln lenv of
		Nothing -> error "Error looking op DGraph"
		(Just gc) -> return $ devGraph gc

-- Cast Signature to CASLSignature if possible
getCASLSign::G_sign->(Maybe CASLSign)
getCASLSign (G_sign _ sign) = cast sign -- sign is of class Typeable -> cast -> (Typeable a, Typeable b)->(Maybe b)

getJustCASLSign::(Maybe CASLSign)->CASLSign
getJustCASLSign (Just cs) = cs
getJustCASLSign Nothing = error "Nothing"

-- Get a String-representation of a Set
getSetStringList::(Show a)=>Set.Set a -> [String]
getSetStringList s = map show $ Set.toList s

-- " of a Map
getMapStringsList::(Show a, Show b)=>Map.Map a b -> [(String, String)]
getMapStringsList s = map (\(a, b) -> (show a, show b)) $ Map.toList s

-- " of a Relation
getRelStringsList::(Show a)=>Rel.Rel a -> [(String, String)]
getRelStringsList s = map (\(a, b) -> (show a, show b)) $ Rel.toList s

-- Get strings to represent an operator-mapping
getOpMapStringsList::OpMap->[(String, [(String, [String], String)])]
getOpMapStringsList om = map (\(a, b) -> ((show a), map opTypeToStrings (Set.toList b))) (Map.toList om) where
	opTypeToStrings::OpType->(String, [String], String)
	opTypeToStrings (OpType {opKind=ok, opArgs=oa, opRes=or' }) = (show ok, map show oa, show or' )
	
-- Get strings to represent a predicate-mapping
getPredTypeStringsList::(Map.Map (Id.Id) (Set.Set PredType))->[(String, [[String]])]
getPredTypeStringsList pm = map (\(id' , pts) -> (show id' ,
					map (\(PredType set) -> map show set) $ Set.toList pts ) ) $ Map.toList pm

-- String representation of non ignored CASLSign-Components					
data CASLSignStrings = CASLSignStrings {
			 sortSetStrings :: [String]
			,sortRelStrings :: [(String, String)]
			,opMapStrings :: [(String, [(String, [String], String)])]
			,predMapStrings :: [(String, [[String]])]
			} deriving Show

-- Conversion from Sign to Stringrepresentation
caslSignToStrings::CASLSign->CASLSignStrings
caslSignToStrings cs =
	CASLSignStrings	{  sortSetStrings=( getSetStringList $ sortSet cs )
			  ,sortRelStrings=( getRelStringsList $ sortRel cs)
			  ,opMapStrings = ( getOpMapStringsList $ opMap cs)
			  ,predMapStrings = ( getPredTypeStringsList $ predMap cs )
			 }

stringToSimpleId::String->Id.SIMPLE_ID
stringToSimpleId = Id.mkSimpleId
			 
-- Fast Id construction from a String
stringToId::String->Id.Id
stringToId = Id.simpleIdToId . Id.mkSimpleId

-- SORT is Id so hopefully this simple mapping does it...
sortSetStringsToSortSet::[String]->(Set.Set Id.Id)
sortSetStringsToSortSet sorts = Set.fromList $ map stringToId sorts

-- Same for Relations
sortRelStringsToSortRel::[(String, String)]->(Rel.Rel Id.Id)
sortRelStringsToSortRel l = Rel.fromList $ map (\(a, b) -> ((stringToId a), (stringToId b))) l

{-
This might be a source of later errors.
FunKinds are checked against a String... needs more work.
-}
opMapStringsToOpMap::[(String, [(String, [String], String)])]->OpMap
opMapStringsToOpMap ops = foldr (\(id' , ops' ) m -> Map.insert (stringToId id' ) (Set.fromList $ map mkOpType ops' ) m) Map.empty ops where  
	mkOpType::(String,[String],String)->OpType
	mkOpType (opkind, args, res) = OpType
					(if opkind == "Partial" then CASLBasic.Partial else CASLBasic.Total)
					(map stringToId args)
					(stringToId res)

{-
Predicate-mapping
-}
predMapStringsToPredMap::[(String, [[String]])]->(Map.Map Id.Id (Set.Set PredType))
predMapStringsToPredMap pres = foldr (\(id' , args) m -> Map.insert
							(stringToId id' )
							(Set.fromList $ map (\n -> PredType (map (\s -> stringToId s) n)) args)
							m
						) Map.empty pres

-- Conversion from String-Form to Sign
stringsToCASLSign::CASLSignStrings->CASLSign
stringsToCASLSign cs =
	Sign {
		 sortSet = sortSetStringsToSortSet $ sortSetStrings cs
		,sortRel = sortRelStringsToSortRel $ sortRelStrings cs
		,opMap = opMapStringsToOpMap $ opMapStrings cs
		,assocOps = Map.empty -- ignored
		,predMap = predMapStringsToPredMap $ predMapStrings cs
		,varMap = Map.empty -- ignored
		,sentences = [] -- ignored
		,envDiags = [] -- ignored
		,globAnnos = emptyGlobalAnnos
		,extendedInfo = () -- ignored
	}


-- Filter out links for collecting sorts, rels, preds...
-- only four types of links are allowed (and afaik needed for this)
linkFilter::[(Graph.LEdge DGLinkLab)]->[(Graph.LEdge DGLinkLab)]
linkFilter [] = []
linkFilter ((l@(_,_,link)):rest) =
	(case dgl_type link of
		LocalDef -> [l]
		GlobalDef -> [l]
		-- LocalThm's with 'Mono' cons tend to link back to their 
		-- origin, effectively wiping out the sorts, etc...
		(LocalThm _ c _) -> case c of Def -> [l]; _ -> []
		(GlobalThm _ c _) -> case c of Def -> [l]; _ -> []
		_ -> []) ++ linkFilter rest
		
-- return a list with all NodeLabs where imports a made (see also 'linkFilter')
inputNodeLabs::DGraph->Graph.Node->[DGNodeLab]
inputNodeLabs dg n = map (\(Just a) -> a) $ map (\(m,_,_) -> Graph.lab dg m) $ linkFilter $ Graph.inn dg n

inputLNodes::DGraph->Graph.Node->[Graph.LNode DGNodeLab]
inputLNodes dg n = map (\(m,_,_) -> (m, (\(Just a) -> a) $ Graph.lab dg m) ) $ linkFilter $ Graph.inn dg n
		
inputNodes::DGraph->Graph.Node->[Graph.Node]
inputNodes dg n = map (\(m,_,_) -> m) $ linkFilter $ Graph.inn dg n

getCASLMorph::(Graph.LEdge DGLinkLab)->(CASL.Morphism.Morphism () () ())
getCASLMorph (_,_,edge) = (\(Just a) -> a) $ (\(Logic.Grothendieck.GMorphism _ _ morph) -> Data.Typeable.cast morph :: (Maybe (CASL.Morphism.Morphism () () ()))) $ dgl_morphism edge

getMCASLMorph::(Graph.LEdge DGLinkLab)->(Maybe (CASL.Morphism.Morphism () () ()))
getMCASLMorph (_,_,edge) = (\(Logic.Grothendieck.GMorphism _ _ morph) -> Data.Typeable.cast morph :: (Maybe (CASL.Morphism.Morphism () () ()))) $ dgl_morphism edge

signViaMorphism::DGraph->Graph.Node->CASLSign
signViaMorphism dg n =
	let	outedges = Graph.out dg n
	in	if outedges == [] then
				emptySign ()
			else
				let
					mcaslmorph = getMCASLMorph $ head outedges
				in	case mcaslmorph of
						(Just caslmorph) -> CASL.Morphism.msource caslmorph
						_ -> emptySign ()
						
data WithOrigin a b = WithOrigin { woItem::a, woOrigin::b }
		
--data WithOriginNode a = WithOriginNode { wonItem::a, wonOrigin::Graph.Node }
type WithOriginNode a = WithOrigin a Graph.Node


-- Equality and Ordering may not only depend on the stored items as this would
-- lead to removal in sets,maps,etc...
-- But still equality-checks on items are needed.

equalItems::(Eq a)=>WithOrigin a b->WithOrigin a c->Bool
equalItems p q = (woItem p) == (woItem q) 

compareItems::(Ord a)=>WithOrigin a b->WithOrigin a c->Ordering
compareItems p q = compare (woItem p) (woItem q)

instance (Eq a, Eq b)=>Eq (WithOrigin a b) where
	wo1 == wo2 = ((woOrigin wo1) == (woOrigin wo2)) && ((woItem wo1) == (woItem wo2))  
	
instance (Eq a, Ord b, Ord a)=>Ord (WithOrigin a b) where
	compare wo1 wo2 =
		let
			icmp = compare (woItem wo1) (woItem wo2)
		in
			if icmp == EQ then compare (woOrigin wo1) (woOrigin wo2) else icmp 
	
instance (Show a, Show b)=>Show (WithOrigin a b) where
	show wo = (show (woItem wo)) ++ " Origin:(" ++ (show (woOrigin wo)) ++ ")"
	
wonItem::WithOriginNode a->a
wonItem = woItem

wonOrigin::WithOriginNode a->Graph.Node
wonOrigin = woOrigin
	
mkWON::a->Graph.Node->WithOriginNode a
mkWON = WithOrigin
	
originOrder::(Ord o)=>WithOrigin a o->WithOrigin b o->Ordering
originOrder wo1 wo2 = compare (woOrigin wo1) (woOrigin wo2)
	
sameOrigin::(Eq o)=>WithOrigin a o->WithOrigin a o->Bool
sameOrigin wo1 wo2 = (woOrigin wo1) == (woOrigin wo2) 

-- gets something from a DGNode or returns default value for DGRefS
getFromDGNode::DGNodeLab->(DGNodeLab->a)->a->a
getFromDGNode node get' def =
	if isDGRef node then def else
		get' node
		
getFromNode::DGraph->Graph.Node->(DGNodeLab->Bool)->(DGNodeLab->a)->(DGraph->Graph.Node->a)->a
getFromNode dg n usenode getnode getgraphnode =
	let	node = (\(Just a) -> a) $ Graph.lab dg n
	in	if usenode node then
			getnode node
		else
			getgraphnode dg n
			
-- generic function to calculate a delta between a node and the nodes it
-- imports from
getFromNodeDelta::DGraph->Graph.Node->(DGNodeLab->a)->(a->a->a)->a->a
getFromNodeDelta dg n get' delta def =
	let	node = (\(Just a) -> a) $ Graph.lab dg n
		innodes = inputNodeLabs dg n
	in
		foldl (\r n' ->
			delta r $ getFromDGNode n' get' def
			) (getFromDGNode node get' def) innodes
			
getFromNodeDeltaM::DGraph->Graph.Node->(DGNodeLab->Bool)->(DGNodeLab->a)->(DGraph->Graph.Node->a)->(a->a->a)->a
getFromNodeDeltaM dg n usenode getnode getgraphnode delta =
	let	--node = (\(Just a) -> a) $ Graph.lab dg n
		innodes = inputNodes dg n
	in
		foldl (\r n' ->
			let 
				newvalue = getFromNode dg n' usenode getnode getgraphnode
				result = delta r newvalue
			in
				result
			) (getFromNode dg n usenode getnode getgraphnode) innodes
			
getFromNodeWithOriginsM::
	DGraph->
	Graph.Node->
	(DGNodeLab->Bool)->
	(DGNodeLab->a)->
	(DGraph->Graph.Node->a)->
	(a->[b])->
	(b->DGraph->Graph.Node->Bool)->
	([WithOriginNode b]->c)->
	c
getFromNodeWithOriginsM dg n usenode getnode getgraphnode getcomponents isorigin createresult =
	let
		item' = getFromNode dg n usenode getnode getgraphnode
		components = getcomponents item'
		traced = foldl (\traced' c ->
			let
				mo = traceOrigin dg n [] (isorigin c)
			in
				traced' ++ [case mo of
					Nothing -> mkWON c n -- current node is origin
					(Just o) -> mkWON c o]
				) [] components
	in
		createresult traced
		
getFromNodeWithOriginsMSet::
	(Ord a)=>
	DGraph->
	Graph.Node->
	(DGNodeLab->Bool)->
	(DGNodeLab->Set.Set a)->
	(DGraph->Graph.Node->Set.Set a)->
	(a->DGraph->Graph.Node->Bool)->
	Set.Set (WithOriginNode a)
getFromNodeWithOriginsMSet dg n usenode getset getgraphset isorigin =
	getFromNodeWithOriginsM dg n usenode getset getgraphset Set.toList isorigin Set.fromList

getFromCASLSignWithOrigins::
	DGraph->Graph.Node->(CASLSign->a)->(a->[b])->(b->a->Bool)->([WithOriginNode b]->c)->c
getFromCASLSignWithOrigins dg n caslget getcomponents isorigin createresult =
	getFromNodeWithOriginsM dg n (\_ -> False) (\_ -> undefined::a)
		(\dg' n' -> getFromCASLSignM dg' n' caslget)
		getcomponents
		(\i dg' n' -> isorigin i (getFromCASLSignM dg' n' caslget))
		createresult
		
getSortsFromNodeWithOrigins::
	DGraph->Graph.Node->SortsWO
getSortsFromNodeWithOrigins dg n =
	getFromCASLSignWithOrigins
		dg
		n
		sortSet
		Set.toList
		Set.member
		Set.fromList
		
getOpsMapFromNodeWithOrigins::
	DGraph->Graph.Node->OpsWO
getOpsMapFromNodeWithOrigins dg n =
	getFromCASLSignWithOrigins
		dg
		n
		opMap
		Map.toList
		(\(mid, _) om -> case Map.lookup mid om of
			Nothing -> False
			(Just _) -> True)
		(Map.fromList . (map (\mewo ->
			(mkWON (fst (wonItem mewo)) (wonOrigin mewo), snd (wonItem mewo)))))
			
getAssocOpsMapFromNodeWithOrigins::
	DGraph->Graph.Node->OpsWO
getAssocOpsMapFromNodeWithOrigins dg n =
	getFromCASLSignWithOrigins
		dg
		n
		assocOps
		Map.toList
		(\(mid, _) om -> case Map.lookup mid om of
			Nothing -> False
			(Just _) -> True)
		(Map.fromList . (map (\mewo ->
			(mkWON (fst (wonItem mewo)) (wonOrigin mewo), snd (wonItem mewo)))))
			
getPredsMapFromNodeWithOrigins::
	DGraph->Graph.Node->PredsWO
getPredsMapFromNodeWithOrigins dg n =
	getFromCASLSignWithOrigins
		dg
		n
		predMap
		Map.toList
		(\(mid, _) om -> case Map.lookup mid om of
			Nothing -> False
			(Just _) -> True)
		(Map.fromList . (map (\mewo ->
			(mkWON (fst (wonItem mewo)) (wonOrigin mewo), snd (wonItem mewo)))))
			
getSensFromNodeWithOrigins::
	DGraph->Graph.Node->SensWO
getSensFromNodeWithOrigins dg n =
	getFromNodeWithOriginsMSet
		dg
		n
		(\_ -> True)
		(Set.fromList . getNodeSentences)
		(\_ _ -> undefined::Set.Set (Ann.Named CASLFORMULA))
		(\s dg' n' ->
			case lab dg' n' of
				Nothing -> False
				(Just node) -> elem s (getNodeSentences node)
		)
			
traceOrigin::DGraph->Graph.Node->[Graph.Node]->(DGraph->Graph.Node->Bool)->Maybe Graph.Node
traceOrigin dg n visited test =
	if (elem n visited) -- circle encountered...
		then
			Nothing -- we are performing a depth-search so terminate this tree
		else
			-- check if this node still carries the attribute
			if not $ test dg n
				then
					-- it does not, but the previous node did
					if (length visited) == 0
						then
							{-	there was no previous node. this means the start
								node did not have the attribute searched for -}
							Debug.Trace.trace
								"traceOrigin: search from invalid node"
								Nothing
						else
							-- normal case, head is the previous node
							(Just (head visited))
				else
					-- this node still carries the attribute
					let
						-- get possible node for import (OmDOC-specific)
						innodes = inputNodes dg n
						-- find first higher origin
						mo = first
								(\n' -> traceOrigin dg n' (n:visited) test)
								innodes
					in
						-- if there is no higher origin, this node is the origin
						case mo of
							Nothing ->
								{-	if further search fails, then this
									node must be the origin -}
								(Just n) 
							(Just _) ->
							 	-- else use found origin
								mo
								
								
-- helper function to extract an element from the caslsign of a node
-- or to provide a safe default
getFromCASLSign::DGNodeLab->(CASLSign->a)->a->a
getFromCASLSign node get' def =
	getFromDGNode
		node
		(\n ->
			let caslsign = getJustCASLSign $ getCASLSign (dgn_sign n)
			in get' caslsign
		)
		def
		
getFromCASLSignM::DGraph->Graph.Node->(CASLSign->a)->a
getFromCASLSignM dg n get' =
	let	node = (\(Just a) -> a) $ Graph.lab dg n
		caslsign = if isDGRef node
					then signViaMorphism dg n
					else getJustCASLSign $ getCASLSign (dgn_sign node)
	in	get' caslsign
			
-- wrapper around 'getFromNodeDelta' for CASLSign-specific operations
getFromCASLSignDelta::DGraph->Graph.Node->(CASLSign->a)->(a->a->a)->a->a
getFromCASLSignDelta dg n get' delta def =
	getFromNodeDelta dg n (\g -> getFromCASLSign g get' def) delta def

getFromCASLSignDeltaM::DGraph->Graph.Node->(CASLSign->a)->(a->a->a)->a->a
getFromCASLSignDeltaM dg n get' delta _ =
	getFromNodeDeltaM dg n
		(\_ -> False)
		(\_ -> undefined::a)
		(\dg' n' -> getFromCASLSignM dg' n' get' )
		delta
		
-- extract all sorts from a node that are not imported from other nodes
getNodeDeltaSorts::DGraph->Graph.Node->(Set.Set SORT)
getNodeDeltaSorts dg n = getFromCASLSignDeltaM dg n sortSet Set.difference Set.empty

getRelsFromNodeWithOrigins::Maybe SortsWO->DGraph->Graph.Node->Rel.Rel SORTWO
getRelsFromNodeWithOrigins mswo dg n =
	let
		sortswo = case mswo of
			Nothing -> getSortsFromNodeWithOrigins dg n
			(Just swo) -> swo
		rel = getFromCASLSignM dg n sortRel
	in
		Rel.fromList $
			map (\(a, b) ->
				let
					swoa = case Set.toList $ Set.filter (\m -> a == wonItem m) sortswo of
						[] ->
							Debug.Trace.trace
								("Unknown Sort in Relation... ("
									++ (show a) ++ ")")
								(mkWON a n)
						(i:_) -> i
					swob = case Set.toList $ Set.filter (\m -> b == wonItem m) sortswo of
						[] ->
							Debug.Trace.trace
								("Unknown Sort in Relation... ("
									++ (show b) ++ ")")
								(mkWON b n)
						(i:_) -> i
				in
					(swoa, swob)
					) $ Rel.toList rel

-- extract all relations from a node that are not imported from other nodes
getNodeDeltaRelations::DGraph->Graph.Node->(Rel.Rel SORT)
getNodeDeltaRelations dg n = getFromCASLSignDeltaM dg n sortRel Rel.difference Rel.empty

-- extract all predicates from a node that are not imported from other nodes
getNodeDeltaPredMaps::DGraph->Graph.Node->(Map.Map Id.Id (Set.Set PredType))		
getNodeDeltaPredMaps dg n = getFromCASLSignDeltaM dg n predMap
	(Map.differenceWith (\a b -> let diff = Set.difference a b in if Set.null diff then Nothing else Just diff))
	Map.empty
	
-- extract all operands from a node that are not imported from other nodes
getNodeDeltaOpMaps::DGraph->Graph.Node->(Map.Map Id.Id (Set.Set OpType))
getNodeDeltaOpMaps dg n = getFromCASLSignDeltaM dg n opMap
	(Map.differenceWith (\a b -> let diff = Set.difference a b in if Set.null diff then Nothing else Just diff))
	Map.empty
	
getSentencesFromG_theory::G_theory->[Ann.Named CASLFORMULA]
getSentencesFromG_theory (G_theory _ _ thsens) =
	let
		(Just csen) = ((cast thsens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))))
	in Prover.toNamedList csen

-- get CASL-formulas from a node
getNodeSentences::DGNodeLab->[Ann.Named CASLFORMULA]
getNodeSentences (DGRef {}) = []
getNodeSentences node =
	let
		(Just csen) = (\(G_theory _ _ thsens) -> (cast thsens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)))) $ dgn_theory node
	in Prover.toNamedList csen

-- extract the sentences from a node that are not imported from other nodes				
getNodeDeltaSentences::DGraph->Graph.Node->(Set.Set (Ann.Named CASLFORMULA))
getNodeDeltaSentences dg n = getFromNodeDeltaM dg n (not . isDGRef) (Set.fromList . getNodeSentences) (\_ _ -> Set.empty) Set.difference

-- generic function to perform mapping of node-names to a specific mapping function
getNodeNameMapping::DGraph->(DGraph->Graph.Node->a)->(a->Bool)->(Map.Map String a)
getNodeNameMapping dg mapper dispose =
	 foldl (\mapping (n,node) ->
		let mapped = mapper dg n
		in
		if dispose mapped then
			mapping
		else
			-- had to change '#' to '_' because '#' is not valid in names...
			Map.insert (adjustNodeName ("AnonNode_"++(show n)) $ getDGNodeName node) (mapper dg n) mapping
		) Map.empty $ Graph.labNodes dg

getNodeDGNameMapping::DGraph->(DGraph->Graph.Node->a)->(a->Bool)->(Map.Map NODE_NAME a)
getNodeDGNameMapping dg mapper dispose =
	 foldl (\mapping (n,node) ->
		let mapped = mapper dg n
		in
		if dispose mapped then
			mapping
		else
			Map.insert (dgn_name node) mapped mapping
		) Map.empty $ Graph.labNodes dg
		
getNodeDGNameMappingWO::DGraph->(DGraph->Graph.Node->a)->(a->Bool)->(Map.Map NODE_NAMEWO a)
getNodeDGNameMappingWO dg mapper dispose =
	 foldl (\mapping (n,node) ->
		let mapped = mapper dg n
		in
		if dispose mapped then
			mapping
		else
			Map.insert (mkWON (dgn_name node) n) mapped mapping
		) Map.empty $ Graph.labNodes dg
		
getNodeDGNameMappingWONP::DGraph->(NODE_NAMEWO->DGraph->Graph.Node->a)->(a->Bool)->(Map.Map NODE_NAMEWO a)
getNodeDGNameMappingWONP dg mapper dispose =
	 foldl (\mapping (n,node) ->
		let
			thisname = mkWON (dgn_name node) n
			mapped = mapper thisname dg n
		in
		if dispose mapped then
			mapping
		else
			Map.insert thisname mapped mapping
		) Map.empty $ Graph.labNodes dg
		
type Imports = Set.Set (String, (Maybe MorphismMap))
type Sorts = Set.Set SORT
type Rels = Rel.Rel SORT
type Preds = Map.Map Id.Id (Set.Set PredType)
type Ops = Map.Map Id.Id (Set.Set OpType)
type Sens = Set.Set (Ann.Named CASLFORMULA)

type NODE_NAMEWO = WithOriginNode NODE_NAME
type SORTWO = WithOriginNode SORT
type IdWO = WithOriginNode Id.Id
type SentenceWO = WithOriginNode (Ann.Named CASLFORMULA)


type ImportsWO = Set.Set (NODE_NAMEWO, (Maybe MorphismMap))
type SortsWO = Set.Set SORTWO
type RelsWO = Rel.Rel SORTWO
type PredsWO = Map.Map IdWO (Set.Set PredType)
type OpsWO = Map.Map IdWO (Set.Set OpType)
type SensWO = Set.Set SentenceWO

type ImportsMap = Map.Map String Imports
type SortsMap = Map.Map String Sorts
type RelsMap = Map.Map String Rels
type PredsMap = Map.Map String Preds
type OpsMap = Map.Map String Ops
type SensMap = Map.Map String Sens

type ImportsMapDGWO = Map.Map NODE_NAMEWO ImportsWO
type SortsMapDGWO = Map.Map NODE_NAMEWO SortsWO
type RelsMapDGWO = Map.Map NODE_NAMEWO RelsWO
type PredsMapDGWO = Map.Map NODE_NAMEWO PredsWO
type OpsMapDGWO = Map.Map NODE_NAMEWO OpsWO
type SensMapDGWO = Map.Map NODE_NAMEWO SensWO

type AllMaps = (ImportsMap, SortsMap, RelsMap, PredsMap, OpsMap, SensMap)

instance Show AllMaps where
	show (imports, sorts, rels, preds, ops, sens) =
		"Imports:\n" ++ show imports ++
		"\nSorts:\n" ++ show sorts ++
		"\nRelations:\n" ++ show rels ++
		"\nPredicates:\n" ++ show preds ++
		"\nOperators:\n" ++ show ops ++
		"\nSentences:\n" ++ show sens

diffMaps::
	(Sorts, Rels, Preds, Ops, Sens) ->
	(Sorts, Rels, Preds, Ops, Sens) ->
	(Sorts, Rels, Preds, Ops, Sens)
diffMaps
	(so1, re1, pr1, op1, se1)
	(so2, re2, pr2, op2, se2) =
		(	
			Set.difference so1 so2,
			Rel.difference re1 re2,
			Map.difference pr1 pr2,
			Map.difference op1 op2,
			Set.difference se1 se2
		)
		
lookupMaps::
	SortsMap ->
	RelsMap ->
	PredsMap ->
	OpsMap ->
	SensMap ->
	String ->
	(Sorts, Rels, Preds, Ops, Sens)
lookupMaps sorts rels preds ops sens name =
		(
			Map.findWithDefault Set.empty name sorts,
			Map.findWithDefault Rel.empty name rels,
			Map.findWithDefault Map.empty name preds,
			Map.findWithDefault Map.empty name ops,
			Map.findWithDefault Set.empty name sens
		)
		
-- create a mapping of node-name -> Set of Sorts for all nodes
getSortsWithNodeNames::DGraph->SortsMap
getSortsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaSorts Set.null

getSortsWithNodeDGNames::DGraph->Map.Map NODE_NAME Sorts
getSortsWithNodeDGNames dg = getNodeDGNameMapping dg getNodeDeltaSorts Set.null

getSortsWOWithNodeDGNamesWO::DGraph->SortsMapDGWO
getSortsWOWithNodeDGNamesWO dg =
	getNodeDGNameMappingWO dg getSortsFromNodeWithOrigins Set.null

-- create a mapping of node-name -> Relation of Sorts for all nodes
getRelationsWithNodeNames::DGraph->RelsMap
getRelationsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaRelations Rel.null

getRelationsWithNodeDGNames::DGraph->Map.Map NODE_NAME Rels
getRelationsWithNodeDGNames dg = getNodeDGNameMapping dg getNodeDeltaRelations Rel.null

getRelationsWOWithNodeDGNamesWO::DGraph->RelsMapDGWO
getRelationsWOWithNodeDGNamesWO dg =
	getNodeDGNameMappingWO dg (getRelsFromNodeWithOrigins Nothing) Rel.null

getRelationsWOWithNodeDGNamesWOSMDGWO::DGraph->SortsMapDGWO->RelsMapDGWO
getRelationsWOWithNodeDGNamesWOSMDGWO dg sm =
	getNodeDGNameMappingWONP dg (\nodenamewo -> getRelsFromNodeWithOrigins (Map.lookup nodenamewo sm)) Rel.null
	
-- create a mapping of node-name -> Predicate-Mapping (PredName -> Set of PredType)
getPredMapsWithNodeNames::DGraph->PredsMap
getPredMapsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaPredMaps Map.null

getPredMapsWithNodeDGNames::DGraph->Map.Map NODE_NAME Preds
getPredMapsWithNodeDGNames dg = getNodeDGNameMapping dg getNodeDeltaPredMaps Map.null

getPredMapsWOWithNodeDGNamesWO::DGraph->PredsMapDGWO
getPredMapsWOWithNodeDGNamesWO dg = getNodeDGNameMappingWO dg getPredsMapFromNodeWithOrigins Map.null 

-- create a mapping of node-name -> Operand-Mapping (OpName -> Set of OpType)
getOpMapsWithNodeNames::DGraph->OpsMap
getOpMapsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaOpMaps Map.null

getOpMapsWithNodeDGNames::DGraph->Map.Map NODE_NAME Ops
getOpMapsWithNodeDGNames dg = getNodeDGNameMapping dg getNodeDeltaOpMaps Map.null

getOpMapsWOWithNodeDGNamesWO::DGraph->OpsMapDGWO
getOpMapsWOWithNodeDGNamesWO dg = getNodeDGNameMappingWO dg getOpsMapFromNodeWithOrigins Map.null 

-- get a mapping of node-name -> Set of Sentences (CASL-formulas)
getSentencesWithNodeNames::DGraph->SensMap
getSentencesWithNodeNames dg = getNodeNameMapping dg getNodeDeltaSentences Set.null

getSentencesWithNodeDGNames::DGraph->Map.Map NODE_NAME Sens
getSentencesWithNodeDGNames dg = getNodeDGNameMapping dg getNodeDeltaSentences Set.null

getSentencesWOWithNodeDGNamesWO::DGraph->SensMapDGWO
getSentencesWOWithNodeDGNamesWO dg = getNodeDGNameMappingWO dg getSensFromNodeWithOrigins Set.null

getAll::DGraph->AllMaps
getAll dg = (
	getNodeImportsNodeNames dg,
	getSortsWithNodeNames dg,
	getRelationsWithNodeNames dg,
	getPredMapsWithNodeNames dg,
	getOpMapsWithNodeNames dg,
	getSentencesWithNodeNames dg
	)

getExternalLibNames::DGraph->(Set.Set LIB_NAME)
getExternalLibNames =
	Set.fromList . map dgn_libname . filter isDGRef . map snd . Graph.labNodes

type DGStructure = Map.Map LIB_NAME AllMaps

createDGStructure::FilePath->(IO DGStructure)
createDGStructure f = 
	do
		(Just (_, lenv)) <- run f
		return (
			foldl (\map' (lname, gc) ->
				Map.insert lname (getAll (devGraph gc)) map'
				) Map.empty $ Map.toList lenv
			)


-- get all axioms
getAxioms::[Ann.Named a]->[Ann.Named a]
getAxioms l = filter (\(NamedSen {isAxiom = iA}) -> iA) l

-- get all non-axioms
getNonAxioms::[Ann.Named a]->[Ann.Named a]
getNonAxioms l = filter (\(NamedSen {isAxiom = iA}) -> not iA) l

isEmptyMorphism::(Morphism a b c)->Bool
isEmptyMorphism (Morphism _ _ sm fm pm _) =
	Map.null sm && Map.null fm && Map.null pm

-- fetch the names of all nodes from wich sorts,rels, etc. are imported
-- this does not list all imports in the DGraph, just the ones that cause
-- sorts,rels, etc. to dissappear from a node
getNodeImportsNodeNames::DGraph->ImportsMap
getNodeImportsNodeNames dg = getNodeNameMapping dg (
	\dgr n -> Set.fromList $ 
	 foldl (\names (from,node) ->
	 	let
			edges' = filter (\(a,b,_) -> (a == from) && (b==n)) $ Graph.labEdges dgr
			caslmorph = case edges' of
				[] -> emptyCASLMorphism
				(l:_) -> getCASLMorph l
			mmm = if isEmptyMorphism caslmorph
				then
					Nothing
				else
					(Just (makeMorphismMap caslmorph))
		in
			((adjustNodeName ("AnonNode_"++(show from)) $ getDGNodeName node), mmm):names
		) [] $ inputLNodes dgr n ) Set.null
	
getNodeImportsNodeDGNames::DGraph->Map.Map NODE_NAME (Set.Set (NODE_NAME, Maybe MorphismMap))
getNodeImportsNodeDGNames dg = getNodeDGNameMapping dg (
	\dgr n -> Set.fromList $ 
	 foldl (\names (from,node) ->
	 	let
			edges' = filter (\(a,b,_) -> (a == from) && (b==n)) $ Graph.labEdges dgr
			caslmorph = case edges' of
				[] -> emptyCASLMorphism
				(l:_) -> getCASLMorph l
			mmm = if isEmptyMorphism caslmorph
				then
					Nothing
				else
					(Just (makeMorphismMap caslmorph))
		in
			((dgn_name node), mmm):names
		) [] $ inputLNodes dgr n ) Set.null
		
adjustNodeName::String->String->String
adjustNodeName def [] = def
adjustNodeName _ name = name

-- get a set of all names for the nodes in the DGraph
getNodeNames::DGraph->(Set.Set (Graph.Node, String))
getNodeNames dg =
	fst $ foldl (\(ns, num) (n, node) ->
		(Set.insert (n, adjustNodeName ("AnonNode_"++(show num)) $ getDGNodeName node) ns, (num+1)::Integer)
		) (Set.empty, 1) $ Graph.labNodes dg
		
partition::(a->Bool)->[a]->([a], [a])
partition left =
	foldl (\(rl, rr) a -> if left a then (a:rl, rr) else (rl, a:rr)) ([],[]) 
		
-- | get two sets of node nums and names. first set are nodes, second are refs
getNodeNamesNodeRef::DGraph->(Set.Set (Graph.Node, String), Set.Set (Graph.Node, String))
getNodeNamesNodeRef dg =
	let
		lnodes = Graph.labNodes dg
		(nodes' , refs) = partition (\(_,n) -> not $ isDGRef n) lnodes
		nnames = map (\(n, node) -> (n, adjustNodeName ("AnonNode_"++(show n)) $ getDGNodeName node)) nodes'
		rnames = map (\(n, node) -> (n, adjustNodeName ("AnonRef_"++(show n)) $ getDGNodeName node)) refs
	in
		(Set.fromList nnames, Set.fromList rnames)
			
getNodeDGNamesNodeRef::DGraph->(Set.Set (Graph.Node, NODE_NAME), Set.Set (Graph.Node, NODE_NAME))
getNodeDGNamesNodeRef dg =
	let
		lnodes = Graph.labNodes dg
		(nodes' , refs) = partition (\(_,n) -> not $ isDGRef n) lnodes
		nnames = map (\(n, node) -> (n, dgn_name node)) nodes'
		rnames = map (\(n, node) -> (n, dgn_name node)) refs
	in
		(Set.fromList nnames, Set.fromList rnames)


-- go through a list and perform a function on each element that returns a Maybe
-- return the first value that is not Nothing
first::(a -> (Maybe b))->[a]->(Maybe b)
first _ [] = Nothing
first f (a:l) = let b = f a in case b of Nothing -> first f l; _ -> b 

-- searches for the origin of an attribute used in a node
-- the finder-function returns true, if the the attribute is 'true' for
-- the attribute-map for a node
findNodeNameFor::ImportsMap->(Map.Map String a)->(a->Bool)->String->(Maybe String)
findNodeNameFor importsMap attribMap finder name =
	let	m_currentAttrib = Map.lookup name attribMap
		currentImports = Set.map fst $ Map.findWithDefault Set.empty name importsMap
	in
		if (
			case m_currentAttrib of
				Nothing -> False
				(Just a) -> finder a
			) then
				(Just name)
				else
				first (findNodeNameFor importsMap attribMap finder) $ Set.toList currentImports

-- lookup a sort starting with a given node (by name)
-- will traverse the importsMap while the sort is not found and
-- return the name of the [first] node that has this sort in its sort-set 
findNodeNameForSort::ImportsMap->SortsMap->SORT->String->(Maybe String)
findNodeNameForSort importsMap sortsMap sort name =
	findNodeNameFor importsMap sortsMap (Set.member sort) name

-- lookup the origin of a predication by id
-- not very usefull without specifying the argument-sorts
findNodeNameForPredication::ImportsMap->PredsMap->Id.Id->String->(Maybe String)
findNodeNameForPredication importsMap predsMap predId name =
	findNodeNameFor importsMap predsMap (\m -> Map.lookup predId m /= Nothing) name
	
-- lookup the origin of a predication by id and argument-sorts (PredType)
findNodeNameForPredicationWithSorts::ImportsMap->PredsMap->(Id.Id, PredType)->String->(Maybe String)
findNodeNameForPredicationWithSorts importsMap predsMap (predId, pt) name =
	findNodeNameFor importsMap predsMap 
		(\m ->	let predSet = Map.findWithDefault Set.empty predId m
			in Set.member pt predSet )
		name

-- lookup the origin of an operand		
findNodeNameForOperator::ImportsMap->OpsMap->Id.Id->String->(Maybe String)
findNodeNameForOperator importsMap opsMap opId name =
	findNodeNameFor importsMap opsMap (\m -> Map.lookup opId m /= Nothing) name
	
-- lookup the origin of an operand with OpType
findNodeNameForOperatorWithSorts::ImportsMap->OpsMap->(Id.Id, OpType)->String->(Maybe String)
findNodeNameForOperatorWithSorts importsMap opsMap (opId, ot) name =
	findNodeNameFor importsMap opsMap 
		(\m ->	let opSet = Map.findWithDefault Set.empty opId m
			in Set.member ot opSet )
		name
		
findNodeNameForOperatorWithFK::ImportsMap->OpsMap->(Id.Id, FunKind)->String->(Maybe String)
findNodeNameForOperatorWithFK importsMap opsMap (opId, fk) name =
	findNodeNameFor importsMap opsMap 
		(\m ->	let opSet = Map.findWithDefault Set.empty opId m
			in not $ null $ filter (\(OpType ofk _ _) -> ofk == fk) $ Set.toList opSet )
		name


findNodeNameForSentenceName::ImportsMap->SensMap->String->String->(Maybe String)
findNodeNameForSentenceName importsMap sensMap sName name =
	findNodeNameFor importsMap sensMap (\n -> not $ Set.null $ Set.filter (\n' -> (senName n' ) == sName) n) name
	
findNodeNameForSentence::ImportsMap->SensMap->CASLFORMULA->String->(Maybe String)
findNodeNameForSentence importsMap sensMap s name =
	findNodeNameFor importsMap sensMap (\n -> not $ Set.null $ Set.filter (\n' -> (sentence n' ) == s) n) name
	

-- | Reduce a DevGraph by backtracking importing links
createReducedDGraph::DGraph->DGraph
createReducedDGraph dg =
	let	lnodes = Graph.labNodes dg
		ledges = Graph.labEdges dg
	in Graph.mkGraph (map (createReducedNode dg) lnodes) ledges
	

buildCASLSentenceDiff::(Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))->(Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))->(Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))
buildCASLSentenceDiff = OMap.difference

buildCASLSignDiff::CASLSign->CASLSign->CASLSign
buildCASLSignDiff = diffSig

emptyCASLMorphism::(CASL.Morphism.Morphism () () ())
emptyCASLMorphism = CASL.Morphism.Morphism (emptySign ()) (emptySign ()) Map.empty Map.empty Map.empty ()
		
emptyCASLGMorphism::Logic.Grothendieck.GMorphism
emptyCASLGMorphism = Logic.Grothendieck.gEmbed (Logic.Grothendieck.G_morphism CASL emptyCASLMorphism)

makeCASLGMorphism::(CASL.Morphism.Morphism () () ())->Logic.Grothendieck.GMorphism
makeCASLGMorphism m = Logic.Grothendieck.gEmbed (Logic.Grothendieck.G_morphism CASL m)

emptyCASLSign::CASLSign
emptyCASLSign = emptySign ()


-- | create a node containing only the local attributes of this node by stripping
-- the attributes of the second node
buildCASLNodeDiff::DGNodeLab->DGNodeLab->DGNodeLab
buildCASLNodeDiff
	node1@(DGNode { dgn_theory = th1})
	(DGNode { dgn_theory = th2}) =
		let	sens1 = (\(G_theory _ _ sens) -> (cast sens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)))) th1
			sens2 = (\(G_theory _ _ sens) -> (cast sens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)))) th2
			sign1 = (\(G_theory _ sign _) -> (cast sign)::(Maybe CASLSign)) th1
			sign2 = (\(G_theory _ sign _) -> (cast sign)::(Maybe CASLSign)) th2
		in
		   case (sens1, sens2, sign1, sign2) of
		   	(Just se1, Just se2, Just si1, Just si2) ->
				let	sediff = buildCASLSentenceDiff se1 se2
					sidiff = buildCASLSignDiff si1 si2
					theo = G_theory CASL sidiff sediff
				in	node1 { dgn_theory = theo }
			_ -> error "This function can only handle CASL-related DGNodeLabS..."		
buildCASLNodeDiff n _ = n -- error "Either one or both Nodes are DGRefs. I cannot handle DGRefs..."

stripCASLMorphism::DGNodeLab->(CASL.Morphism.Morphism () () ())->DGNodeLab
stripCASLMorphism
	n@(DGNode { dgn_theory = th } )
	(CASL.Morphism.Morphism { CASL.Morphism.fun_map = fm, CASL.Morphism.pred_map = pm }) =
		let	mcsi = (\(G_theory _ sign _) -> (cast sign)::(Maybe CASLSign)) th
			mcse = (\(G_theory _ _ sens) -> (cast sens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)))) th
		in case mcsi of
			(Just (Sign ss sr om ao oldpm vm se ev ga ei)) ->
				let	funlist = (map (\(_, (f, _)) -> f) $ Map.toList fm)::[Id.Id]
					predlist = (map (\(_, p) -> p) $ Map.toList pm)::[Id.Id]
					newpredmap = foldl (\nmap' id' ->
						Map.filterWithKey (\k _ -> k /= id' ) nmap'
						) oldpm predlist
					newopmap = foldl (\nmap' id' ->
						Map.filterWithKey (\k _ -> k /= id' ) nmap'
						) om funlist
					newassocmap = foldl (\nmap' id' ->
						Map.filterWithKey (\k _ -> k /= id' ) nmap'
						) ao funlist
				in	case mcse of
						(Just csens) -> n { dgn_theory = (G_theory CASL (Sign ss sr newopmap newassocmap newpredmap vm se ev ga ei) csens) }
						_ -> error "Could not cast sentences to (ThSens CASLFORMULA) (but a CASLSign was cast... (wierd!))"
			Nothing -> n  -- maybe this node is not CASL-related... leave it as is
stripCASLMorphism n@(DGRef {}) _ = n -- can DGRefS have a morphism from another node in the graph ?


stripCASLMorphisms::DGraph->(Graph.LNode DGNodeLab)->(Graph.LNode DGNodeLab)
stripCASLMorphisms dg (n, node) =
	case node of
		(DGRef {}) -> (n, node) -- no need to do this for a reference...
		_ ->
			let	incoming = filter ( \(_,tn,_) -> n == tn ) $ Graph.labEdges dg
				{- imports = filter ( \(_,_,iedge) ->
					case iedge of
						(DGLink _ t _) ->
							case t of
								LocalDef -> True
								GlobalDef -> True
								HidingDef -> True
								_ -> False
					) incoming -}
				morphisms = map ( \(_,_,e) -> dgl_morphism e) incoming
			in (n,
				foldl (\newnode gmorph ->
					let	mcaslmorph = (\(GMorphism _ _ morph) -> (cast morph)::(Maybe (CASL.Morphism.Morphism () () ()))) gmorph
					in	case mcaslmorph of
						(Just caslmorph) -> stripCASLMorphism newnode caslmorph
						_ -> newnode
						) node morphisms)
						
						
type MorphismMap = (
		(Map.Map SORT SORT)
		,(Map.Map (Id.Id,OpType) (Id.Id,OpType))
		,(Map.Map (Id.Id,PredType) (Id.Id,PredType))
		,(Set.Set SORT)
		)
		
type MorphismMapWO = (
		(Map.Map SORTWO SORTWO)
		,(Map.Map (IdWO,OpType) (IdWO, OpType))
		,(Map.Map (IdWO,PredType) (IdWO,PredType))
		,(Set.Set SORTWO)
		)
		
implode::[a]->[[a]]->[a]
implode _ [] = []
implode _ [last' ] = last'
implode with (item' :rest) = item' ++ with ++ (implode with rest)

createHidingString::CASLSign->String
createHidingString (Sign sortset _ opmap _ predmap _ _ _ _ _) =
	let hidden = map show (Set.toList sortset) ++
			 map show (Map.keys opmap) ++
			 map show (Map.keys predmap)
	in	implode ", " hidden

getSymbols::CASLSign->[Id.Id]
getSymbols (Sign sortset _ opmap _ predmap _ _ _ _ _) =
	(Set.toList sortset) ++ (Map.keys opmap) ++ (Map.keys predmap)
	
makeMorphismMap::(Morphism () () ())->MorphismMap
makeMorphismMap (Morphism ssource starget sortmap funmap predmap _) =
	let
		newfunmap = Map.fromList $ map (
			\((sid,sot),(tid,tfk)) ->
				-- Hets sets opKind to Partial on morphism... why ?
				-- resulting signatures have Total operators...
				((sid,(sot { opKind = Total }) ), (tid,
					OpType
						tfk
						(map (\id' -> Map.findWithDefault id' id' sortmap) (opArgs sot))
						((\id' -> Map.findWithDefault id' id' sortmap) (opRes sot))
					) ) ) $ Map.toList funmap
		newpredmap = Map.fromList $ map (
			\((sid, spt),tid) ->
				((sid, spt), (tid,
					PredType (map (\id' -> Map.findWithDefault id' id' sortmap) (predArgs spt))
				) ) ) $ Map.toList predmap
	in
		(sortmap, newfunmap, newpredmap, Set.fromList $ getSymbols $ diffSig ssource starget)
		
removeMorphismSorts::MorphismMap->Sorts->Sorts
removeMorphismSorts (sm,_,_,_) sorts =
	let
		msorts = Map.elems sm
	in
		Set.filter (\s -> not $ elem s msorts) sorts
		
addMorphismSorts::MorphismMap->Sorts->Sorts
addMorphismSorts (sm,_,_,_) sorts =
	let
		msorts = Map.elems sm
	in	
		Set.union sorts $ Set.fromList msorts
		
removeMorphismOps::MorphismMap->Ops->Ops
removeMorphismOps (_,om,_,_) ops =
	let
		mops = map fst $ Map.elems om
	in
		Map.filterWithKey (\k _ -> not $ elem k mops) ops
		
addMorphismOps::MorphismMap->Ops->Ops
addMorphismOps (_,om,_,_) ops =
	let
		mops = Map.elems om
	in
		foldl (\newmap (i,ot) ->
			Map.insert
				i
				(Set.union
					(Map.findWithDefault Set.empty i newmap)
					(Set.singleton ot)
				)
				newmap
			) ops mops 
		
removeMorphismPreds::MorphismMap->Preds->Preds
removeMorphismPreds (_,_,pm,_) preds =
	let
		mpreds = map fst $ Map.elems pm
	in
		Map.filterWithKey (\k _ -> not $ elem k mpreds) preds 
	
addMorphismPreds::MorphismMap->Preds->Preds
addMorphismPreds (_,_,pm,_) preds =
	let
		mpreds = Map.elems pm
	in
		foldl (\newmap (i,pt) ->
			Map.insert
				i
				(Set.union
					(Map.findWithDefault Set.empty i newmap)
					(Set.singleton pt)
				)
				newmap
			) preds mpreds 
		
morphismMapToMorphism::MorphismMap->(Morphism () () ())
morphismMapToMorphism (sortmap, funmap, predmap,_) =
	let
		mfunmap = Map.fromList $ map (\((sid, sot),t) -> ((sid, sot { opKind = Partial }),t)) $ Map.toList $ Map.map (\(tid,(OpType fk _ _)) ->
			(tid, fk) ) funmap
		mpredmap = Map.map (\(tid,_) ->	tid ) predmap
	in
		Morphism (emptySign ()) (emptySign ()) sortmap mfunmap mpredmap ()
		
applyMorphHiding::MorphismMap->[Id.Id]->MorphismMap
applyMorphHiding mm [] = mm
applyMorphHiding (sortmap, funmap, predmap, hidingset) hidings =
	(
		 Map.filterWithKey (\sid _ -> not $ elem sid hidings) sortmap
		,Map.filterWithKey (\(sid,_) _ -> not $ elem sid hidings) funmap
		,Map.filterWithKey (\(sid,_) _ -> not $ elem sid hidings) predmap
		,hidingset
	)
	
buildMorphismSign::MorphismMap->[Id.Id]->CASLSign->CASLSign
buildMorphismSign
	(mmsm, mmfm, mmpm, _) 
	hidings
	sourcesign =
	let
		(Sign
			sortset
			sortrel
			opmap
			assocops
			predmap
			varmap
			sens
			envdiags
			ga
			ext
			) = applySignHiding sourcesign hidings
	in
		Sign
			(Set.map
				(\origsort ->
					Map.findWithDefault origsort origsort mmsm
				)
				sortset)
			(Rel.fromList $ map (\(a, b) ->
				(Map.findWithDefault a a mmsm
				,Map.findWithDefault b b mmsm)
				) $ Rel.toList sortrel)
			(foldl (\mappedops (sid, sopts) ->
				foldl (\mo sot ->
					case Map.lookup (sid, sot) mmfm of
						Nothing -> mo
						(Just (mid, mot)) ->
							Map.insertWith (Set.union) mid (Set.singleton mot) mo
					) mappedops $ Set.toList sopts
				) Map.empty $ Map.toList opmap)
			(foldl (\mappedops (sid, sopts) ->
				foldl (\mo sot ->
					case Map.lookup (sid, sot) mmfm of
						Nothing -> mo
						(Just (mid, mot)) ->
							Map.insertWith (Set.union) mid (Set.singleton mot) mo
					) mappedops $ Set.toList sopts
				) Map.empty $ Map.toList assocops)
			(foldl (\mappedpreds (sid, sprts) ->
				foldl (\mp spt ->
					case Map.lookup (sid, spt) mmpm of
						Nothing -> mp
						(Just (mid, mpt)) ->
							Map.insertWith (Set.union) mid (Set.singleton mpt) mp
					) mappedpreds $ Set.toList sprts
				) Map.empty $ Map.toList predmap)
			(Map.map (\vsort -> Map.findWithDefault vsort vsort mmsm) varmap)
			sens
			envdiags
			ga
			ext
	
applySignHiding::CASLSign->[Id.Id]->CASLSign
applySignHiding 
	(Sign sortset sortrel opmap assocops predmap varmap sens envdiags ga ext)
	hidings =
	Sign
		(Set.filter (not . flip elem hidings) sortset)
		(Rel.fromList $ filter (\(id' ,_) -> not $ elem id' hidings) $ Rel.toList sortrel)
		(Map.filterWithKey (\sid _ -> not $ elem sid hidings) opmap)
		(Map.filterWithKey (\sid _ -> not $ elem sid hidings) assocops)
		(Map.filterWithKey (\sid _ -> not $ elem sid hidings) predmap)
		(Map.filter (\varsort -> not $ elem varsort hidings) varmap)
		sens
		envdiags
		ga
		ext

createLocalNode::DGraph->(Graph.LNode DGNodeLab)->(Graph.LNode DGNodeLab)
createLocalNode dg (n, node) =
	case node of
		(DGRef {}) -> (n, node) -- this is actually bad 
			-- there is often a Morphism associated with a DGRef so should
			-- we strip to morphed symbols from this ?
		_ ->
			let	incoming = filter ( \(_,tn,_) -> n == tn ) $ Graph.labEdges dg
				{-imports = filter ( \(_,_,iedge) ->
					case iedge of
						(DGLink _ t _) ->
							case t of
								LocalDef -> True
								GlobalDef -> True
								HidingDef -> True
								_ -> False
					) incoming-}
				innodes = map ( \(n' ,_,_) -> (\(Just a) -> a) $ Graph.lab dg n' ) incoming
			in
				(n, foldl (\lnode inode -> buildCASLNodeDiff lnode inode) node innodes)
		
createReducedNode::DGraph->(Graph.LNode DGNodeLab)->(Graph.LNode DGNodeLab)
createReducedNode dg (n,node) = 
	case node of
		(DGRef {}) -> (n, node)
		_ ->
			let	incoming = filter ( \(_,tn,_) -> n == tn ) $ Graph.labEdges dg
				(li,gi,hi) =
					foldl ( \(nli, ngi, nhi) edge@(_,_,iedge) ->
					case iedge of
						(DGLink _ t _) ->
							case t of
								LocalDef -> (nli++[edge], ngi, nhi)
								GlobalDef -> (nli, ngi++[edge], nhi) 
								HidingDef -> (nli, ngi, nhi++[edge])
								_ -> (nli, ngi, nhi)
						) ([],[],[]) incoming
				localnodes = map ( \(n' ,_,_) -> (\(Just a) -> (n' , a)) $ Graph.lab dg n' ) li
				globalnodes = map ( \(n' ,_,_) -> (\(Just a) -> (n' , a)) $ Graph.lab dg n' ) gi
				hidingnodes = map ( \(n' ,_,_) -> (\(Just a) -> (n' , a)) $ Graph.lab dg n' ) hi
			in
				stripCASLMorphisms dg (n,
					foldl (\nnode (inn'' , inode) ->
						let (_, rnode) = createLocalNode dg (inn'' , inode)
						in buildCASLNodeDiff nnode rnode
						)
					(foldl (\nnode (_, inode) ->
						buildCASLNodeDiff nnode inode
						) node (globalnodes ++ hidingnodes)) localnodes
				)
				
{-
a hiding import is a global import, limited to a subset of the exporting node
a local import is an import of the local attributes of the exporting node
a global import imports all attributes from the exporting node (local and imported)

reducing a node:
to reduce a node, we need to reverse all imports, meaning to remove everything from the
node that was imported from another node according to the type of the import.

reducing a local import : remove the exporting node's set of attributes from the importing node's set
	note : the exporting node must be reduced, to remove imported attributes...
	
reducing a global import : remove the exporting node's set of attributes from the importing node's set
	note : we get the nodes in a state, when their sets are fully imported...
	
reducing a hiding import : remove the attributes of the exporting node from the importing node
	note : the imported attributes will[/should] be a subset of the exporting node's set
	
how to get the local attributes :
	just strip all imported attributes from the node (without reducing other nodes).
	only local attributes can remain...
-}






