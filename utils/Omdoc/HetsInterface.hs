{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The Main module of the Heterogeneous Tool Set. 
   It provides the main function to call.

-}

{- todo: option for omitting writing of env
-}

module HetsInterface where

import Control.Monad (when)

import System.Environment (getArgs)
import System.Exit (ExitCode(ExitSuccess), exitWith)

import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Graph as Graph --

import Common.Utils
import Common.Result
import Common.PrettyPrint
import Common.AS_Annotation
import Common.GlobalAnnotations (emptyGlobalAnnos)
import qualified Common.Lib.Map as Map


import Syntax.AS_Library (LIB_DEFN(..), LIB_NAME()) 
import Syntax.GlobalLibraryAnnotations (initGlobalAnnos)

import Driver.ReadFn
import Driver.WriteFn
import Driver.Options

import Comorphisms.LogicGraph

--import Logic.Languages
import Logic.Grothendieck hiding (Morphism)

import Static.AnalysisLibrary
import Static.DevGraph
import Static.PrintDevGraph()

import Isabelle.CreateTheories

-- for extraction functions
import CASL.AS_Basic_CASL
import CASL.Logic_CASL


--import Syntax.Print_HetCASL
#ifdef UNI_PACKAGE
import GUI.AbstractGraphView
import GUI.ConvertDevToAbstractGraph
import InfoBus 
import Events
import Destructible
import DialogWin (useHTk)
#endif

-- my imports
import CASL.Sign
import CASL.Morphism
import qualified CASL.AS_Basic_CASL as CASLBasic
import Data.Typeable
import qualified Common.Id as Id
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Logic.Grothendieck as Gro
import qualified Common.AS_Annotation as Ann
import qualified Syntax.AS_Library as ASL
import qualified Data.Maybe as Data.Maybe

import qualified CASL.Morphism as CASL.Morphism

import Logic.Logic as Logic

import Data.List (sortBy)

import Debug.Trace (trace)

{-
#ifdef PROGRAMATICA
import Haskell.Haskell2DG
#endif
-}

showGraph :: FilePath -> HetcatsOpts -> 
             Maybe (LIB_NAME, -- filename
                    a,   -- as tree
                    b,   -- development graph
                    LibEnv    -- DGraphs for imported modules 
                   )  -> IO ()
showGraph file opt env =
    case env of
        Just (ln,_,_,libenv) -> do
            putIfVerbose opt 2 ("Trying to display " ++ file
                                ++ " in a graphical window")
            putIfVerbose opt 3 "Initializing Converter"
#ifdef UNI_PACKAGE
            graphMem <- initializeConverter
            useHTk -- All messages are displayed in TK dialog windows 
                   -- from this point on
            putIfVerbose opt 3 "Converting Graph"
            (gid, gv, _cmaps) <- convertGraph graphMem ln libenv opt
            GUI.AbstractGraphView.redisplay gid gv
            graph <- get_graphid gid gv
            sync(destroyed graph)
            InfoBus.shutdown
            exitWith ExitSuccess 
#else
            fail "No graph display interface; UNI_PACKAGE option has been disabled during compilation of Hets"
#endif
        Nothing -> putIfVerbose opt 1
            ("Error: Basic Analysis is neccessary to display "
             ++ "graphs in a graphical window")

hasEnvOut :: HetcatsOpts -> Bool
hasEnvOut = any ( \ o -> case o of EnvOut -> True
                                   _ -> False) . outtypes

-- Just (_,_,dg,_) <- run "CASL/test/X1.casl"
-- let (Just caslsign) = getCASLSign $ getFirstNodeSign dg 
run  :: FilePath -> IO (Maybe (LIB_NAME, LIB_DEFN, DGraph, LibEnv))
run file = 
    do let opt = defaultHetcatsOpts
       ld <- read_LIB_DEFN opt file
       defl <- lookupLogic "logic from command line: " 
                                        (defLogic opt) logicGraph
       Common.Result.Result ds res <- ioresToIO 
                                       (ana_LIB_DEFN logicGraph defl opt 
                                        emptyLibEnv ld)
       showDiags opt ds
       return res

dho::HetcatsOpts
dho = defaultHetcatsOpts

{- Call this function as follows (be sure that there is no ../uni):
make hets
make ghci
:l hets.hs
:module +Data.Graph.Inductive.Graph
Just (ln,ast,dg,libenv)<-run "../CASL-lib/List.casl"
-}

showGraph2::FilePath -> IO ()
showGraph2 f = do
	env <- run f
	showGraph f Driver.Options.defaultHetcatsOpts env

-- further functions for extracting information from the output
{-toCASLsens :: G_l_sentence_list -> [Named (FORMULA ())]
toCASLsens (G_l_sentence_list lid sens) = 
   case coerce lid CASL sens of 
          Just sens' -> sens'
          _ -> error "not a list of CASL sentences"-- Get first node from DG and extract signature
-}


	  
getFirstNodeSign = (\x -> (\(_,s) -> dgn_sign s) ((labNodes x)!!0) )

getFirstNode = (\x -> ((labNodes x)!!0))

--getFirstNodeSentence = (\x -> (\(_,s) -> dgn_sens s) ((labNodes x)!!0) )

--getNodeSentence = (\(_,s) -> dgn_sens s)
--getNodeSentence = (\(_,s) -> toNamedList $ (\(G_theory _ _ thsens) -> thsens) $ dgn_theory s)

--getSentences::(Gro.G_l_sentence_list)->(Maybe [Ann.Named CASLFORMULA])
--getSentences (Gro.G_l_sentence_list _ t) = cast t

-- isAxiom was added... (a :: Bool)
transSen::[Ann.Named CASLFORMULA]->[(String, CASLFORMULA)]
transSen [] = []
transSen ((Ann.NamedSen n _ s):rest) = [(n, s)] ++ transSen rest

transSenBack::[(String, CASLFORMULA)]->[Ann.Named CASLFORMULA]
transSenBack [] = []
transSenBack ((n, s):rest) = (Ann.NamedSen n False s):(transSenBack rest)

getPureFormulas::[(String, CASLFORMULA)]->[CASLFORMULA]
getPureFormulas [] = []
getPureFormulas ((name, f):rest) = [f] ++ getPureFormulas rest

--getFormulas = (\x -> getPureFormulas $ (\(Just s) -> transSen s) $ getSentences $ getFirstNodeSentence x)
--getNamedFormulas = (\x -> (\(Just s) -> transSen s) $ getSentences $ getFirstNodeSentence x)

getDG f = do
	(Just (_,_,dg,_)) <- run f
	return dg 

-- Cast Signature to CASLSignature if possible
getCASLSign::G_sign->(Maybe CASLSign)
getCASLSign (G_sign _ sign) = cast sign -- sign is of class Typeable -> cast -> (Typeable a, Typeable b)->(Maybe b)

getJustCASLSign::(Maybe CASLSign)->CASLSign
getJustCASLSign (Just cs) = cs

--getCASLFormula::Gro.G_l_sentence_list->CASLFORMULA
--getCASLFormula  sl = let (Just asl)=getSentences sl in (\(a, b) -> b) ((transSen asl)!!0) 

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
	opTypeToStrings (OpType {opKind=ok, opArgs=oa, opRes=or}) = (show ok, map show oa, show or)
	
-- Get strings to represent a predicate-mapping
getPredTypeStringsList::(Map.Map (Id.Id) (Set.Set PredType))->[(String, [[String]])]
getPredTypeStringsList pm = map (\(id, pts) -> (show id,
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
opMapStringsToOpMap ops = foldr (\(id, ops) m -> Map.insert (stringToId id) (Set.fromList $ map mkOpType ops) m) Map.empty ops where  
	mkOpType::(String,[String],String)->OpType
	mkOpType (opkind, args, res) = OpType
					(if opkind == "Partial" then CASLBasic.Partial else CASLBasic.Total)
					(map stringToId args)
					(stringToId res)

{-
Predicate-mapping
-}
predMapStringsToPredMap::[(String, [[String]])]->(Map.Map Id.Id (Set.Set PredType))
predMapStringsToPredMap pres = foldr (\(id, args) m -> Map.insert
							(stringToId id)
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
		,extendedInfo = () -- ignored
	}

-- we need more info to make a graph...
-- just the DGraph is not sufficient...
--showgraph :: DGraph -> IO()
--showgraph dg = do
--		showGraph "no-file" defaultHetcatsOpts (Just ((ASL.Lib_id (ASL.Direct_link "" [])), (ASL.Lib_defn (ASL.Lib_id (ASL.Direct_link "" [])) [] [] []), dg, Map.empty)) 


{- Call this function as follows:
ghci -fglasgow-exts -fno-monomorphism-restriction  -fallow-overlapping-instances -fallow-undecidable-instances -ighc -ifgl -ihxt
:l hets.hs
:module +Common.Lib.Graph
Just (ln,ast,dg,libenv)<-run "../CASL-lib/List.casl"
-}

		
-- Filter out links for collecting sorts, rels, preds...
-- only four types of links are allowed (and afaik needed for this)
linkFilter::[(Graph.LEdge DGLinkLab)]->[(Graph.LEdge DGLinkLab)]
linkFilter [] = []
linkFilter ((l@(n,m,link)):rest) =
	(case dgl_type link of
		LocalDef -> [l]
		GlobalDef -> [l]
		-- LocalThm's with 'Mono' cons tend to link back to their 
		-- origin, effectively wiping out the sorts, etc...
		(LocalThm tls1 c tls2) -> case c of Def -> [l]; _ -> []
		(GlobalThm tls1 c tls2) -> case c of Def -> [l]; _ -> []
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
		
		

-- gets something from a DGNode or returns default value for DGRefS
getFromDGNode::DGNodeLab->(DGNodeLab->a)->a->a
getFromDGNode node get def =
	if isDGRef node then def else
		get node
		
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
getFromNodeDelta dg n get delta def =
	let	node = (\(Just a) -> a) $ Graph.lab dg n
		innodes = inputNodeLabs dg n
	in
		foldl (\r n ->
			delta r $ getFromDGNode n get def
			) (getFromDGNode node get def) innodes
			
getFromNodeDeltaM::DGraph->Graph.Node->(DGNodeLab->Bool)->(DGNodeLab->a)->(DGraph->Graph.Node->a)->(a->a->a)->a
getFromNodeDeltaM dg n usenode getnode getgraphnode delta =
	let	node = (\(Just a) -> a) $ Graph.lab dg n
		innodes = inputNodes dg n
	in
		foldl (\r n ->
			delta r $ getFromNode dg n usenode getnode getgraphnode
			) (getFromNode dg n usenode getnode getgraphnode) innodes
	
			
-- helper function to extract an element from the caslsign of a node
-- or to provide a safe default
getFromCASLSign::DGNodeLab->(CASLSign->a)->a->a
getFromCASLSign node get def =
	getFromDGNode
		node
		(\n ->
			let caslsign = getJustCASLSign $ getCASLSign (dgn_sign n)
			in get caslsign
		)
		def
		
getFromCASLSignM::DGraph->Graph.Node->(CASLSign->a)->a
getFromCASLSignM dg n get =
	let	node = (\(Just a) -> a) $ Graph.lab dg n
		caslsign = if isDGRef node
					then signViaMorphism dg n
					else getJustCASLSign $ getCASLSign (dgn_sign node)
	in	get caslsign
			
		
-- wrapper around 'getFromNodeDelta' for CASLSign-specific operations
getFromCASLSignDelta::DGraph->Graph.Node->(CASLSign->a)->(a->a->a)->a->a
getFromCASLSignDelta dg n get delta def =
	getFromNodeDelta dg n (\g -> getFromCASLSign g get def) delta def

getFromCASLSignDeltaM::DGraph->Graph.Node->(CASLSign->a)->(a->a->a)->a->a
getFromCASLSignDeltaM dg n get delta _ =
	getFromNodeDeltaM dg n
		(\_ -> False)
		(\g -> undefined::a)
		(\dg' n' -> getFromCASLSignM dg' n' get)
		delta
	
-- extract all sorts from a node that are not imported from other nodes
getNodeDeltaSorts::DGraph->Graph.Node->(Set.Set SORT)
getNodeDeltaSorts dg n = getFromCASLSignDeltaM dg n sortSet Set.difference Set.empty

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
	
-- get CASL-formulas from a node
getNodeSentences::DGNodeLab->[Ann.Named CASLFORMULA]
getNodeSentences (DGRef _ _ _ _ _) = []
getNodeSentences node =
	let
		(Just csen) = (\(G_theory _ _ thsens) -> (cast thsens)::(Maybe (ThSens CASLFORMULA))) $ dgn_theory node
	in toNamedList csen

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
			Map.insert (adjustNodeName ("AnonNode#"++(show n)) $ getDGNodeName node) (mapper dg n) mapping
		) Map.empty $ Graph.labNodes dg

type Imports = Set.Set (String, (Maybe MorphismMap))
type Sorts = Set.Set SORT
type Rels = Rel.Rel SORT
type Preds = Map.Map Id.Id (Set.Set PredType)
type Ops = Map.Map Id.Id (Set.Set OpType)
type Sens = Set.Set (Ann.Named CASLFORMULA)

type ImportsMap = Map.Map String Imports
type SortsMap = Map.Map String Sorts
type RelsMap = Map.Map String Rels
type PredsMap = Map.Map String Preds
type OpsMap = Map.Map String Ops
type SensMap = Map.Map String Sens

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

-- create a mapping of node-name -> Relation of Sorts for all nodes
getRelationsWithNodeNames::DGraph->RelsMap
getRelationsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaRelations Rel.null

-- create a mapping of node-name -> Predicate-Mapping (PredName -> Set of PredType)
getPredMapsWithNodeNames::DGraph->PredsMap
getPredMapsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaPredMaps Map.null

-- create a mapping of node-name -> Operand-Mapping (OpName -> Set of OpType)
getOpMapsWithNodeNames::DGraph->OpsMap
getOpMapsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaOpMaps Map.null

-- get a mapping of node-name -> Set of Sentences (CASL-formulas)
getSentencesWithNodeNames::DGraph->SensMap
getSentencesWithNodeNames dg = getNodeNameMapping dg getNodeDeltaSentences Set.null

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
		(Just (_, _, _, lenv)) <- run f
		return (
			foldl (\map (lname, (_,_,dg)) ->
				Map.insert lname (getAll dg) map
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
			edges = filter (\(a,b,_) -> (a == from) && (b==n)) $ Graph.labEdges dgr
			caslmorph = case edges of
				[] -> emptyCASLMorphism
				(l:r) -> getCASLMorph l
			mmm = if isEmptyMorphism caslmorph
				then
					Nothing
				else
					(Just (makeMorphismMap caslmorph))
		in
			((adjustNodeName ("AnonNode#"++(show from)) $ getDGNodeName node), mmm):names
		) [] $ inputLNodes dgr n ) Set.null
	
adjustNodeName::String->String->String
adjustNodeName def [] = def
adjustNodeName _ name = name

-- get a set of all names for the nodes in the DGraph
getNodeNames::DGraph->(Set.Set (Graph.Node, String))
getNodeNames dg =
	fst $ foldl (\(ns, num) (n, node) ->
		(Set.insert (n, adjustNodeName ("AnonNode#"++(show num)) $ getDGNodeName node) ns, num+1)
		) (Set.empty, 1) $ Graph.labNodes dg
		
partition::(a->Bool)->[a]->([a], [a])
partition left =
	foldl (\(rl, rr) a -> if left a then (a:rl, rr) else (rl, a:rr)) ([],[]) 
		
-- | get two sets of node nums and names. first set are nodes, second are refs
getNodeNamesNodeRef::DGraph->(Set.Set (Graph.Node, String), Set.Set (Graph.Node, String))
getNodeNamesNodeRef dg =
	let
		lnodes = Graph.labNodes dg
		(nodes, refs) = partition (\(_,n) -> not $ isDGRef n) lnodes
		nnames = map (\(n, node) -> (n, adjustNodeName ("AnonNode#"++(show n)) $ getDGNodeName node)) nodes
		rnames = map (\(n, node) -> (n, adjustNodeName ("AnonRef#"++(show n)) $ getDGNodeName node)) refs
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
	findNodeNameFor importsMap sensMap (\n -> not $ Set.null $ Set.filter (\n -> (senName n) == sName) n) name
	
findNodeNameForSentence::ImportsMap->SensMap->CASLFORMULA->String->(Maybe String)
findNodeNameForSentence importsMap sensMap s name =
	findNodeNameFor importsMap sensMap (\n -> not $ Set.null $ Set.filter (\n -> (sentence n) == s) n) name
	

-- | Reduce a DevGraph by backtracking importing links
createReducedDGraph::DGraph->DGraph
createReducedDGraph dg =
	let	lnodes = Graph.labNodes dg
		ledges = Graph.labEdges dg
	in Graph.mkGraph (map (createReducedNode dg) lnodes) ledges
	

buildCASLSentenceDiff::(ThSens CASLFORMULA)->(ThSens CASLFORMULA)->(ThSens CASLFORMULA)
buildCASLSentenceDiff = Set.difference

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
	node2@(DGNode { dgn_theory = th2}) =
		let	sens1 = (\(G_theory _ sign sens) -> (cast sens)::(Maybe (ThSens CASLFORMULA))) th1
			sens2 = (\(G_theory _ sign sens) -> (cast sens)::(Maybe (ThSens CASLFORMULA))) th2
			sign1 = (\(G_theory _ sign sens) -> (cast sign)::(Maybe CASLSign)) th1
			sign2 = (\(G_theory _ sign sens) -> (cast sign)::(Maybe CASLSign)) th2
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
	(CASL.Morphism.Morphism { CASL.Morphism.sort_map = sm, CASL.Morphism.fun_map = fm, CASL.Morphism.pred_map = pm }) =
		let	mcsi = (\(G_theory lid sign sens) -> (cast sign)::(Maybe CASLSign)) th
			mcse = (\(G_theory lid sign sens) -> (cast sens)::(Maybe (ThSens CASLFORMULA))) th
		in case mcsi of
			(Just (Sign ss sr om ao oldpm vm se ev ei)) ->
				let	funlist = (map (\(_, (f, fk)) -> f) $ Map.toList fm)::[Id.Id]
					predlist = (map (\(_, p) -> p) $ Map.toList pm)::[Id.Id]
					newpredmap = foldl (\nmap id ->
						Map.filterWithKey (\k _ -> k /= id) nmap
						) oldpm predlist
					newopmap = foldl (\nmap id ->
						Map.filterWithKey (\k _ -> k /= id) nmap
						) om funlist
					newassocmap = foldl (\nmap id ->
						Map.filterWithKey (\k _ -> k /= id) nmap
						) ao funlist
				in	case mcse of
						(Just csens) -> n { dgn_theory = (G_theory CASL (Sign ss sr newopmap newassocmap newpredmap vm se ev ei) csens) }
						_ -> error "Could not cast sentences to (ThSens CASLFORMULA) (but a CASLSign was cast... (wierd!))"
			Nothing -> n  -- maybe this node is not CASL-related... leave it as is
stripCASLMorphism n@(DGRef {dgn_libname = ln}) _ = n -- can DGRefS have a morphism from another node in the graph ?


stripCASLMorphisms::DGraph->(Graph.LNode DGNodeLab)->(Graph.LNode DGNodeLab)
stripCASLMorphisms dg (n, node) =
	case node of
		(DGRef {dgn_libname = ln}) -> (n, node) -- no need to do this for a reference...
		_ ->
			let	incoming = filter ( \(_,tn,_) -> n == tn ) $ Graph.labEdges dg
				imports = filter ( \(_,_,iedge) ->
					case iedge of
						DGLink m t o ->
							case t of
								LocalDef -> True
								GlobalDef -> True
								HidingDef -> True
								_ -> False
						_ -> False
					) incoming
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
		)

makeMorphismMap::(Morphism () () ())->MorphismMap
makeMorphismMap (Morphism _ _ sortmap funmap predmap _) =
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
		(sortmap, newfunmap, newpredmap)
		
removeMorphismSorts::MorphismMap->Sorts->Sorts
removeMorphismSorts (sm,_,_) sorts =
	let
		msorts = Map.elems sm
	in
		Set.filter (\s -> not $ elem s msorts) sorts
		
addMorphismSorts::MorphismMap->Sorts->Sorts
addMorphismSorts (sm,_,_) sorts =
	let
		msorts = Map.elems sm
	in	
		Set.union sorts $ Set.fromList msorts
		
removeMorphismOps::MorphismMap->Ops->Ops
removeMorphismOps (_,om,_) ops =
	let
		mops = map fst $ Map.elems om
	in
		Map.filterWithKey (\k _ -> not $ elem k mops) ops
		
addMorphismOps::MorphismMap->Ops->Ops
addMorphismOps (_,om,_) ops =
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
removeMorphismPreds (_,_,pm) preds =
	let
		mpreds = map fst $ Map.elems pm
	in
		Map.filterWithKey (\k _ -> not $ elem k mpreds) preds 
	
addMorphismPreds::MorphismMap->Preds->Preds
addMorphismPreds (_,_,pm) preds =
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
morphismMapToMorphism (sortmap, funmap, predmap) =
	let
		mfunmap = Map.fromList $ map (\((sid, sot),t) -> ((sid, sot { opKind = Partial }),t)) $ Map.toList $ Map.map (\(tid,(OpType fk _ _)) ->
			(tid, fk) ) funmap
		mpredmap = Map.map (\(tid,_) ->	tid ) predmap
	in
		Morphism (emptySign ()) (emptySign ()) sortmap mfunmap mpredmap ()
		
applyMorphHiding::MorphismMap->[Id.Id]->MorphismMap
applyMorphHiding mm [] = mm
applyMorphHiding (sortmap, funmap, predmap) hidings =
	(
		 Map.filterWithKey (\sid _ -> not $ elem sid hidings) sortmap
		,Map.filterWithKey (\(sid,_) _ -> not $ elem sid hidings) funmap
		,Map.filterWithKey (\(sid,_) _ -> not $ elem sid hidings) predmap
	)
	
buildMorphismSign::MorphismMap->[Id.Id]->CASLSign->CASLSign
buildMorphismSign
	mm@(mmsm, mmfm, mmpm) 
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
			ext
	
applySignHiding::CASLSign->[Id.Id]->CASLSign
applySignHiding 
	(Sign sortset sortrel opmap assocops predmap varmap sens envdiags ext)
	hidings =
	Sign
		(Set.filter (not . flip elem hidings) sortset)
		(Rel.fromList $ filter (\(id,_) -> not $ elem id hidings) $ Rel.toList sortrel)
		(Map.filterWithKey (\sid _ -> not $ elem sid hidings) opmap)
		(Map.filterWithKey (\sid _ -> not $ elem sid hidings) assocops)
		(Map.filterWithKey (\sid _ -> not $ elem sid hidings) predmap)
		(Map.filter (\varsort -> not $ elem varsort hidings) varmap)
		sens
		envdiags
		ext

createLocalNode::DGraph->(Graph.LNode DGNodeLab)->(Graph.LNode DGNodeLab)
createLocalNode dg (n, node) =
	case node of
		(DGRef {dgn_libname = ln}) -> (n, node) -- this is actually bad 
			-- there is often a Morphism associated with a DGRef so should
			-- we strip to morphed symbols from this ?
		_ ->
			let	incoming = filter ( \(_,tn,_) -> n == tn ) $ Graph.labEdges dg
				imports = filter ( \(_,_,iedge) ->
					case iedge of
						DGLink m t o ->
							case t of
								LocalDef -> True
								GlobalDef -> True
								HidingDef -> True
								_ -> False
						_ -> False
					) incoming
				innodes = map ( \(n,_,_) -> (\(Just a) -> a) $ Graph.lab dg n ) incoming
			in
				(n, foldl (\lnode inode -> buildCASLNodeDiff lnode inode) node innodes)
		
createReducedNode::DGraph->(Graph.LNode DGNodeLab)->(Graph.LNode DGNodeLab)
createReducedNode dg (n,node) = 
	case node of
		(DGRef {dgn_libname = ln}) -> (n, node)
		_ ->
			let	incoming = filter ( \(_,tn,_) -> n == tn ) $ Graph.labEdges dg
				(li,gi,hi) =
					foldl ( \(nli, ngi, nhi) edge@(_,_,iedge) ->
					case iedge of
						DGLink m t o ->
							case t of
								LocalDef -> (nli++[edge], ngi, nhi)
								GlobalDef -> (nli, ngi++[edge], nhi) 
								HidingDef -> (nli, ngi, nhi++[edge])
								_ -> (nli, ngi, nhi)
						_ -> (nli, ngi, nhi)
						) ([],[],[]) incoming
				localnodes = map ( \(n,_,_) -> (\(Just a) -> (n, a)) $ Graph.lab dg n ) li
				globalnodes = map ( \(n,_,_) -> (\(Just a) -> (n, a)) $ Graph.lab dg n ) gi
				hidingnodes = map ( \(n,_,_) -> (\(Just a) -> (n, a)) $ Graph.lab dg n ) hi
			in
				stripCASLMorphisms dg (n,
					foldl (\nnode (inn, inode) ->
						let (rn, rnode) = createLocalNode dg (inn, inode)
						in buildCASLNodeDiff nnode rnode
						)
					(foldl (\nnode (inn, inode) ->
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


