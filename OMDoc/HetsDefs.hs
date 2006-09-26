{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

  Additional definitions for interfacing Hets
-}
module OMDoc.HetsDefs
  (
      module Driver.Options
    , module OMDoc.HetsDefs
    , module Syntax.AS_Library
    , module Common.GlobalAnnotations
  )
  where

import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Graph as Graph 

import Common.AS_Annotation
import Common.GlobalAnnotations (emptyGlobalAnnos)

import Syntax.AS_Library --(LIB_NAME(),LIB_DEFN()) 

import Driver.Options

import Logic.Grothendieck hiding (Morphism)

import Static.DevGraph

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

import qualified Logic.Prover as Prover

import qualified Common.OrderedMap as OMap

import qualified Debug.Trace as Debug.Trace

import qualified Data.List as Data.List

import Data.Maybe (fromMaybe)

import OMDoc.Util 

-- | shortcut to Debug.Trace.trace
dtt::String->a->a
dtt = Debug.Trace.trace

-- | "alias" for defaultHetcatsOpts (for export)
dho::HetcatsOpts
dho = defaultHetcatsOpts

-- | transform a list of named sentences to a list with name-sentence-tuples
transSen::[Ann.Named CASLFORMULA]->[(String, CASLFORMULA)]
transSen [] = []
transSen ((Ann.NamedSen n _ _ s):rest) = [(n, s)] ++ transSen rest

-- | transform a list of name-sentence-tuples to a list of named sentences
transSenBack::[(String, CASLFORMULA)]->[Ann.Named CASLFORMULA]
transSenBack [] = []
transSenBack ((n, s):rest) = (Ann.NamedSen n False False s):(transSenBack rest)

-- | strip names from a list of name-formula-tuples
getPureFormulas::[(String, CASLFORMULA)]->[CASLFORMULA]
getPureFormulas [] = []
getPureFormulas ((_, f):rest) = [f] ++ getPureFormulas rest

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
  CASLSignStrings {  sortSetStrings=( getSetStringList $ sortSet cs )
        ,sortRelStrings=( getRelStringsList $ sortRel cs)
        ,opMapStrings = ( getOpMapStringsList $ opMap cs)
        ,predMapStrings = ( getPredTypeStringsList $ predMap cs )
       }

-- Create a simple id from a string
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
    HidingDef -> [l]
    (FreeDef {}) -> [l]
    (CofreeDef {}) -> [l]
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

innNodes::DGraph->Graph.Node->[Graph.LNode DGNodeLab]
innNodes dg n =
  map
    (\(m,_,_) ->
      (m, fromMaybe (error "corrupt graph!") (Graph.lab dg m))
    )
    (Graph.inn dg n)

getCASLMorphLL::DGLinkLab->(CASL.Morphism.Morphism () () ())
getCASLMorphLL edge =
  fromMaybe (error "cannot cast morphism to CASL.Morphism")  $ (\(Logic.Grothendieck.GMorphism _ _ morph) -> Data.Typeable.cast morph :: (Maybe (CASL.Morphism.Morphism () () ()))) $ dgl_morphism edge

getCASLMorph::(Graph.LEdge DGLinkLab)->(CASL.Morphism.Morphism () () ())
getCASLMorph (_,_,edge) = getCASLMorphLL edge

getMCASLMorph::(Graph.LEdge DGLinkLab)->(Maybe (CASL.Morphism.Morphism () () ()))
getMCASLMorph (_,_,edge) = (\(Logic.Grothendieck.GMorphism _ _ morph) -> Data.Typeable.cast morph :: (Maybe (CASL.Morphism.Morphism () () ()))) $ dgl_morphism edge

signViaMorphism::DGraph->Graph.Node->CASLSign
signViaMorphism dg n =
  let outedges = Graph.out dg n
  in  if outedges == [] then
        emptySign ()
      else
        let
          mcaslmorph = getMCASLMorph $ head outedges
        in  case mcaslmorph of
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
  let node = (\(Just a) -> a) $ Graph.lab dg n
  in  if usenode node then
      getnode node
    else
      getgraphnode dg n
      
-- generic function to calculate a delta between a node and the nodes it
-- imports from
getFromNodeDelta::DGraph->Graph.Node->(DGNodeLab->a)->(a->a->a)->a->a
getFromNodeDelta dg n get' delta def =
  let
    node = (\(Just a) -> a) $ Graph.lab dg n
    innodes = inputNodeLabs dg n
  in
    foldl (\r n' ->
      delta r $ getFromDGNode n' get' def
      ) (getFromDGNode node get' def) innodes
      
getFromNodeDeltaM::DGraph->Graph.Node->(DGNodeLab->Bool)->(DGNodeLab->a)->(DGraph->Graph.Node->a)->(a->a->a)->a
getFromNodeDeltaM dg n usenode getnode getgraphnode delta =
  let --node = (\(Just a) -> a) $ Graph.lab dg n
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
  (Eq b, Show b)=>
  DGraph->
  Graph.Node->
  (DGNodeLab->Bool)->
  (DGNodeLab->a)->
  (DGraph->Graph.Node->a)->
  (a->[b])->
  (b->DGraph->Graph.Node->Bool)->
  (Graph.LEdge DGLinkLab->b->b)->
  ([WithOriginNode b]->c)->
  c
getFromNodeWithOriginsM dg n usenode getnode getgraphnode getcomponents isorigin morph createresult =
  let
    item' = getFromNode dg n usenode getnode getgraphnode
    components = getcomponents item'
    traced = foldl (\traced' c ->
      let
        ttm = traceToMorph dg n c [] isorigin morph
--        mo = Debug.Trace.trace ("Trace : " ++ show ttm) $ traceMorphingOrigin dg n c [] isorigin morph
      in
        traced' ++ [case ttm of
          OBNothing -> mkWON c n -- current node is origin
          (OBMorphism {}) -> mkWON c n -- current node is origin
          (OBOrigin o) -> mkWON c o]
        ) [] components
  in
    createresult traced
    
getFromNodeWithOriginsMSet::
  (Eq a, Show a, Ord a)=>
  DGraph->
  Graph.Node->
  (DGNodeLab->Bool)->
  (DGNodeLab->Set.Set a)->
  (DGraph->Graph.Node->Set.Set a)->
  (a->DGraph->Graph.Node->Bool)->
  (Graph.LEdge DGLinkLab->a->a)->
  Set.Set (WithOriginNode a)
getFromNodeWithOriginsMSet dg n usenode getset getgraphset isorigin morph =
  getFromNodeWithOriginsM dg n usenode getset getgraphset Set.toList isorigin morph Set.fromList

getFromCASLSignWithOrigins::
  (Eq b, Show b)=>
  DGraph->Graph.Node->(CASLSign->a)->(a->[b])->(b->a->Bool)
  ->(Graph.LEdge DGLinkLab->b->b)
  ->([WithOriginNode b]->c)
  ->c
getFromCASLSignWithOrigins dg n caslget getcomponents isorigin morph createresult =
  getFromNodeWithOriginsM dg n (\_ -> False) (\_ -> undefined::a)
    (\dg' n' -> getFromCASLSignM dg' n' caslget)
    getcomponents
    (\i dg' n' -> isorigin i (getFromCASLSignM dg' n' caslget))
    morph
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
    sortMorph
    Set.fromList

getSortsFromNodeWithMorphOrigins::
  DGraph->Graph.Node->SortsWO
getSortsFromNodeWithMorphOrigins dg n =
  getFromCASLSignWithOrigins
    dg
    n
    sortSet
    Set.toList
    Set.member
    sortMorph
    Set.fromList


    
getOpsMapFromNodeWithOrigins::
  DGraph->Graph.Node->OpsWO
getOpsMapFromNodeWithOrigins dg n =
  getFromCASLSignWithOrigins
    dg
    n
    opMap
    Map.toList
    (\(mid, mtype) om -> case Map.lookup mid om of
      Nothing -> False
      (Just (mtype')) -> mtype == mtype')
    idMorph
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
    (\(mid, mtype) om -> case Map.lookup mid om of
      Nothing -> False
      (Just (mtype')) -> mtype == mtype')
    idMorph
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
    (\(mid, mtype) om -> case Map.lookup mid om of
      Nothing -> False
      (Just (mtype')) -> mtype == mtype')
    idMorph
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
    idMorph --sentences don't morph
      
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
              {-  there was no previous node. this means the start
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
            -- get possible node for import (OMDDoc-specific)
            innodes = inputNodes dg n
            -- find first higher origin
            mo = first
                (\n' -> traceOrigin dg n' (n:visited) test)
                innodes
          in
            -- if there is no higher origin, this node is the origin
            case mo of
              Nothing ->
                {-  if further search fails, then this
                  node must be the origin -}
                (Just n) 
              (Just _) ->
                -- else use found origin
                mo

-- this works, but still renaming must be handled special...
traceMorphingOrigin::
  (Eq a, Show a)=>
  DGraph
  ->Graph.Node
  ->a
  ->[Graph.Node]
  ->(a->DGraph->Graph.Node->Bool)
  ->(Graph.LEdge DGLinkLab->a->a)
  ->Maybe Graph.Node
traceMorphingOrigin
  dg
  n
  a
  visited
  atest
  amorph =
  if (elem n visited) -- circle encountered...
    then
      Nothing -- we are performing a depth-search so terminate this tree
    else
      -- check if this node still carries the attribute
      if not $ atest a dg n
        then
          -- it does not, but the previous node did
          if (length visited) == 0
            then
              {-  there was no previous node. this means the start
                node did not have the attribute searched for -}
              Debug.Trace.trace
                "traceMorphismOrigin: search from invalid node"
                Nothing
            else
              -- normal case, head is the previous node
              (Just (head visited))
        else
          -- this node still carries the attribute
          let
            -- get possible node for import (OMDDoc-specific)
            -- find first higher origin
            mo = first
                (\edge@(from, _, _) ->
                  let
                    ma = amorph edge a
                  in
                    if (ma /= a)
                      then
                        Debug.Trace.trace
                          ("Stopping origin trace on " ++ show a ++ " to " ++ show ma)
                          Nothing
                      else
                        traceMorphingOrigin dg from ma (n:visited) atest amorph
                )
                (Graph.inn dg n)
          in
            -- if there is no higher origin, this node is the origin
            case mo of
              Nothing ->
                {-  if further search fails, then this
                  node must be the origin -}
                (Just n) 
              (Just _) ->
                -- else use found origin
                mo

data OriginBranch = OBOrigin Graph.Node | OBMorphism Graph.Node | OBNothing
  deriving Show

traceToMorph::
  (Eq a, Show a)=>
  DGraph
  ->Graph.Node
  ->a
  ->[Graph.Node]
  ->(a->DGraph->Graph.Node->Bool)
  ->(Graph.LEdge DGLinkLab->a->a)
  ->OriginBranch
traceToMorph
  dg
  n
  a
  visited
  atest
  amorph =
  if (elem n visited) -- circle encountered...
    then
      OBNothing
    else
      if not $ atest a dg n
        then
          if (length visited) == 0
            then
              OBNothing
            else
              OBOrigin (head visited)
        else
          let
            inedges = Graph.inn dg n
            branches =
              map
                (\edge@(from, _, _) ->
                  let
                    am = amorph edge a
                  in
                    (am, traceToMorph dg from am (n:visited) atest amorph)
                )
                inedges
            remapped =
              map
                (\(am, ob) ->
                  if am == a
                    then
                      ob
                    else
                      case ob of
                        (OBOrigin x) -> OBMorphism x
                        _ -> ob
                )
                branches
          in
            case
              Data.List.find
                (\ob -> case ob of (OBOrigin {}) -> True; _ -> False)
                remapped
            of
              (Just x) ->
             --   Debug.Trace.trace
               --   ("Found real origin for " ++ show a ++ " at " ++ show n)
                  x
              _ ->
                case
                  Data.List.find
                    (\ob -> case ob of (OBMorphism {}) -> True; _ -> False)
                    remapped
                of
                  (Just x) ->
               --     Debug.Trace.trace
                 --     ("Found only morph origin for " ++ show a ++ " at " ++ show n)
                      x
                  _ ->
                    if null remapped
                      then
                   --     Debug.Trace.trace 
                     --     ("Found current node as origin for " ++ show a ++ " at " ++ show n)
                          (OBOrigin n)
                      else
                        OBNothing


-- embed old checks...
nullMorphCheck::forall a . (DGraph->Graph.Node->Bool)->(DGraph->Graph.Node->a->Bool)
nullMorphCheck check = (\dg n _ -> check dg n)

idMorph::forall a . Graph.LEdge DGLinkLab->a->a
idMorph _ a = a

morphByMorphism::forall a . (Morphism () () ()->a->a)->(Graph.LEdge DGLinkLab->a->a)
morphByMorphism morph =
  (\(_, _, dgl) a ->
    let
      caslmorph = getCASLMorphLL dgl
    in
      morph caslmorph a
  )

sortMorph::Graph.LEdge DGLinkLab->SORT->SORT
sortMorph = morphByMorphism sortBeforeMorphism
    

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
  let
    node = (\(Just a) -> a) $ Graph.lab dg n
    caslsign = if isDGRef node
          --then signViaMorphism dg n
          then getJustCASLSign $ getCASLSign (dgn_sign node)
          else getJustCASLSign $ getCASLSign (dgn_sign node)
  in  get' caslsign
      
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
  
getProverSentences::G_theory->Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)
getProverSentences (G_theory _ _ thsens) =
  let
    (Just csen) = ((cast thsens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))))
  in
    csen

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
   
-- added Integer to keep the order of imports (to OMDoc, from OMDoc)
type Imports = Set.Set (Int, (String, (Maybe MorphismMap), HidingAndRequationList, Bool))
type Sorts = Set.Set SORT
type Rels = Rel.Rel SORT
type Preds = Map.Map Id.Id (Set.Set PredType)
type Ops = Map.Map Id.Id (Set.Set OpType)
type Sens = Set.Set (Ann.Named CASLFORMULA)

type NODE_NAMEWO = WithOriginNode NODE_NAME
type SORTWO = WithOriginNode SORT
type IdWO = WithOriginNode Id.Id
type SentenceWO = WithOriginNode (Ann.Named CASLFORMULA)


type ImportsWO = Set.Set (Int, (NODE_NAMEWO, (Maybe MorphismMap), HidingAndRequationList))
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

--type AllMaps = (ImportsMap, SortsMap, RelsMap, PredsMap, OpsMap, SensMap)

{-
instance Show AllMaps where
  show (imports, sorts, rels, preds, ops, sens) =
    "Imports:\n" ++ show imports ++
    "\nSorts:\n" ++ show sorts ++
    "\nRelations:\n" ++ show rels ++
    "\nPredicates:\n" ++ show preds ++
    "\nOperators:\n" ++ show ops ++
    "\nSentences:\n" ++ show sens
-}

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

getSortsWOMorphWithNodeDGNamesWO::DGraph->SortsMapDGWO
getSortsWOMorphWithNodeDGNamesWO dg =
  getNodeDGNameMappingWO dg getSortsFromNodeWithMorphOrigins Set.null

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

findSortOrigin::LibEnv->LIB_NAME->Graph.Node->Id.Id->Maybe (LIB_NAME, Graph.Node)
findSortOrigin lenv ln nn sid =
  let
    dg =
      devGraph
        $
        Map.findWithDefault (error ("No such libname : " ++ show ln)) ln lenv
    node = Data.Maybe.fromMaybe (error ("No such node : #" ++ show nn)) $ Graph.lab dg nn
    sortswomap = getSortsWOWithNodeDGNamesWO dg
    nodesorts = Map.findWithDefault Set.empty (mkWON (dgn_name node) nn) sortswomap
  in
    if isDGRef node
      then
        findSortOrigin lenv (dgn_libname node) (dgn_node node) sid
      else
        case
          Set.toList
            $
            Set.filter (\wosort -> woItem wosort == sid) nodesorts
        of
          [] -> Nothing
          (wosort:_) ->
            if woOrigin wosort == nn
              then
                Just (ln, nn)
              else
                findSortOrigin lenv ln (woOrigin wosort) sid

findPredOrigin::LibEnv->LIB_NAME->Graph.Node->Id.Id->PredType->Maybe (LIB_NAME, Graph.Node)
findPredOrigin lenv ln nn pid pt =
  let
    dg =
      devGraph
        $
        Map.findWithDefault (error ("No such libname : " ++ show ln)) ln lenv
    node = Data.Maybe.fromMaybe (error ("No such node : #" ++ show nn)) $ Graph.lab dg nn
    predswomap = getPredMapsWOWithNodeDGNamesWO dg
    nodepreds = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) predswomap
  in
    if isDGRef node
      then
        findSortOrigin lenv (dgn_libname node) (dgn_node node) pid
      else
        case
          Map.toList
            $
            Map.filterWithKey (\wopid pts -> woItem wopid == pid && Set.member pt pts) nodepreds
        of
          [] -> Nothing
          ((wopid, _):_) ->
            if woOrigin wopid == nn
              then
                Just (ln, nn)
              else
                findSortOrigin lenv ln (woOrigin wopid) pid

findOpOrigin::LibEnv->LIB_NAME->Graph.Node->Id.Id->OpType->Maybe (LIB_NAME, Graph.Node)
findOpOrigin lenv ln nn oid ot =
  let
    dg =
      devGraph
        $
        Map.findWithDefault (error ("No such libname : " ++ show ln)) ln lenv
    node = Data.Maybe.fromMaybe (error ("No such node : #" ++ show nn)) $ Graph.lab dg nn
    opswomap = getOpMapsWOWithNodeDGNamesWO dg
    nodeops = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) opswomap
  in
    if isDGRef node
      then
        findSortOrigin lenv (dgn_libname node) (dgn_node node) oid
      else
        case
          Map.toList
            $
            Map.filterWithKey (\wooid ots -> woItem wooid == oid && Set.member ot ots) nodeops
        of
          [] -> Nothing
          ((wooid, _):_) ->
            if woOrigin wooid == nn
              then
                Just (ln, nn)
              else
                findSortOrigin lenv ln (woOrigin wooid) oid
    

--debugging-function
findPredsByName::PredsMap->String->[(String, (Id.Id, Set.Set PredType))]
findPredsByName pm name =
  let
    nameid = stringToId name
  in
    foldl (\l (k, v) ->
      foldl (\l' (pid, v') ->
        if pid == nameid
          then
            l' ++ [(k, (pid, v'))]
          else
            l'
      ) l (Map.toList v)
    ) [] (Map.toList pm)

getPredMapsWithNodeDGNames::DGraph->Map.Map NODE_NAME Preds
getPredMapsWithNodeDGNames dg = getNodeDGNameMapping dg getNodeDeltaPredMaps Map.null

getPredMapsWOWithNodeDGNamesWO::DGraph->PredsMapDGWO
getPredMapsWOWithNodeDGNamesWO dg = getNodeDGNameMappingWO dg getPredsMapFromNodeWithOrigins Map.null 

--debugging-function
findPredsWODGByName::PredsMapDGWO->String->[(NODE_NAMEWO, (IdWO, Set.Set PredType))]
findPredsWODGByName pm name =
  let
    nameid = stringToId name
  in
    foldl (\l (k, v) ->
      foldl (\l' (pid, v') ->
        if (wonItem pid) == nameid
          then
            l' ++ [(k, (pid, v'))]
          else
            l'
      ) l (Map.toList v)
    ) [] (Map.toList pm)
    
-- create a mapping of node-name -> Operand-Mapping (OpName -> Set of OpType)
getOpMapsWithNodeNames::DGraph->OpsMap
getOpMapsWithNodeNames dg = getNodeNameMapping dg getNodeDeltaOpMaps Map.null

--debugging-function
findOpsByName::OpsMap->String->[(String, (Id.Id, Set.Set OpType))]
findOpsByName om name =
  let
    nameid = stringToId name
  in
    foldl (\l (k, v) ->
      foldl (\l' (oid, v') ->
        if oid == nameid
          then
            l' ++ [(k, (oid, v'))]
          else
            l'
      ) l (Map.toList v)
    ) [] (Map.toList om)

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

{-getAll::DGraph->AllMaps
getAll dg = (
  getNodeImportsNodeNames dg,
  getSortsWithNodeNames dg,
  getRelationsWithNodeNames dg,
  getPredMapsWithNodeNames dg,
  getOpMapsWithNodeNames dg,
  getSentencesWithNodeNames dg
  )
-}

getExternalLibNames::DGraph->(Set.Set LIB_NAME)
getExternalLibNames =
  Set.fromList . map dgn_libname . filter isDGRef . map snd . Graph.labNodes

-- get all axioms
getAxioms::[Ann.Named a]->[Ann.Named a]
getAxioms l = filter (\(NamedSen {isAxiom = iA}) -> iA) l

-- get all non-axioms
getNonAxioms::[Ann.Named a]->[Ann.Named a]
getNonAxioms l = filter (\(NamedSen {isAxiom = iA}) -> not iA) l

isEmptyMorphism::(Morphism a b c)->Bool
isEmptyMorphism (Morphism _ _ sm fm pm _) =
  Map.null sm && Map.null fm && Map.null pm

isEmptyCASLMorphism::CASL.Morphism.Morphism () () ()->Bool
isEmptyCASLMorphism m = CASL.Sign.isSubSig (\_ _ -> True) (msource m) (mtarget m)

isEmptyMorphismMap::MorphismMap->Bool
isEmptyMorphismMap (sm,om,pm,hs) =
  (Map.null sm && Map.null om && Map.null pm)

isNotHidingMorphismMap::MorphismMap->Bool
isNotHidingMorphismMap (_,_,_,hs) =
  (Set.null hs)

-- fetch the names of all nodes from wich sorts,rels, etc. are imported
-- this does not list all imports in the DGraph, just the ones that cause
-- sorts,rels, etc. to dissappear from a node
getNodeImportsNodeNames::DGraph->ImportsMap
getNodeImportsNodeNames dg = getNodeNameMapping dg (
  \dgr n -> Set.fromList $ 
   foldl (\names (c, (from,node)) ->
    let
      edges' = filter (\(a,b,_) -> (a == from) && (b==n)) $ Graph.labEdges dgr
      caslmorph = case edges' of
        [] -> emptyCASLMorphism
        (l:_) -> getCASLMorph l
      isglobal = case edges' of
        [] -> True
        ((_,_,e):_) -> case dgl_type e of
          (LocalDef) -> False
          _ -> True
      mmm = if isEmptyMorphism caslmorph
        then
          Nothing
        else
          (Just (makeMorphismMap caslmorph))
    in
      ((c, ((adjustNodeName ("AnonNode_"++(show from)) $ getDGNodeName node), mmm, ([],[]), isglobal))):names
    ) [] $ zip [1..] (inputLNodes dgr n) ) Set.null
  
getNodeImportsNodeDGNamesWO::DGraph->ImportsMapDGWO --Map.Map NODE_NAMEWO (Set.Set (NODE_NAMEWO, Maybe MorphismMap))
getNodeImportsNodeDGNamesWO dg = getNodeDGNameMappingWO dg (
  \dgr n -> Set.fromList $ 
   foldl (\names (c, (from,node)) ->
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
      ((c,((mkWON (dgn_name node) from), mmm, ([],[])))):names
    ) [] $ zip [1..] (inputLNodes dgr n) ) Set.null

switchTargetSourceMorph::Morphism () () ()->Morphism () () ()
switchTargetSourceMorph m =
  m { mtarget = msource m, msource = mtarget m }

getNodeAllImportsNodeDGNamesWOLL::
  DGraph
  ->Map.Map NODE_NAMEWO [(NODE_NAMEWO, Maybe DGLinkLab, Maybe MorphismMap)]
getNodeAllImportsNodeDGNamesWOLL dg = getNodeDGNameMappingWO dg (
  \dgr n -> 
    let
      incomming =
        (filter (\(_, tn, _) -> tn == n)) $ Graph.labEdges dgr
      incommingWN =
        map
          (\(fn,tn,iedge) ->
            case Graph.lab dgr fn of
              Nothing -> error "Corrupt Graph!"
              (Just inode) -> (fn,tn,iedge,inode)
          )
          incomming
    in
      foldl
        (\imports (fn, _, iedge, inode) ->
{-          let
            icaslmorph = getCASLMorph (undefined, undefined, iedge)
            caslmorph = case dgl_type iedge of 
              HidingDef -> switchTargetSourceMorph icaslmorph
              _ -> icaslmorph
            mm = makeMorphismMap caslmorph
            mmm = if isEmptyMorphismMap mm
              then
                Nothing
              else
                (Just mm) 
          in -}
            imports ++ [ ((mkWON (dgn_name inode) fn), Just iedge, Nothing) ]
        )
        []
        incommingWN
  )
  null

getNodeAllImportsNodeDGNamesWOLLo::
  DGraph
  ->Map.Map NODE_NAMEWO [(NODE_NAMEWO, Maybe DGLinkLab, Maybe MorphismMap)]
getNodeAllImportsNodeDGNamesWOLLo dg = getNodeDGNameMappingWO dg (
  \dgr n -> 
    foldl (\names (from,node) ->
      let
        edges' = filter (\(a,b,_) -> (a == from) && (b==n)) $ Graph.labEdges dgr
        mfirstedge = case edges' of
          (l:_) -> Just l
          _ -> Nothing
        mfirstll = case mfirstedge of
          Nothing -> Nothing
          (Just (_,_,ll)) -> Just ll
        caslmorph = case mfirstedge of
          (Just l) -> getCASLMorph l
          _ -> emptyCASLMorphism
        mmm = if isEmptyMorphism caslmorph
          then
            Nothing
          else
            (Just (makeMorphismMap caslmorph))
      in
        ((mkWON (dgn_name node) from), mfirstll, mmm):names
    ) [] (innNodes dgr n) )
    null
    
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
  let
    m_currentAttrib = Map.lookup name attribMap
    currentImports = Set.map (\(_, (a,_,_,_)) -> a) $ Map.findWithDefault Set.empty name importsMap
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
    (\m ->  let predSet = Map.findWithDefault Set.empty predId m
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
    (\m ->  let opSet = Map.findWithDefault Set.empty opId m
      in Set.member ot opSet )
    name
    
findNodeNameForOperatorWithFK::ImportsMap->OpsMap->(Id.Id, FunKind)->String->(Maybe String)
findNodeNameForOperatorWithFK importsMap opsMap (opId, fk) name =
  findNodeNameFor importsMap opsMap 
    (\m ->  let opSet = Map.findWithDefault Set.empty opId m
      in not $ null $ filter (\(OpType ofk _ _) -> ofk == fk) $ Set.toList opSet )
    name


findNodeNameForSentenceName::ImportsMap->SensMap->String->String->(Maybe String)
findNodeNameForSentenceName importsMap sensMap sName name =
  findNodeNameFor importsMap sensMap (\n -> not $ Set.null $ Set.filter (\n' -> (senName n' ) == sName) n) name
  
findNodeNameForSentence::ImportsMap->SensMap->CASLFORMULA->String->(Maybe String)
findNodeNameForSentence importsMap sensMap s name =
  findNodeNameFor importsMap sensMap (\n -> not $ Set.null $ Set.filter (\n' -> (sentence n' ) == s) n) name
  
buildCASLSentenceDiff::(Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))->(Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))->(Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof))
buildCASLSentenceDiff = OMap.difference

buildCASLSignDiff::CASLSign->CASLSign->CASLSign
buildCASLSignDiff = diffSig const

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
  let
    sens1 = (\(G_theory _ _ sens) -> (cast sens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)))) th1
    sens2 = (\(G_theory _ _ sens) -> (cast sens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)))) th2
    sign1 = (\(G_theory _ sign _) -> (cast sign)::(Maybe CASLSign)) th1
    sign2 = (\(G_theory _ sign _) -> (cast sign)::(Maybe CASLSign)) th2
  in
    case (sens1, sens2, sign1, sign2) of
      (Just se1, Just se2, Just si1, Just si2) ->
        let
          sediff = buildCASLSentenceDiff se1 se2
          sidiff = buildCASLSignDiff si1 si2
          theo = G_theory CASL sidiff sediff
        in
          node1 { dgn_theory = theo }
      _ ->
        error "This function can only handle CASL-related DGNodeLabS..."   
buildCASLNodeDiff n _ = n -- error "Either one or both Nodes are DGRefs. I cannot handle DGRefs..."

stripCASLMorphism::DGNodeLab->(CASL.Morphism.Morphism () () ())->DGNodeLab
stripCASLMorphism
  n@(DGNode { dgn_theory = th } )
  (CASL.Morphism.Morphism { CASL.Morphism.fun_map = fm, CASL.Morphism.pred_map = pm }) =
    let
      mcsi = (\(G_theory _ sign _) -> (cast sign)::(Maybe CASLSign)) th
      mcse = (\(G_theory _ _ sens) -> (cast sens)::(Maybe (Prover.ThSens CASLFORMULA (AnyComorphism, BasicProof)))) th
    in case mcsi of
      (Just (Sign ss sr om ao oldpm vm se ev ga ei)) ->
        let
          funlist = (map (\(_, (f, _)) -> f) $ Map.toList fm)::[Id.Id]
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
        in  case mcse of
            (Just csens) -> n { dgn_theory = (G_theory CASL (Sign ss sr newopmap newassocmap newpredmap vm se ev ga ei) csens) }
            _ -> error "Could not cast sentences to (ThSens CASLFORMULA) (but a CASLSign was cast... (wierd!))"
      Nothing -> n  -- maybe this node is not CASL-related... leave it as is
stripCASLMorphism n@(DGRef {}) _ = n -- can DGRefS have a morphism from another node in the graph ?


stripCASLMorphisms::DGraph->(Graph.LNode DGNodeLab)->(Graph.LNode DGNodeLab)
stripCASLMorphisms dg (n, node) =
  case node of
    (DGRef {}) -> (n, node) -- no need to do this for a reference...
    _ ->
      let
        incoming = filter ( \(_,tn,_) -> n == tn ) $ Graph.labEdges dg
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
          let
            mcaslmorph = (\(GMorphism _ _ morph) -> (cast morph)::(Maybe (CASL.Morphism.Morphism () () ()))) gmorph
          in  case mcaslmorph of
            (Just caslmorph) -> stripCASLMorphism newnode caslmorph
            _ -> newnode
            ) node morphisms)
   
-- Morphism-presentation with Strings (from xml)
-- Strings need to be looked up from their representation
-- to create an Id
type MorphismMapS = (
    Map.Map String String
  , Map.Map (String,OpType) (String,OpType)
  , Map.Map (String,PredType) (String,PredType)
  , Set.Set String
  )
  
morphismMapToMMS::MorphismMap->MorphismMapS
morphismMapToMMS (sm, om, pm, hs) =
  (
      Map.fromList
        (
          map
            (\(a,b) -> (show a, show b))
            (Map.toList sm)
        )
    , Map.fromList
        (
          map
            (\((a,at),(b,bt)) -> ((show a, at), (show b, bt)))
            (Map.toList om)
        )
    , Map.fromList
        (
          map
            (\((a,at),(b,bt)) -> ((show a, at), (show b, bt)))
            (Map.toList pm)
        )
    , Set.map
        show
        hs
  )

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


type RequationList = [ ( (String, String), (String, String) ) ]

type HidingAndRequationList = ([String], RequationList)

-- string is 'from'
type RequationListList = [(String, HidingAndRequationList)]

-- string is 'where'
type RequationMap = Map.Map String RequationListList

hidingAndRequationListToMorphismMap::
  HidingAndRequationList
  ->MorphismMap
hidingAndRequationListToMorphismMap
  (hidden, requationlist) =
    (
        Map.fromList (map (\((_,a),(_,b)) -> (stringToId a, stringToId b)) requationlist)
      , Map.empty
      , Map.empty
      , Set.fromList (map stringToId hidden)
    )

isEmptyHidAndReqL::HidingAndRequationList->Bool
isEmptyHidAndReqL (_, l) = null l

isNonHidingHidAndReqL::HidingAndRequationList->Bool
isNonHidingHidAndReqL (h, _) = null h
    
createHidingString::CASLSign->String
createHidingString (Sign sortset _ opmap _ predmap _ _ _ _ _) =
  let
    hidden = map show (Set.toList sortset) ++
       map show (Map.keys opmap) ++
       map show (Map.keys predmap)
  in  implode ", " hidden

getSymbols::CASLSign->[Id.Id]
getSymbols (Sign sortset _ opmap _ predmap _ _ _ _ _) =
  (Set.toList sortset) ++ (Map.keys opmap) ++ (Map.keys predmap)

-- hiding is currently wrong because this function does only check 
-- if any symbols dissappear in the target - this happens also when renaming...
makeMorphismMap_o::(Morphism () () ())->MorphismMap
makeMorphismMap_o (Morphism ssource starget sortmap funmap predmap _) =
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
    (sortmap, newfunmap, newpredmap, Set.fromList $ getSymbols 
                $ diffSig const ssource starget)

makeMorphismMap::(Morphism () () ())->MorphismMap
makeMorphismMap m =
  let
    ssign = msource m
    tsign = mtarget m
    sortmap = sort_map m
    predmap = pred_map m
    opmap = fun_map m
    hiddeninit = getSymbols ssign
    -- all (translated) symbols from the source (
    (sms, hiddens) =
      Set.fold
        (\s (sms', hs) ->
          let
            newsort = Map.findWithDefault s s sortmap
          in
            -- check whether the translated sort appears in the target
            if Set.member newsort (sortSet tsign)
              then
--                Debug.Trace.trace ("Found Sort in Target : " ++ show newsort)
                -- if it does, it is not hidden
                (sms'
                  {
                    -- delete original sort
                    sortSet = Set.delete s (sortSet sms')
                  }, Data.List.delete s hs)
              else
--                Debug.Trace.trace ("Sort is hidden : " ++ show newsort)
                (sms', hs)
        )
        (ssign, hiddeninit)
        (sortSet ssign)
    (smp, hiddenp) =
     Map.foldWithKey
      (\pid ps (smp', hp) ->
        Set.fold
          (\pt (smp'', hp') ->
            case Map.lookup (pid, pt) predmap of
              Nothing ->
                (smp'', hp')
              (Just newpid) ->
                let
                  currentsourcepts = Map.findWithDefault Set.empty pid (predMap smp'')
                  currentpts = Map.findWithDefault Set.empty newpid (predMap tsign)
                  conpt = convertPredType pt
                in
                  if
                    Set.member
                      conpt
                      currentpts
                    then
 --                     Debug.Trace.trace ("Found Predicate in Target : " ++ show newpid) $
                      (smp''
                        {
                          predMap =
                            Map.insert
                              pid
                              (Set.delete pt currentsourcepts)
                              (predMap smp'')
                        }, Data.List.delete pid hp')
                    else
--                      Debug.Trace.trace ("Predicate is hidden : " ++ show newpid) $
                      (smp'', hp')
          )
          (smp', hp)
          ps
      )
      (sms, hiddens)
      (predMap ssign)
    (_, hiddeno) =
     Map.foldWithKey
      (\oid os (smo', ho) ->
        Set.fold
          (\ot (smo'', ho') ->
            let
              (newoid, newfk) =
                case lookupOp (oid, ot) of
                  Nothing ->
                    (oid, opKind ot)
                  (Just x) -> x
              currentsourceots = Map.findWithDefault Set.empty oid (opMap smo'')
              currentots = Map.findWithDefault Set.empty newoid (opMap tsign)
              conot = (convertOpType ot) { opKind = newfk }
            in
              if
                Set.member
                  conot
                  currentots
                then
--                  Debug.Trace.trace ("Found Operator in Target : " ++ show newoid ++ " was ( " ++ show oid ++ ")" ++ show opmap) $
                  (smo''
                    {
                      opMap =
                        Map.insert
                          oid
                          (Set.delete ot currentsourceots)
                          (Map.delete oid (opMap smo''))
                    }, Data.List.delete oid ho')
                else
--                  Debug.Trace.trace ("Operator is hidden : " ++ show newoid) $
                  (smo'', ho')
          )
          (smo', ho)
          os
      )
      (smp, hiddenp)
      (opMap ssign)
{-    sma =
     Map.foldWithKey
      (\oid os sma' ->
        Set.fold
          (\ot sma'' ->
            case lookupOp (oid, ot) of
              Nothing ->
                sma''
              (Just (newoid, newfk)) ->
                let
                  currentsourceots = Map.findWithDefault Set.empty oid (opMap sma'')
                  currentots = Map.findWithDefault Set.empty newoid (assocOps tsign)
                  conot = (convertOpType ot) { opKind = newfk }
                in
                  if
                    Set.member
                      conot
                      currentots
                    then
     --                 Debug.Trace.trace ("Found Operator in Target (A) : " ++ show newoid) $
                      sma''
                        {
                          assocOps =
                            Map.insert
                              oid
                              (Set.delete ot currentsourceots)
                              (assocOps sma'')
                        }
                    else
--                      Debug.Trace.trace ("Operator is hidden (A) : " ++ show newoid) $
                      sma''
          )
          sma'
          os
      )
      smo
      (assocOps ssign) -}
    newopmap =
      Map.fromList $
        map
          (\((sid,sot),(tid,tfk)) ->
          -- Hets sets opKind to Partial on morphism... why ?
          -- resulting signatures have Total operators...
            ( (sid, (sot { opKind = Total }) ), (tid, (convertOpType sot  { opKind = tfk }) ) )
          )
          (Map.toList opmap)
    newpredmap =
      Map.fromList $
        map
          ( \( (sid, spt), tid ) -> ( (sid, spt), (tid, convertPredType spt) ) ) 
          (Map.toList predmap)
  in
--    Debug.Trace.trace ("Making MM by " ++ (show opmap) ++ " from " ++ (show ssign) ++ " -> " ++ (show tsign) ++ "...")
--    $
--    Debug.Trace.trace ("Hiding : " ++ (show $ getSymbols sma) ++ " or " ++ show hiddeno)
      (sortmap, newopmap, newpredmap, Set.fromList hiddeno)
  where
    convertArgs::[SORT]->[SORT]
    convertArgs = map (\x -> Map.findWithDefault x x (sort_map m))
    convertPredType::PredType->PredType
    convertPredType p = p { predArgs = convertArgs (predArgs p) }
    convertOpType::OpType->OpType
    convertOpType o =
      o
        {
            opArgs = convertArgs (opArgs o)
          , opRes = Map.findWithDefault (opRes o) (opRes o) (sort_map m)
        }
    lookupOp::(Id.Id, OpType)->Maybe (Id.Id, FunKind)
    lookupOp (oid, ot) =
      case Map.lookup (oid, ot) (fun_map m) of
        (Just x) -> (Just x)
        Nothing ->
          case
            Map.lookup
              (oid, ot { opKind = (if (opKind ot) == Total then Partial else Total) })
              (fun_map m)
            of
              (Just x) -> (Just x)
              Nothing -> Nothing
          
    
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
 
-- create a Morphism from a MorphismMap (stores hidden symbols in source-sign -> sortSet 
morphismMapToMorphism::MorphismMap->(Morphism () () ())
morphismMapToMorphism (sortmap, funmap, predmap, hs) =
  let
    mfunmap = Map.fromList $ map (\((sid, sot),t) -> ((sid, sot { opKind = Partial }),t)) $ Map.toList $ Map.map (\(tid,(OpType fk _ _)) ->
      (tid, fk) ) funmap
    mpredmap = Map.map (\(tid,_) -> tid ) predmap
    -- this is just a workaround to store the hiding-set
    sourceSignForHiding = emptyCASLSign { sortSet = hs }
  in
    Morphism
      {
          msource = sourceSignForHiding
        , mtarget = (emptySign ())
        , sort_map = sortmap
        , fun_map = mfunmap
        , pred_map = mpredmap
        , extended_map = ()
      }
    
applyMorphHiding::MorphismMap->[Id.Id]->MorphismMap
applyMorphHiding mm [] = mm
applyMorphHiding (sortmap, funmap, predmap, hidingset) hidings =
  (
     Map.filterWithKey (\sid _ -> not $ elem sid hidings) sortmap
    ,Map.filterWithKey (\(sid,_) _ -> not $ elem sid hidings) funmap
    ,Map.filterWithKey (\(sid,_) _ -> not $ elem sid hidings) predmap
    ,hidingset
  )
  
buildMorphismSignO::MorphismMap->[Id.Id]->CASLSign->CASLSign
buildMorphismSignO
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

buildMorphismSign::Morphism () () ()->Set.Set SORT->CASLSign->CASLSign
buildMorphismSign morphism hidingSet sign =
  let
    sortshide = Set.filter (\x -> not $ Set.member x hidingSet) (sortSet sign)
    relhide =
      Rel.fromList $
        filter
          (\(a,b) ->
            (not $ Set.member a hidingSet) && (not $ Set.member b hidingSet)
          )
          (Rel.toList (sortRel sign))
    predshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSet) (predMap sign)
    opshide =
      Map.filterWithKey
        (\k _ ->
            not $ Set.member k hidingSet
        )
      (opMap sign)
    assocshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSet) (assocOps sign)
    msorts =  
      Set.map
        (mapSort (sort_map morphism)) 
        sortshide
    mrel =
     Rel.fromList $
      map
        (\(a, b) ->
          (mapSort (sort_map morphism) a, mapSort (sort_map morphism) b)
        ) 

        (Rel.toList relhide)
    mpreds =
      Map.foldWithKey
        (\pid ps mpm ->
          let
            mapped =
              map
                (mapPredSym (sort_map morphism) (pred_map morphism))
                (zip (repeat pid) (Set.toList ps))
          in
            foldl
              (\mpm' (pid',  pt') ->
                Map.insertWith Set.union pid' (Set.singleton pt') mpm'
              )
              mpm
              mapped
        )
        (Map.empty)
        predshide
    mops =
      Map.foldWithKey
        (\oid os mom ->
          let
            mapped =
              map
                (mapOpSym (sort_map morphism) (fun_map morphism))
                (zip (repeat oid) (Set.toList os))
          in
            foldl
              (\mom' (oid',  ot') ->
                Map.insertWith Set.union oid' (Set.singleton ot') mom'
              )
              mom
              mapped
        )
        (Map.empty)
        opshide
    mass =
      Map.foldWithKey
        (\oid os mam ->
          let
            mapped =
              map
                (mapOpSym (sort_map morphism) (fun_map morphism))
                (zip (repeat oid) (Set.toList os))
          in
            foldl
              (\mam' (oid',  ot') ->
                Map.insertWith Set.union oid' (Set.singleton ot') mam'
              )
              mam
              mapped
        )
        (Map.empty)
        assocshide
    msign =
      sign
        {
            sortSet = msorts
          , sortRel = mrel
          , predMap = mpreds
          , opMap = mops
          , assocOps = mass
        }
  in
      msign

  
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

-- | Instance of Read for IdS           
instance Read Id.Id where
  readsPrec _ ('[':s) =
    let
      (tokens, rest) = spanEsc (not . (flip elem "[]")) s
      tokenl = breakIfNonEsc "," tokens
      token = map (\str -> Id.Token (trimString str) Id.nullRange) tokenl
      idl = breakIfNonEsc "," rest
      ids = foldl (\ids' str ->
        case ((readsPrec 0 (trimString str))::[(Id.Id, String)]) of
          [] -> error ("Unable to parse \"" ++ str ++ "\"")
          ((newid,_):_) -> ids' ++ [newid]
          ) [] idl
    in
      case (trimString rest) of
        (']':_) -> [(Id.Id token [] Id.nullRange, "")]
        _ -> [(Id.Id token ids Id.nullRange, "")]
      
  readsPrec _ _ = []

escapeForId::String->String
escapeForId [] = []
escapeForId ('[':r) = "\\[" ++ escapeForId r
escapeForId (']':r) = "\\]" ++ escapeForId r
escapeForId (',':r) = "\\," ++ escapeForId r
escapeForId (' ':r) = "\\ " ++ escapeForId r
escapeForId (c:r) = c:escapeForId r

-- | creates a parseable representation of an Id (see Read-instance)
idToString::Id.Id->String
idToString (Id.Id toks ids _) =
                "[" ++
                (implode "," (map (\t -> escapeForId $ Id.tokStr t) toks)) ++
                (implode "," (map idToString ids)) ++
                "]"
                
-- this encapsulates a node_name in an id
nodeNameToId::NODE_NAME->Id.Id
nodeNameToId (s,e,n) = Id.mkId [s,(stringToSimpleId e),(stringToSimpleId (show n))]

-- this reads back an encapsulated node_name
idToNodeName::Id.Id->NODE_NAME
idToNodeName (Id.Id toks _ _) = (toks!!0, show (toks!!1), read (show (toks!!2)))

getSortSet::DGraph->Node->Set.Set SORT
getSortSet dg n =
  getFromCASLSignM dg n sortSet

-- map every node to a map of every input node to a set of symbols *hidden*
-- when importing from the input node
type HidingMap = Map.Map Graph.Node (Map.Map Graph.Node (Set.Set SORT))

-- add node 1 to node 2
addSignsAndHideSet::DGraph->Set.Set SORT->Node->Node->DGNodeLab
addSignsAndHideSet dg hidingSetForSource n1 n2 =
  let
    n1dgnl = case Graph.lab dg n1 of
      Nothing -> error ("No such Node! " ++ (show n1))
      (Just x) -> x
    n2dgnl = case Graph.lab dg n2 of
      Nothing -> error ("No such Node! " ++ (show n2))
      (Just x) -> x
    sign1 =  getJustCASLSign $ getCASLSign (dgn_sign n1dgnl)
    sign2 =  getJustCASLSign $ getCASLSign (dgn_sign n2dgnl)
    asign = CASL.Sign.addSig (\_ _ -> ()) sign1 sign2
    sortshide = Set.filter (\x -> not $ Set.member x hidingSetForSource) (sortSet asign)
    relhide =
      Rel.fromList $
        filter
          (\(a,b) ->
            (not $ Set.member a hidingSetForSource) && (not $ Set.member b hidingSetForSource)
          )
          (Rel.toList (sortRel asign))
    predshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSetForSource) (predMap asign)
    opshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSetForSource) (opMap asign)
    assocshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSetForSource) (assocOps asign)
    signhide =
      asign
        {
            sortSet = sortshide
          , sortRel = relhide
          , predMap = predshide
          , opMap = opshide
          , assocOps = assocshide
        }
    newnodel =
      n2dgnl
        {
          dgn_theory = G_theory CASL signhide (Prover.toThSens [])
        }
  in
{-    Debug.Trace.trace
      ("--==!! Created new node from " ++ (show sign1) ++ " --==!! and !!==-- " ++ (show sign2) ++ " --==!! -> !!==-- " ++ (show asign) ++ " !!==-- ") -}
      newnodel

addSignsAndHideWithMorphism::DGraph->Set.Set SORT->Morphism () () ()->Node->Node->DGNodeLab
addSignsAndHideWithMorphism dg hiding mm n1 n2 =
  let
    n1dgnl = case Graph.lab dg n1 of
      Nothing -> error ("No such Node! " ++ (show n1))
      (Just x) -> x
    n2dgnl = case Graph.lab dg n2 of
      Nothing -> error ("No such Node! " ++ (show n2))
      (Just x) -> x
    sign1 =  getJustCASLSign $ getCASLSign (dgn_sign n1dgnl)

    sign2 =  getJustCASLSign $ getCASLSign (dgn_sign n2dgnl)

    msign = buildMorphismSign mm hiding sign1

    asign = CASL.Sign.addSig (\_ _ -> ()) msign sign2

    sens = getProverSentences (dgn_theory n2dgnl)

    newnodel =
      n2dgnl
        {
          dgn_theory = G_theory CASL asign sens
        }
  in
{-    Debug.Trace.trace
      ("--==!! Created new node from " ++ (show (dgn_name n1dgnl)) ++ " " ++ (show sign1) ++ " --==!! ##and## !!==-- " ++ (show (dgn_name n2dgnl)) ++ " " ++ (show sign2) ++ " --==!! ##--## !!==-- " ++ (show hiding) ++ " --==!! ##++## !!==-- " ++ (show msign) ++ "--==!! ##by## !!==-- " ++ show mm ++ " --==!! ##->## !!==-- " ++ (show asign) ++ " !!==-- ") -}
      newnodel

addSignsAndHideWithMorphismExt::Set.Set SORT->Morphism () () ()->DGNodeLab->DGNodeLab->DGNodeLab
addSignsAndHideWithMorphismExt hiding mm n1dgnl n2dgnl =
  let
    sign1 =  getJustCASLSign $ getCASLSign (dgn_sign n1dgnl)

    sign2 =  getJustCASLSign $ getCASLSign (dgn_sign n2dgnl)

    msign = buildMorphismSign mm hiding sign1

    asign = CASL.Sign.addSig (\_ _ -> ()) msign sign2

    sens = getProverSentences (dgn_theory n2dgnl)

    newnodel =
      n2dgnl
        {
          dgn_theory = G_theory CASL asign sens
        }
  in
{-    Debug.Trace.trace
      ("--==!! Created new node from " ++ (show (dgn_name n1dgnl)) ++ " " ++ (show sign1) ++ " --==!! ##and## !!==-- " ++ (show (dgn_name n2dgnl)) ++ " " ++ (show sign2) ++ " --==!! ##--## !!==-- " ++ (show hiding) ++ " --==!! ##++## !!==-- " ++ (show msign) ++ "--==!! ##by## !!==-- " ++ show mm ++ " --==!! ##->## !!==-- " ++ (show asign) ++ " !!==-- ") -}
      newnodel



-- add node 1 to node 2
addSignsAndHide::DGraph->HidingMap->Node->Node->DGraph
addSignsAndHide dg hidingMap n1 n2 =
  let
    n1dgnl = case Graph.lab dg n1 of
      Nothing -> error ("No such Node! " ++ (show n1))
      (Just x) -> x
    n2dgnl = case Graph.lab dg n2 of
      Nothing -> error ("No such Node! " ++ (show n2))
      (Just x) -> x
    -- n2 is the target
    hidingMapForNode = Map.findWithDefault Map.empty n2 hidingMap
    -- n1 is the source
    hidingSetForSource = Map.findWithDefault Set.empty n1 hidingMapForNode
    sign1 =  getJustCASLSign $ getCASLSign (dgn_sign n1dgnl)
    sign2 =  getJustCASLSign $ getCASLSign (dgn_sign n2dgnl)
    asign = CASL.Sign.addSig (\_ _ -> ()) sign1 sign2
    sortshide = Set.filter (\x -> not $ Set.member x hidingSetForSource) (sortSet asign)
    relhide =
      Rel.fromList $
        filter
          (\(a,b) ->
            (not $ Set.member a hidingSetForSource) && (not $ Set.member b hidingSetForSource)
          )
          (Rel.toList (sortRel asign))
    predshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSetForSource) (predMap asign)
    opshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSetForSource) (opMap asign)
    assocshide = Map.filterWithKey (\k _ -> not $ Set.member k hidingSetForSource) (assocOps asign)
    signhide =
      asign
        {
            sortSet = sortshide
          , sortRel = relhide
          , predMap = predshide
          , opMap = opshide
          , assocOps = assocshide
        }
    newnodel =
      n2dgnl
        {
          dgn_theory = G_theory CASL signhide (Prover.toThSens [])
        }
  in
    Debug.Trace.trace ("HidingSet for " ++ show n1 ++ " -> "  ++ show n2 ++ " : " ++ show hidingSetForSource) $ Graph.insNode (n2, newnodel) (Graph.delNode n2 dg)


addSigns::DGraph->Node->Node->DGraph
addSigns dg n1 n2 =
  let
    n1dgnl = case Graph.lab dg n1 of
      Nothing -> error ("No such Node! " ++ (show n1))
      (Just x) -> x
    n2dgnl = case Graph.lab dg n2 of
      Nothing -> error ("No such Node! " ++ (show n2))
      (Just x) -> x
    sign1 =  getJustCASLSign $ getCASLSign (dgn_sign n1dgnl)
    sign2 =  getJustCASLSign $ getCASLSign (dgn_sign n2dgnl)
    asign = CASL.Sign.addSig (\_ _ -> ()) sign1 sign2
    newnodel = n2dgnl {
      dgn_theory =
        (\(G_theory _ _ {-thsens-} _) -> G_theory CASL asign (Prover.toThSens [])) (dgn_theory n2dgnl)
      }
      
  in
    Graph.insNode (n2, newnodel) (Graph.delNode n2 dg)

data SortTrace =
    SortNotFound
  | ST
    {
        st_sort :: SORT
      , st_lib_name :: LIB_NAME
      , st_node :: Graph.Node
      , st_branches :: [SortTrace]
    }

displaySortTrace::String->SortTrace->String
displaySortTrace p SortNotFound = p ++ "_|_"
displaySortTrace
  p
  (ST { st_sort = s, st_lib_name = ln, st_node = n, st_branches = b }) =
  p ++ (show s) ++ " in " ++ (show ln) ++ ":" ++ (show n) 
    ++ 
    (if null b
      then
        ""
      else
        (concat
          (map
            (\branch -> "\n" ++ (displaySortTrace (p++"  ") branch) ) 
            b
          )
        )
    )

--instance Show SortTrace where
--  show = displaySortTrace ""

buildSortTraceFor::
  LibEnv
  ->LIB_NAME
  ->[(LIB_NAME, Graph.Node)]
  ->SORT
  ->Graph.Node
  ->SortTrace
buildSortTraceFor
  lenv
  ln
  visited
  s
  n =
  let
    dg =
      devGraph
        $ Map.findWithDefault
          (error ((show ln) ++ ": no such Library in Environment!"))
          ln
          lenv
    node =
      fromMaybe
        (error ( (show n) ++ "No such node in DevGraph!") )
        (Graph.lab dg n)
    caslsign = getJustCASLSign $ getCASLSign (dgn_sign node)
    sorts = sortSet caslsign
    newvisited = (ln, n):visited
    incoming =
      filter
        (\(from,_) ->
          (not (elem from (map snd (filter (\(ln',_) -> ln' == ln ) newvisited))))
        )
        $ map (\(from,_,ll) -> (from, ll)) $ Graph.inn dg n
    incoming_sorttrans =
      map
        (\(from, ll) ->
          let
            caslmorph = getCASLMorphLL ll
            newsort = sortBeforeMorphism caslmorph s
          in
            (from, newsort)
        )
        incoming
    reflib = dgn_libname node
    refnode = dgn_node node
    nexttraces =
      if
        isDGRef node
          then
            [(buildSortTraceFor lenv reflib newvisited s refnode)]
          else
            map
              (\(nodenum, newsort) ->
                buildSortTraceFor lenv ln newvisited newsort nodenum
              )
              incoming_sorttrans
  in
    if Set.member s sorts
      then
        ST
          {
              st_sort = s
            , st_lib_name = ln
            , st_node = n
            , st_branches = nexttraces
          }
      else
        SortNotFound

sortBeforeMorphism::Morphism a b c->SORT->SORT
sortBeforeMorphism m s =
  let
    maplist = Map.toList (sort_map m)
    previous_sort =
      case
        Data.List.find (\(_,b) -> b == s) maplist
      of
        Nothing -> s
        (Just (a,_)) -> a
  in
    previous_sort

sortAfterMorphism::Morphism a b c->SORT->SORT
sortAfterMorphism m s =
  Map.findWithDefault s s (sort_map m)


buildAllSortTracesFor::
  LibEnv
  ->LIB_NAME
  ->Graph.Node
  ->[SortTrace]
buildAllSortTracesFor
  lenv
  ln
  n =
  let
    dg =
      devGraph
        $ Map.findWithDefault
          (error ((show ln) ++ ": no such Library in Environment!"))
          ln
          lenv
    node =
      fromMaybe
        (error ( (show n) ++ "No such node in DevGraph!") )
        (Graph.lab dg n)
    caslsign = getJustCASLSign $ getCASLSign (dgn_sign node)
    sorts = Set.toList $ sortSet caslsign
  in
    map
      (\s -> 
        buildSortTraceFor
          lenv
          ln
          []
          s
          n
      )
      sorts

{-
instance Show [SortTrace] where
  show = concat . map (\st -> (show st) ++ "\n")
-}
 
showLinks::DGraph->IO ()
showLinks dg =
  let
    nodes' = Graph.labNodes dg
    edges' = Graph.labEdges dg
  in
    showRec nodes' edges'
  where
    showRec::[Graph.LNode DGNodeLab] -> [Graph.LEdge DGLinkLab] -> IO ()
    showRec _ [] = return ()
    showRec nodes' ((from, to, _):rest) =
      let
        fromname = getDGNodeName $ fromMaybe (error "!") $ lookup from nodes'
        toname = getDGNodeName $ fromMaybe (error "!") $ lookup to nodes'
      in
        putStrLn (fromname ++ " -> " ++ toname) >> showRec nodes' rest

getMorphismImages::DGraph->[(String, String, String)]
getMorphismImages dg =
  let
    nodes' = Graph.labNodes dg
    edges' = Graph.labEdges dg
  in
    showRec nodes' edges'
  where
    showRec::[Graph.LNode DGNodeLab] -> [Graph.LEdge DGLinkLab] ->[(String, String, String)]
    showRec _ [] = []
    showRec nodes' ((from, to, ll):rest) =
      let
        fromname = getDGNodeName $ fromMaybe (error "!") $ lookup from nodes'
        toname = getDGNodeName $ fromMaybe (error "!") $ lookup to nodes'
        caslmorph = getCASLMorphLL ll
        sourcesyms = symOf (msource caslmorph)
        targetsyms = symOf (mtarget caslmorph)
      in
        (fromname, toname,  "(" ++ (show sourcesyms) ++ ") -> (" ++ (show targetsyms) ++ ")"):(showRec nodes' rest)


getMorphismSets::DGraph->[ (String, String, SymbolSet, SymbolSet) ]
getMorphismSets dg =
  let
    nodes' = Graph.labNodes dg
    edges' =
      filter
        (\(_,_,ll) ->
          case dgl_type ll of
            (LocalDef {}) -> True
            (GlobalDef {}) -> True
            (HidingDef {}) -> True
            _ -> False
        )
        (Graph.labEdges dg)
  in
    makeSets nodes' edges'
  where
    makeSets::[Graph.LNode DGNodeLab] -> [Graph.LEdge DGLinkLab] ->[(String, String, SymbolSet, SymbolSet)]
    makeSets _ [] = []
    makeSets nodes' ((from, to, ll):rest) =
      let
        fromname = getDGNodeName $ fromMaybe (error "!") $ lookup from nodes'
        toname = getDGNodeName $ fromMaybe (error "!") $ lookup to nodes'
        caslmorph = getCASLMorphLL ll
        sourcesyms = symOf (msource caslmorph)
        targetsyms = symOf (mtarget caslmorph)
        isHiding = case (dgl_type ll) of (HidingDef {}) -> True; _ -> False
        diffset =
          if not isHiding
            then
              Set.difference sourcesyms targetsyms
            else
              Set.difference targetsyms sourcesyms
        extset =
          if isHiding
            then
              Set.difference sourcesyms targetsyms
            else
              Set.difference targetsyms sourcesyms
      in
        (fromname ++ (if isHiding then "!" else ""), toname,  diffset, extset):(makeSets nodes' rest)



-- computes order of processing for a whole library environment
-- handles library references by making sure that the target node
-- has been processed before so processing the reference is safe


-- libname, node-name, node-num, trace-order
-- | TracemarkS are the steps to take when following links
data TraceMark = TraceMark (LIB_NAME, String, Graph.Node, Int)
  deriving Eq

instance Ord TraceMark where
  TraceMark (_, _, _, i1) < TraceMark (_, _, _, i2) = i1 < i2

{- |
  Creates a list of TraceMarkS from a library environment that show
  the order of inter node dependencies for following links
-}
createTraceMarks::LibEnv->[TraceMark]
createTraceMarks le =
  let
    libNamesAndDGs = Map.fromList $ map (\(a, b) -> (a, devGraph b)) $ Map.toList le
    initialFinalMap =
      Map.map
        (\dg ->
          let
            graphnodes = Graph.labNodes dg
            noimports =
              filter
                (\(nodeNum, node) ->
                 -- references cannot be starts
                 (not $ isDGRef node) &&
                  (null $
                    filter
                      -- only definitional links disqualify a node as start
                      (\(_,_,ll) -> defLink ll)
                      (Graph.inn dg nodeNum)
                  )
                )
                graphnodes
          in
            noimports
        )
        libNamesAndDGs
    (initialMarked, _) =
      foldl
        (\(currentList, n) (libname, ninodes) ->
          let
            (cm, nn) =
              foldl
                (\(cm', nn') (nodenum, node) ->
                  ( cm'++[TraceMark (libname, (getDGNodeName node), nodenum, nn')], nn' + 1)
                )
                ([], n)
                ninodes
          in
            (currentList ++ cm, nn)
        )
        ([], (0::Int))
        (Map.toList initialFinalMap)
    flat =
      foldl
        (\f (libname, dg) ->
          f ++ map (\(nodeNum, node) -> (libname, nodeNum, node)) (Graph.labNodes dg)
        )
        []
        (Map.toList libNamesAndDGs)
    flatNoInit =
      filter
        (\(libname, nodeNum, _) ->
          case
            Data.List.find
              (\(TraceMark (libname', _, nodeNum', _)) ->
                libname == libname' && nodeNum == nodeNum'
              )
              initialMarked
          of
            Nothing -> True
            _ -> False
        )
        flat
    (amarked, _) =
      until
        (\(_, unmarked) -> null unmarked)
        (\(marked, (current@(libname, nodeNum, node)):unmarked) ->
          let
            (realNode, realLibName) =
              if isDGRef node
                then
                  (dgn_node node, dgn_libname node)
                else
                  (nodeNum, libname)
            importDG = (Map.findWithDefault (error "impossible!") realLibName libNamesAndDGs)
            inNodeNums =
              map
                (\(from, _, _) -> from)
                $ filter
                    (\(_, _, ll) -> defLink ll)
                    (Graph.inn
                      importDG
                      realNode
                    )
            inMarked =
              map
                (\nn ->
                  case
                    Data.List.find
                      (\(TraceMark (libname', _, nodeNum', _)) ->
                        libname' == realLibName && nodeNum' == nn
                      )
                      marked
                  of
                    Nothing -> False
                    _ -> True
                )
                inNodeNums
          in
            if and inMarked
              then
                -- check against real, but save in context of current DG
                (marked ++ [TraceMark (libname, getDGNodeName node, nodeNum, length marked)], unmarked)
              else
                (marked, unmarked++[current])
        )
        (initialMarked, flatNoInit)
  in
    amarked

-- | check if a DGLinkLab is one of the definitional types
defLink::DGLinkLab->Bool
defLink dgl =
  case dgl_type dgl of
    (LocalDef {}) -> True
    (GlobalDef {}) -> True
    (HidingDef {}) -> True
    (FreeDef {}) -> True
    (CofreeDef {}) -> True
    _ -> False

type TakenBy =
  Map.Map
    (LIB_NAME, Graph.Node)
    (
        Set.Set SORT
      , Map.Map Id.Id (Set.Set PredType)
      , Map.Map Id.Id (Set.Set OpType)
    )

type TakenMap = Map.Map (LIB_NAME, Graph.Node) TakenBy

{- |
  Create a minimal library environment where developement graph nodes only
  contain sorts, ops and preds where they are defined (or imported via DGRefS)
-}
createMinimalLibEnv::
  LibEnv -- ^ library environment to reduce
  ->[TraceMark] -- ^ tracemarks created by 'createTraceMarks'
  ->(LibEnv, TakenMap)
createMinimalLibEnv ln tracemarks =
  foldl
    (\(ln', tm') (TraceMark (libname, _, nodenum, _)) ->
      let
        currentTBMap = Map.findWithDefault (Map.empty::TakenBy) (libname, nodenum) tm'
        currentLookup = Map.findWithDefault (error "This can't happen!") libname ln'
        currentDG = devGraph currentLookup
        currentNode = (\(Just a) -> a) $ Graph.lab currentDG nodenum
        currentCASLSign = getJustCASLSign $ getCASLSign (dgn_sign currentNode)
        inDefLinks =
          filter
            (\(_, _, ll) -> defLink ll)
            (Graph.inn currentDG nodenum)
        (strippedCASLSign, newTBM) =
          foldl
            (\(s, tbm'') (from, _, ll) ->
              let
                caslmorph = getCASLMorphLL ll
                sourcesign =
                  case dgl_type ll of
                    (HidingDef {}) -> mtarget caslmorph
                    (FreeDef {}) ->
                      let
                        nodesign =
                          (\(Just a) -> a)
                            $
                            getCASLSign
                              (dgn_sign
                                $
                                (\(Just a) -> a)
                                  $
                                  Graph.lab
                                    currentDG
                                    from
                              )
                      in
                        nodesign
                    _ -> msource caslmorph
                strippedSorts =
                  Set.difference (sortSet s) (sortSet sourcesign)
                takenSorts = Set.difference (sortSet s) strippedSorts
                strippedRels =
                  Rel.fromList
                    $
                    filter
                      (\(a,b) ->
                        any (\x -> (Set.member x strippedSorts)) [a,b]
                      )
                      (Rel.toList (sortRel s))
                strippedPreds = signstrip s sourcesign predMap
                takenPreds = Map.differenceWith (\a b -> Just $ Set.difference a b) (predMap s) strippedPreds
                strippedOps = signstrip s sourcesign opMap
                takenOps = Map.differenceWith (\a b -> Just $ Set.difference a b) (opMap s) strippedOps
                strippedAssocOps = signstrip s sourcesign assocOps
                (prevTakenSortSet, prevTakenPredMap, prevTakenOpMap) =
                  Map.findWithDefault (Set.empty, Map.empty, Map.empty) (libname, from) tbm''
              in
                (
                    s
                      {
                          sortSet = strippedSorts
                        , sortRel = strippedRels
                        , predMap = strippedPreds
                        , opMap = strippedOps
                        , assocOps = strippedAssocOps
                      }
                  , Map.insert
                      (libname, from)
                      (
                          Set.union prevTakenSortSet takenSorts
                        , Map.unionWith (Set.union) prevTakenPredMap takenPreds
                        , Map.unionWith (Set.union) prevTakenOpMap takenOps
                      )
                      tbm''
                )
            )
            (currentCASLSign, currentTBMap)
            inDefLinks
        currentSentences = getProverSentences (dgn_theory currentNode)
        newNode =
          currentNode
            {
              dgn_theory = G_theory CASL strippedCASLSign currentSentences
            }
        oldEdges = Graph.labEdges currentDG
        oldNodes = filter (\(n,_) -> n /= nodenum) $ Graph.labNodes currentDG
        newGraph = mkGraph ((nodenum, newNode):oldNodes) oldEdges
        newLookup =
          currentLookup
            {
              devGraph = newGraph
            }
      in
        (Map.insert libname newLookup ln', Map.insertWith (Map.union) (libname, nodenum) newTBM tm')
    )
    (ln, Map.empty)
    (reverse tracemarks)
  where
    signstrip::
      (Ord a, Ord b)
      =>CASLSign
      ->CASLSign
      ->(CASLSign->Map.Map a (Set.Set b))
      ->Map.Map a (Set.Set b)
    signstrip tosign fromsign =
      (\selector ->
        Map.filter (not . Set.null)
        $
        Map.mapWithKey
        (\sid sset ->
          let
            sourceset = Map.findWithDefault Set.empty sid (selector fromsign)
          in
            (Set.difference sset sourceset)
        )
        (selector tosign)
      )

type IdNameMapping = (LIB_NAME, NODE_NAME, String, Graph.Node, Set.Set (Id.Id, String), Set.Set ((Id.Id, PredType), String), Set.Set ((Id.Id, OpType), String), Set.Set ((Id.Id, Int), String), Set.Set ((Int, Id.Id, OpType), String))


{-
instance Show IdNameMapping where
  show (ln, nn, nsn, nnum, sorts, preds, ops, sens, cons) =
    "(" ++ show ln ++ ", " ++ show nn ++ ", " ++ show nsn ++ ", "
      ++ show nnum ++ ", " ++ show sorts ++ ", " ++ show preds ++ ", "
      ++ show ops ++ ", " ++ show sens ++ ", " ++ show cons ++ ")"
-}

inmGetLibName::IdNameMapping->LIB_NAME
inmGetLibName (ln, _, _, _, _, _, _, _, _) = ln

inmGetNodeName::IdNameMapping->NODE_NAME
inmGetNodeName (_, nn, _, _, _, _, _, _, _) = nn

inmGetNodeId::IdNameMapping->String
inmGetNodeId (_, _, id', _, _, _, _, _, _) = id'

inmGetNodeNum::IdNameMapping->Graph.Node
inmGetNodeNum (_, _, _, nn, _, _, _, _, _) = nn

inmGetIdNameSortSet::IdNameMapping->Set.Set (Id.Id, String)
inmGetIdNameSortSet (_, _, _, _, s, _, _, _, _) = s

inmGetIdNamePredSet::IdNameMapping->Set.Set ((Id.Id, PredType), String)
inmGetIdNamePredSet (_, _, _, _, _, s, _, _, _) = s

inmGetIdNameOpSet::IdNameMapping->Set.Set ((Id.Id, OpType), String)
inmGetIdNameOpSet (_, _, _, _, _, _, s, _, _) = s

inmGetIdNameSensSet::IdNameMapping->Set.Set ((Id.Id, Int), String)
inmGetIdNameSensSet (_, _, _, _, _, _, _, s, _) = s

inmGetIdNameConsSet::IdNameMapping->Set.Set ((Int, Id.Id, OpType), String)
inmGetIdNameConsSet (_, _, _, _, _, _, _, _, c) = c

inmGetIdNameConsSetLikeOps::IdNameMapping->Set.Set ((Id.Id, OpType), String)
inmGetIdNameConsSetLikeOps (_, _, _, _, _, _, _, _, c) =
  Set.map
    (\((_, id', ot), name) -> ((id', ot), name))
    c

inmGetIdNameAllSet::IdNameMapping->Set.Set (Id.Id, String)
inmGetIdNameAllSet inm =
  Set.union
    (
      Set.union
        (
          Set.union
            (inmGetIdNameSortSet inm)
            (
              Set.map
                (\( (id', _), s') -> (id', s'))
                (inmGetIdNameSensSet inm)
            )
        )
        (
          Set.union
            (
            Set.map
              (\( (id',_), s') -> (id', s'))
              (inmGetIdNamePredSet inm)
            )
            (
            Set.map
              (\( (id',_), s') -> (id', s'))
              (inmGetIdNameOpSet inm)
            )
        )
    )
    (
      Set.map
        (\((_, id', _), s') -> (id', s'))
        (inmGetIdNameConsSet inm)
    )

inmGetLNNN::IdNameMapping->(LIB_NAME, Graph.Node)
inmGetLNNN inm = (inmGetLibName inm, inmGetNodeNum inm)

inmFindLNNN::(LIB_NAME, Graph.Node)->[IdNameMapping]->Maybe IdNameMapping
inmFindLNNN lnnn = Data.List.find (\inm -> inmGetLNNN inm == lnnn)

getIdOrigins::[IdNameMapping]->Id.Id->[IdNameMapping]
getIdOrigins [] _ = []
getIdOrigins (o:r) sid =
  (
    if
      Set.null
        $
        Set.filter
          (\(sid', _) -> sid' == sid)
          $
          inmGetIdNameAllSet o
      then
        []
      else
        [o]
  ) ++ getIdOrigins r sid

getNameOrigins::[IdNameMapping]->String->[IdNameMapping]
getNameOrigins [] _ = []
getNameOrigins (o:r) name =
  (
    if
      Set.null
        $
        Set.filter
          (\(_, name') -> name' == name)
          $
          inmGetIdNameAllSet o
      then
        []
      else
        [o]
  ) ++ getNameOrigins r name

getNameOrigin::[IdNameMapping]->LIB_NAME->Graph.Node->String->[IdNameMapping]
getNameOrigin names ln node name =
  case getLNGN names ln node of
    Nothing -> []
    (Just o) ->
      if
        Set.null
          $
          Set.filter
            (\(_, name') -> name' == name)
            $
            inmGetIdNameAllSet o
      then
        []
      else
        [o]

getLNGNL::[IdNameMapping]->LIB_NAME->Graph.Node->[IdNameMapping]
getLNGNL m ln nn =
  case (getLNGN m ln nn) of
    Nothing -> []
    (Just o) -> [o]

getLNGN::[IdNameMapping]->LIB_NAME->Graph.Node->Maybe IdNameMapping
getLNGN [] _ _ = Nothing
getLNGN (h:r) ln nn
  | (inmGetLibName h) == ln && (inmGetNodeNum h) == nn = Just h
  | otherwise = getLNGN r ln nn

getNameFor::[IdNameMapping]->(IdNameMapping->a)->(a->c)->(c->Bool)->(c->String)->Maybe String
getNameFor [] _ _ _ _ = Nothing
getNameFor (h:r) translate process found extract =
  let
    processed = process $ translate h
  in
    if found processed
      then
        Just (extract processed)
      else
        getNameFor r translate process found extract

getNameForSort::[IdNameMapping]->SORT->Maybe String
getNameForSort mapping s =
  getNameFor
    mapping
    inmGetIdNameSortSet
    (Set.filter (\(sid, _) -> sid == s))
    (not . Set.null)
    (snd . head . Set.toList)

getNameForPred::[IdNameMapping]->(Id.Id, PredType)->Maybe String
getNameForPred mapping (pid, pt) =
  getNameFor
    mapping
    inmGetIdNamePredSet
    (Set.filter (\((pid', pt'), _) -> pid' == pid && pt' == pt))
    (not . Set.null)
    (snd . head . Set.toList)

getNameForOp::[IdNameMapping]->(Id.Id, OpType)->Maybe String
getNameForOp mapping (oid, ot) =
  getNameFor
    mapping
    inmGetIdNameOpSet
    (Set.filter (\((oid', ot'), _) -> oid' == oid && ot' == ot))
    (not . Set.null)
    (snd . head . Set.toList)

getNameForSens::[IdNameMapping]->(Id.Id, Int)->Maybe String
getNameForSens mapping (s,sn) =
  getNameFor
    mapping
    inmGetIdNameSensSet
    (Set.filter (\((sid, sn'), _) -> sid == s && sn' == sn))
    (not . Set.null)
    (snd . head . Set.toList)

getNameForCons::[IdNameMapping]->(Int, Id.Id, OpType)->Maybe String
getNameForCons mapping (sennum, cid, ot) =
  getNameFor
    mapping
    inmGetIdNameConsSet
    (Set.filter (\((sennum', cid', ot'), _) -> sennum' == sennum && cid' == cid && ot' == ot))
    (not . Set.null)
    (snd . head . Set.toList)

cv_Op_typeToOpType::OP_TYPE->OpType
cv_Op_typeToOpType (Op_type fk args res _) = OpType fk args res

cv_OpTypeToOp_type::OpType->OP_TYPE
cv_OpTypeToOp_type (OpType fk args res) = Op_type fk args res Id.nullRange

cv_Pred_typeToPredType::PRED_TYPE->PredType
cv_Pred_typeToPredType (Pred_type args _) = PredType args

cv_PredTypeToPred_type::PredType->PRED_TYPE
cv_PredTypeToPred_type (PredType args) = Pred_type args Id.nullRange

extractConstructorOps::Ann.Named CASLFORMULA->Set.Set (Id.Id, OpType)
extractConstructorOps ansen =
  case Ann.sentence ansen of
    (Sort_gen_ax cons _) ->
      foldl
        (\ops (Constraint _ symbs _) ->
          foldl
            (\ops' (Qual_op_name name ot _) ->
              Set.insert (name, cv_Op_typeToOpType ot) ops'
            )
            ops
            (map fst symbs)
        )
        Set.empty
        cons
    _ -> Set.empty

{- |
  Create a list of SetS of tuples of an Id and a unique String for the Id.
  Each Set is annotated with it's node number, node name and library name.
-}
createUniqueNames::
  LibEnv -- ^ the minimal libary environment to create names for
  ->[TraceMark] -- ^ tracemarks used to create the minimal environment
  ->[IdNameMapping] 
createUniqueNames ln tracemarks =
  foldl
    (\names (TraceMark (libname, _, nodenum, _)) ->
      let
        dg = devGraph $ Map.findWithDefault (error "This can't happen!") libname ln
        node = (\(Just a) -> a) $ Graph.lab dg nodenum
        nodename = getNodeName node
        caslsign = (\(Just a) -> a) $ getCASLSign (dgn_sign node)
        previousNodeNameUse =
          foldl
            (\c inm ->
              if (
                  -- check if there is another node with the same name...
                  ( (inmGetNodeName inm) == dgn_name node)
                  ||
                    -- ...or if the nodename matches a used unique name
                    not
                      (Set.null
                        $
                        Set.filter
                          (\(_, uname) ->
                            nodename == uname
                          )
                          (inmGetIdNameSortSet inm)
                      )
                )
                then
                  c + 1
                else
                  c
            )
            (0::Integer)
            names
        uniqueNodeName =
          case
            previousNodeNameUse
          of
            0 -> nodename
            n -> nodename ++ "_" ++ (show (n+1))
        usedIdsForSorts =
          Set.fromList
            $
            map
              (stringToId . nodeNameToName)
              (
                (
                  map
                    inmGetNodeName
                    names
                )
                ++ [dgn_name node]
              )
        uniqueSortIds =
          Set.fold
            (\sid us ->
              let
                sameIdBefore =
                  Set.fold
                    (\id' c ->
                      if id' == sid
                        then
                          c + 1
                        else
                          c
                    )
                    (0::Integer)
                    usedIdsForSorts
                -- this catches overloading... 
                sameIdInNodeCount =
                  Set.fold
                    (\(sid', _) c ->
                      if sid' == sid
                        then
                          c + 1
                        else
                          c
                    )
                    sameIdBefore
                    us
                -- this catches same named but different sorts
                previousSameIdCount =
                  foldl
                    (\c inm ->
                      Set.fold
                        (\(ui, _) c' ->
                          if ui == sid
                            then
                              c' + 1
                            else
                              c'
                        )
                        c
                        (inmGetIdNameAllSet inm)
                    )
                    sameIdInNodeCount
                    names
                thisName =
                  case
                    previousSameIdCount
                  of
                    0 -> show sid
                    n -> (show sid) ++ "_" ++ (show (n+1))
              in
                Set.insert (sid, thisName) us
            )
            Set.empty
            (sortSet caslsign)
        usedIdsForPreds =
          Set.union
            usedIdsForSorts
            (Set.map fst uniqueSortIds)
        uniquePredIds =
          Map.foldWithKey
            (\pid pts us ->
              Set.fold
                (\pt us' ->
                  let
                    sameIdBefore =
                      Set.fold
                        (\id' c ->
                          if id' == pid
                            then
                              c + 1
                            else
                              c
                        )
                        (0::Integer)
                        usedIdsForPreds
                    sameIdInNodeCount =
                      Set.fold
                        (\((pid',_), _) c ->
                          if pid' == pid
                            then
                              c + 1
                            else
                              c
                        )
                        sameIdBefore
                        us'
                    previousSameIdCount =
                      foldl
                        (\c inm ->
                          Set.fold
                            (\(ui, _) c' ->
                              if ui == pid
                                then
                                  c' + 1
                                else
                                  c'
                            )
                            c
                            (inmGetIdNameAllSet inm)
                        )
                        sameIdInNodeCount
                        names
                    thisName =
                      case
                        previousSameIdCount
                      of
                        0 -> show pid
                        n -> (show pid) ++ "_" ++ (show (n+1))

                  in
                    Set.insert ((pid, pt), thisName) us'
                )
                us
                pts
            )
            Set.empty
            (predMap caslsign)
        usedIdsForOps =
          Set.union
            usedIdsForPreds
            (
              Set.map
                (fst . fst)
                uniquePredIds
            )
        uniqueOpIds =
          Map.foldWithKey
            (\oid ots us ->
              Set.fold
                (\ot us' ->
                  let
                    sameIdBefore =
                      Set.fold
                        (\id' c ->
                          if id' == oid
                            then
                              c + 1
                            else
                              c
                        )
                        (0::Integer)
                        usedIdsForOps
                    sameIdInNodeCount =
                      Set.fold
                        (\((oid',_), _) c ->
                          if oid' == oid
                            then
                              c + 1
                            else
                              c
                        )
                        sameIdBefore
                        us'
                    previousSameIdCount =
                      foldl
                        (\c inm ->
                          Set.fold
                            (\(ui, _) c' ->
                              if ui == oid
                                then
                                  c' + 1
                                else
                                  c'
                            )
                            c
                            (inmGetIdNameAllSet inm)
                        )
                        sameIdInNodeCount
                        names
                    thisName =
                      case
                        previousSameIdCount
                      of
                        0 -> show oid
                        n -> (show oid) ++ "_" ++ (show (n+1))

                  in
                    Set.insert ((oid, ot), thisName) us'
                )
                us
                ots
            )
            Set.empty
            (opMap caslsign)
        usedIdsForSens =
          Set.union
            usedIdsForOps
            (
              Set.map
                (fst . fst)
                uniqueOpIds
            )
        uniqueSensIds =
          foldl
            (\us (ns, snum) ->
              let
                sid = stringToId $ senName ns 
                sidid =
                  case
                    senName ns
                  of
                    [] -> "AnonSens"
                    x -> x
                -- this catches overloading... 
                sameIdBefore =
                  Set.fold
                    (\id' c ->
                      if id' == sid
                        then
                          c + 1
                        else
                          c
                    )
                    (0::Integer)
                    usedIdsForSens
                sameIdInNodeCount =
                  Set.fold
                    (\((sid', _), _) c ->
                      if sid' == sid
                        then
                          c + 1
                        else
                          c
                    )
                    sameIdBefore
                    us
                -- this catches same named but different sorts
                previousSameIdCount =
                  foldl
                    (\c inm ->
                      Set.fold
                        (\(ui, _) c' ->
                          if ui == sid
                            then
                              c' + 1
                            else
                              c'
                        )
                        c
                        (inmGetIdNameAllSet inm)
                    )
                    sameIdInNodeCount
                    names
                thisName =
                  case
                    previousSameIdCount
                  of
                    0 -> sidid
                    n -> sidid ++ "_" ++ (show (n+1))
              in
                Set.insert ((sid, snum), thisName) us
            )
            Set.empty
            (zip (getNodeSentences node) ([1..]::[Int]))
        usedIdsForCons =
          Set.union
            usedIdsForSens
            (
              Set.map
                (fst . fst)
                uniqueSensIds
            )
        sencons =
          concatMap
            (\(s, n) ->
              Set.toList
                $
                Set.map
                  (\(cid, ot) -> (n, cid, ot))
                  (extractConstructorOps s)
            )
            (zip (getNodeSentences node) [1..])
        uniqueConsIds =
          foldl
            (\uCI (sennum, cid, ct) ->
              let
                sameIdBefore =
                  Set.fold
                    (\id' c ->
                      if id' == cid
                        then
                          c + 1
                        else
                          c
                    )
                    (0::Integer)
                    usedIdsForCons
                sameIdInNodeCount =
                  Set.fold
                    (\((_, cid' ,_), _) c ->
                      if cid' == cid
                        then
                          c + 1
                        else
                          c
                    )
                    sameIdBefore
                    uCI
                previousSameIdCount =
                  foldl
                    (\c inm ->
                      Set.fold
                        (\(ui, _) c' ->
                          if ui == cid
                            then
                              c' + 1
                            else
                              c'
                        )
                        c
                        (inmGetIdNameAllSet inm)
                    )
                    sameIdInNodeCount
                    names
                nameFromOps =
                  case
                    Data.List.find
                      ( \( (oid, ot), _ ) -> oid == cid && ot == ct )
                      (Set.toList uniqueOpIds)
                  of
                    Nothing -> Nothing
                    (Just (_, uname)) -> Just uname
                thisName =
                  case nameFromOps of
                    Nothing ->
                      case
                        previousSameIdCount
                      of
                        0 -> show cid
                        n -> (show cid) ++ "_" ++ (show (n+1))
                    (Just uname) -> uname
              in
                Set.insert ((sennum, cid, ct), thisName) uCI
            )
            Set.empty
            sencons
      in
        if isDGRef node -- references do not create new names
          then
            names
          else
            names ++
              [(
                  libname
                , dgn_name node
                , uniqueNodeName
                , nodenum
                , uniqueSortIds
                , uniquePredIds
                , uniqueOpIds
                , uniqueSensIds
                , uniqueConsIds
              )]
    )
    []
    tracemarks
  where
    getNodeName::DGNodeLab->String
    getNodeName = nodeNameToName . dgn_name
    nodeNameToName::NODE_NAME->String
    nodeNameToName =
      (\nn ->
        let
          nodename = showName nn
        in
          if (length nodename) == 0
            then
              "AnonNode"
            else
              nodename
      )


nodeNameToName::NODE_NAME->String
nodeNameToName =
  (\nn ->
    let
      nodename = showName nn
    in
      if (length nodename) == 0
        then
          "AnonNode"
        else
          nodename
  )

data Identifier =
    IdNodeName Id.Id
  | IdId Id.Id
  | IdOp Id.Id OpType
  | IdPred Id.Id PredType
  | IdSens Id.Id Int
  | IdCons Id.Id OpType Int
  deriving Show

data IdentifierType = IdTNodeName | IdTId | IdTOp | IdTPred | IdTSens | IdTCons
  deriving (Show, Eq, Ord)

getIdType::Identifier->IdentifierType
getIdType (IdNodeName {}) = IdTNodeName
getIdType (IdId {}) = IdTId
getIdType (IdOp {}) = IdTOp
getIdType (IdPred {}) = IdTPred
getIdType (IdSens {}) = IdTSens
getIdType (IdCons {}) = IdTCons

getIdId::Identifier->Id.Id
getIdId (IdNodeName i) = i
getIdId (IdId i) = i
getIdId (IdOp i _) = i
getIdId (IdPred i _) = i
getIdId (IdSens i _) = i
getIdId (IdCons i _ _) = i

instance Eq Identifier where
  (IdNodeName x) == (IdNodeName y) = x == y
  (IdId x) == (IdId y) = x == y
  (IdOp x xt) == (IdOp y yt) = x == y && xt == yt
  (IdPred x xt) == (IdPred y yt) = x == y && xt == yt
  (IdSens x _) == (IdSens y _) = x == y
  (IdCons x xt _) == (IdCons y yt _) = x == y && xt == yt
  x == y = False

instance Ord Identifier where
  x `compare` y =
    if (getIdType x) == (getIdType y)
      then
        (show x) `compare`(show y)
      else
        (getIdType x) `compare` (getIdType y)

type IdentifierWON = WithOriginNode Identifier

getFlatNames::LibEnv->Map.Map LIB_NAME (Set.Set IdentifierWON)
getFlatNames lenv =
  foldl
    (\fm ln ->
      let
        dg = devGraph $ Map.findWithDefault (error "!") ln lenv
        sortswomap = getSortsWOWithNodeDGNamesWO dg
        opswomap = getOpMapsWOWithNodeDGNamesWO dg
        predswomap = getPredMapsWOWithNodeDGNamesWO dg
        dgnodes = filter (not . isDGRef . snd) $ Graph.labNodes dg
        nodenameids =
          map
            (\(nn, node) -> (nn, stringToId $ nodeNameToName $ dgn_name node))
            dgnodes
        senslist =
          concatMap
            (\(nn, node) -> map (\x -> (nn, x)) $ zip [1..] (getNodeSentences node))
            dgnodes
        senscons =
          concatMap
            (\(nodenum, (sennum, s)) ->
              Set.toList
                $
                Set.map
                  (\(cid, ot) -> (nodenum, (sennum, cid, ot)))
                  (extractConstructorOps s)
            )
            senslist
        sorts' = foldl
          (\fm' sortsetwo ->
            Map.insertWith
              Set.union
              ln
              (Set.map (\swo -> mkWON (IdId (woItem swo)) (woOrigin swo) ) sortsetwo)
              fm'
          )
          fm
          (Map.elems sortswomap)
        ops' =
          foldl
            (\fm' opmapwo ->
              foldl
                (\fm'' (oid, ots) ->
                  foldl
                    (\fm''' ot ->
                      Map.insertWith
                        Set.union
                        ln
                        (Set.singleton (mkWON (IdOp (woItem oid) ot) (woOrigin oid)))
                        fm'''
                    )
                    fm''
                    (Set.toList ots)
                )
                fm'
                (Map.toList opmapwo)
            )
            sorts'
            (Map.elems opswomap)
        preds' =
          foldl
            (\fm' predmapwo ->
              foldl
                (\fm'' (pid, pts) ->
                  foldl
                    (\fm''' pt ->
                      Map.insertWith
                        Set.union
                        ln
                        (Set.singleton (mkWON (IdPred (woItem pid) pt) (woOrigin pid)))
                        fm'''
                    )
                    fm''
                    (Set.toList pts)
                )
                fm'
                (Map.toList predmapwo)
            )
            ops'
            (Map.elems predswomap)
        sens' =
          foldl
            (\fm' (nodenum, (sennum, namedsen)) ->
              Map.insertWith
                Set.union
                ln
                (Set.singleton (mkWON (IdSens (stringToId $ senName namedsen) sennum) nodenum))
                fm'
            )
            preds'
            senslist
        cons' =
          foldl
            (\fm' (nodenum, (sennum, cid, cot)) ->
              Map.insertWith
                Set.union
                ln
                (Set.singleton (mkWON (IdCons cid cot sennum) nodenum))
                fm'
            )
            sens'
            senscons
        nodes' =
          Map.insertWith
            Set.union
            ln
            (
              Set.fromList
                (
                  map
                    (\(nn, nnid)-> mkWON (IdNodeName nnid) nn)
                    nodenameids
                )
            )
            cons'
      in
        nodes'
    )
    Map.empty
    (Map.keys lenv)

identifyFlatNames::
  LibEnv
  ->Map.Map LIB_NAME (Set.Set IdentifierWON)
  ->Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
identifyFlatNames
  lenv
  flatmap =
  let
    reflist =
      foldl
        (\rl ln ->
          let
            dg = devGraph $ Map.findWithDefault (error "!") ln lenv
            refnodes =
              filter
                (\(_, node) -> isDGRef node)
                (Graph.labNodes dg)
          in
            rl ++ (map (\(rnn, rnode) -> (ln, rnn, dgn_libname rnode, dgn_node rnode)) refnodes)
        )
        []
        (Map.keys lenv)
  in
    foldl
      (\im (refln, refnn, refedln, refednode) ->
        let
          reflnids = Map.findWithDefault Set.empty refln flatmap
          refedids = Set.filter (\ws -> woOrigin ws == refnn) reflnids
          refedlnids = Map.findWithDefault Set.empty refedln flatmap
        in
          Set.fold
            (\rws im' ->
              case
                Set.toList
                  $
                  Set.filter (\x -> woItem x == woItem rws) refedlnids
              of
                [] -> Map.insert (refln, rws) (refedln, mkWON (IdId $ stringToId "unknown") refednode) im'
                ws:_ -> Map.insert (refln, rws) (refedln, ws) im'
            )
            im
            refedids
      )
      Map.empty
      reflist

removeReferencedIdentifiers::
  Map.Map LIB_NAME (Set.Set IdentifierWON)
  ->Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
  ->Map.Map LIB_NAME (Set.Set IdentifierWON)
removeReferencedIdentifiers 
  flatMap
  identMap =
  let
    newmap =
      foldl
        (\nm (ln, ids) ->
          Set.fold
            (\idwo nm' ->
              case Map.lookup (ln, idwo) identMap of
                Nothing -> Map.insertWith (Set.union) ln (Set.singleton idwo) nm'
                _ -> nm'
            )
            nm
            ids
        )
        Map.empty
        (Map.toList flatMap)
  in
    newmap

-- OMDoc does only enforce unique names inside a theory
getIdUseNumber::
  Map.Map LIB_NAME (Set.Set IdentifierWON)
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
getIdUseNumber
  remMap
  =
  let
    unnMap =
      Map.map
        (\idwoset ->
          let
            maxorigin =
              Set.fold
                (\iwo mo ->
                  max mo (woOrigin iwo)
                )
                0
                idwoset
          in
            foldl
              (\newset currentOrigin ->
                let
                  thisSet = Set.filter (\i -> (woOrigin i) == currentOrigin) idwoset
                  thisNewSet =
                    Set.fold
                      (\iwo tNS ->
                        let
                          usedHere =
                            Set.fold
                              (\(previousIWO,_) uH ->
                                if (getIdId $ woItem previousIWO) == (getIdId $ woItem iwo)
                                  then
                                    uH + 1
                                  else
                                    uH
                              )
                              0
                              tNS
                        in
                          Set.insert (iwo, usedHere) tNS
                      )
                      Set.empty
                      thisSet
                in
                  Set.union newset thisNewSet
              )
              Set.empty
              [0..maxorigin]
        )
        remMap
  in
    makeUniqueNodeNames unnMap

makeUniqueNodeNames::
  Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
makeUniqueNodeNames
  unnMap
  =
  Map.foldWithKey
    (\ln idset m ->
      let
        newidset =
          Set.fold
            (\(wid, c) nis ->
              case woItem wid of
                IdNodeName {} ->
                  let
                    previousUse =
                      Set.fold
                        (\(wid', _) pU ->
                          case woItem wid' of
                            IdNodeName {} ->
                              if (getIdId $ woItem wid') == (getIdId $ woItem wid)
                                then
                                  pU + 1
                                else
                                  pU
                            _ ->
                              pU
                        )
                        (0::Int)
                        nis
                  in
                    Set.insert (wid, previousUse) nis
                _ ->
                  Set.insert (wid, c) nis
            )
            Set.empty
            idset
      in
        Map.insert ln newidset m
    )
    Map.empty
    unnMap

makeUniqueNames::
  Map.Map LIB_NAME (Set.Set (IdentifierWON, Int))
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, String))
makeUniqueNames
  countMap
  =
  Map.map
    (\iwons ->
      Set.map
        (\(iwon, c) ->
          let
            ext = case c of 0 -> ""; _ -> "_" ++ (show c)
          in
            (iwon, (show (getIdId (woItem iwon))) ++ ext)
        )
        iwons
    )
    countMap

makeUniqueIdNameMapping::
  LibEnv
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, String)) 
  ->[IdNameMapping]
makeUniqueIdNameMapping
  lenv
  unnMap
  =
  foldl
    (\unnames ln ->
      let
        dg = devGraph $ Map.findWithDefault (error "!") ln lenv
        ids = Map.findWithDefault Set.empty ln unnMap
        dgnodes = filter (not . isDGRef . snd) $ Graph.labNodes dg
        senslist =
          concatMap
            (\(nn, node) -> map (\x -> (nn, x)) $ zip [0..] (getNodeSentences node))
            dgnodes
        senscons =
          concatMap
            (\(nodenum, (sennum, s)) ->
              Set.toList
                $
                Set.map
                  (\(cid, ot) -> (nodenum, (sennum, cid, ot)))
                  (extractConstructorOps s)
            )
            senslist
        sensfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdSens {} -> True; _ -> False)
            ids
        consfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdCons {} -> True; _ -> False)
            ids
      in
        foldl
          (\unnames' (nn, node) ->
            let
              nodeids =
                Set.filter
                  (\(i, _) -> woOrigin i == nn)
                  ids
              nodename =
                if not $ isDGRef node
                  then
                    case
                      Set.toList
                        $
                        Set.filter
                          (\(i,_) -> i == mkWON (IdNodeName (stringToId $ nodeNameToName $ dgn_name node)) nn)
                          ids
                    of
                      [] ->
                        Debug.Trace.trace
                          ("no node found for "
                            ++ show (nn, nodeNameToName $ dgn_name node) ++ "..."
                          )
                          (getDGNodeName node)
                      (_, unName):_ ->
                          unName
                  else
                    let
                      mln = dgn_libname node
                      mdg = devGraph $ Map.findWithDefault (error "!") mln lenv
                      mnn = dgn_node node
                      mnode = (\(Just a) -> a) $ Graph.lab mdg mnn
                    in
                      case
                        Set.toList
                          $
                          Set.filter
                            (\(i,_) ->
                              i ==
                                mkWON
                                  (IdNodeName (stringToId $ nodeNameToName $ dgn_name mnode))
                                  mnn
                            )
                            (Map.findWithDefault Set.empty mln unnMap)
                      of
                        [] -> Debug.Trace.trace
                          ("no refnode found... "
                            ++ show (ln, nn, nodeNameToName $ dgn_name node)
                            ++ " -> " ++ show (mln, mnn, nodeNameToName $ dgn_name mnode)
                          )
                          (nodeNameToName $ dgn_name mnode)
                        (_, unName):_ -> unName
              remappedsorts =
                Set.map
                  (\(i, uname) ->
                    (getIdId $ woItem i, uname)
                  )
                  (Set.filter (\(i, _) -> case woItem i of IdId {} -> True; _ -> False) nodeids)
              remappedops =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdOp oid ot) ->
                        ((oid, ot), uname)
                      _ -> error "!"
                  )
                  (Set.filter (\(i, _) -> case woItem i of IdOp {} -> True; _ -> False) nodeids)
              remappedpreds =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdPred pid pt) ->
                        ((pid, pt), uname)
                      _ -> error "!"
                  )
                  (Set.filter (\(i, _) -> case woItem i of IdPred {} -> True; _ -> False) nodeids)
              nodesensunn = Set.filter (\(i, _) -> woOrigin i == nn) sensfromunn
              nodesens =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdSens sensid sennum) ->
                        ((sensid, sennum), uname)
                      _ -> error "Non-sentence found in sentence processing...."
                  )
                nodesensunn
              nodeconsunn = Set.filter (\(i, _) -> woOrigin i == nn) consfromunn
              nodecons =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdCons conid conot sennum) ->
                        ((sennum, conid, conot), uname)
                      _ -> error "Non-constructor found in constructor processing...."
                  )
                nodeconsunn
                
            in
              unnames'
                ++
                [
                  (
                      ln
                    , dgn_name node
                    , nodename
                    , nn
                    , remappedsorts
                    , remappedpreds
                    , remappedops
                    , nodesens
                    , nodecons
                  )
                ]
          )
          unnames
          (Graph.labNodes dg)
    )
    []
    (Map.keys lenv)



makeFullNames::
  LibEnv
  ->Map.Map LIB_NAME (Set.Set (IdentifierWON, String))
  ->Map.Map (LIB_NAME, IdentifierWON) (LIB_NAME, IdentifierWON)
  ->[IdNameMapping]
makeFullNames
  lenv
  unnMap
  identMap
  =
  foldl
    (\fullnames ln ->
      let
        dg = devGraph $ Map.findWithDefault (error "!") ln lenv
        sortswomap = getSortsWOWithNodeDGNamesWO dg
        opswomap = getOpMapsWOWithNodeDGNamesWO dg
        predswomap = getPredMapsWOWithNodeDGNamesWO dg
        ids = Map.findWithDefault Set.empty ln unnMap
        dgnodes = filter (not . isDGRef . snd) $ Graph.labNodes dg
        senslist =
          concatMap
            (\(nn, node) -> map (\x -> (nn, x)) $ zip [0..] (getNodeSentences node))
            dgnodes
        senscons =
          concatMap
            (\(nodenum, (sennum, s)) ->
              Set.toList
                $
                Set.map
                  (\(cid, ot) -> (nodenum, (sennum, cid, ot)))
                  (extractConstructorOps s)
            )
            senslist
        sensfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdSens {} -> True; _ -> False)
            ids
        consfromunn =
          Set.filter
            (\(i, _) -> case woItem i of IdCons {} -> True; _ -> False)
            ids
      in
        foldl
          (\fullnames' (nn, node) ->
            let
              nodename =
                if not $ isDGRef node
                  then
                    case
                      Set.toList
                        $
                        Set.filter
                          (\(i,_) -> i == mkWON (IdNodeName (stringToId $ nodeNameToName $ dgn_name node)) nn)
                          ids
                    of
                      [] -> Debug.Trace.trace ("no node found for " ++ show (nn, nodeNameToName $ dgn_name node) ++ "...") (getDGNodeName node)
                      (_, unName):_ -> unName
                  else
                    let
                      mln = dgn_libname node
                      mdg = devGraph $ Map.findWithDefault (error "!") mln lenv
                      mnn = dgn_node node
                      mnode = (\(Just a) -> a) $ Graph.lab mdg mnn
                    in
                      case
                        Set.toList
                          $
                          Set.filter
                            (\(i,_) -> i == mkWON (IdNodeName (stringToId $ nodeNameToName $ dgn_name mnode)) mnn)
                            (Map.findWithDefault Set.empty mln unnMap)
                      of
                        [] -> Debug.Trace.trace ("no refnode found... " ++ show (ln, nn, nodeNameToName $ dgn_name node) ++ " -> " ++ show (mln, mnn, nodeNameToName $ dgn_name mnode) ) (nodeNameToName $ dgn_name mnode)
                        (_, unName):_ -> unName
              nodesortswo = Map.findWithDefault Set.empty (mkWON (dgn_name node) nn) sortswomap
              remappedsorts =
                Set.map
                  (\swo ->
                    let
                      sasid = mkWON (IdId (woItem swo)) (woOrigin swo)
                    in
                      case Map.lookup (ln, sasid) identMap of
                        Nothing ->
                          case
                            Set.toList
                              $
                              Set.filter
                                (\(i, _) -> i == sasid)
                                ids
                          of
                            [] ->
                              Debug.Trace.trace
                                ("no sort found... " ++ show swo)
                                ((woItem swo), show swo)
                            (_, unName):_ -> (woItem swo, unName)
                        (Just (mln, mid)) ->
                          case
                            Set.toList
                              $
                              Set.filter
                                (\(i, _) -> i == mid)
                                (Map.findWithDefault Set.empty mln unnMap)
                          of
                            [] ->
                              Debug.Trace.trace
                                ("no sort found... (ref) " ++ show swo)
                                ((woItem swo), show swo)
                            (_, unName):_ -> (woItem swo, unName)
                  )
                  nodesortswo
              nodeopswo = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) opswomap
              remappedops =
                Map.foldWithKey
                  (\idwo ots remops ->
                    Set.fold
                      (\ot ro ->
                        let
                          opasid = mkWON (IdOp (woItem idwo) ot) (woOrigin idwo)
                          newItem = 
                            case Map.lookup (ln, opasid) identMap of
                              Nothing ->
                                case
                                  Set.toList
                                    $
                                    Set.filter
                                      (\(i, _) -> i == opasid)
                                      ids
                                of
                                  [] ->
                                    Debug.Trace.trace
                                      ("no op found...")
                                      (((woItem idwo), ot), show idwo)
                                  (_, unName):_ -> (((woItem idwo), ot), unName)
                              (Just (mln, mid)) ->
                                case
                                  Set.toList
                                    $
                                    Set.filter
                                      (\(i, _) -> i == mid)
                                      (Map.findWithDefault Set.empty mln unnMap)
                                of
                                  [] ->
                                    Debug.Trace.trace
                                      ("no op found (ref)")
                                      (((woItem idwo), ot), show idwo)
                                  (_, unName):_ -> (((woItem idwo), ot), unName)
                        in
                          (Set.insert newItem ro)
                      )
                      remops
                      ots
                  )
                  Set.empty
                  nodeopswo
              nodepredswo = Map.findWithDefault Map.empty (mkWON (dgn_name node) nn) predswomap
              remappedpreds =
                Map.foldWithKey
                  (\idwo pts rempreds ->
                    Set.fold
                      (\pt rp ->
                        let
                          predasid = mkWON (IdPred (woItem idwo) pt) (woOrigin idwo)
                          newItem = 
                            case Map.lookup (ln, predasid) identMap of
                              Nothing ->
                                case
                                  Set.toList
                                    $
                                    Set.filter
                                      (\(i, _) -> i == predasid)
                                      ids
                                of
                                  [] ->
                                    Debug.Trace.trace
                                      ("no pred found...")
                                      (((woItem idwo), pt), show idwo)
                                  (_, unName):_ -> (((woItem idwo), pt), unName)
                              (Just (mln, mid)) ->
                                case
                                  Set.toList
                                    $
                                    Set.filter
                                      (\(i, _) -> i == mid)
                                      (Map.findWithDefault Set.empty mln unnMap)
                                of
                                  [] ->
                                    Debug.Trace.trace
                                      ("no pred found (ref)")
                                      (((woItem idwo), pt), show idwo)
                                  (_, unName):_ -> (((woItem idwo), pt), unName)
                        in
                          (Set.insert newItem rp)
                      )
                      rempreds
                      pts
                  )
                  Set.empty
                  nodepredswo
              nodesensunn = Set.filter (\(i, _) -> woOrigin i == nn) sensfromunn
              nodesens =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdSens sensid sennum) ->
                        ((sensid, sennum), uname)
                      _ -> error "Non-sentence found in sentence processing...."
                  )
                nodesensunn
              nodeconsunn = Set.filter (\(i, _) -> woOrigin i == nn) consfromunn
              nodecons =
                Set.map
                  (\(i, uname) ->
                    case woItem i of
                      (IdCons conid conot sennum) ->
                        ((sennum, conid, conot), uname)
                      _ -> error "Non-constructor found in constructor processing...."
                  )
                nodeconsunn
            in
              fullnames'
                ++
                [
                  (
                      ln
                    , dgn_name node
                    , nodename
                    , nn
                    , remappedsorts
                    , remappedpreds
                    , remappedops
                    , nodesens
                    , nodecons
                  )
                ]
          )
          fullnames
          (Graph.labNodes dg)
    )
    []
    (Map.keys lenv)


{- |
  Extend a list of unique names obtained from a minimal library environment
  by applying it to a full library environment and performing Id origin
  resolution according to a given list of TraceMarkS
-}
createFullNameMapping::
  LibEnv -- ^ full library environment
  ->TakenMap -- ^ mapping of taken items
  ->[TraceMark] -- ^ tracemarks used in creating unique names
  ->[IdNameMapping] -- ^ unique name sets
  ->[IdNameMapping]
createFullNameMapping
  lenv
  takenMap
  tracemarks
  uniqueNames
  =
    foldl
      (\fullnames (TraceMark (libname, nodename, nodenum, _)) ->
        let
          dg = devGraph $ Map.findWithDefault (error "This can't happen!") libname lenv
          node = (\(Just a) -> a) $ Graph.lab dg nodenum
          caslsign = (\(Just a) -> a) $ getCASLSign (dgn_sign node)
          mappedSorts =
            Set.fold
              (\sid ns->
                Set.insert
                  --(sid, findUniqueName libname nodenum sid inSorts)
                  (sid, findUniqueSortName libname nodenum sid)
                  ns
              )
              Set.empty
              (sortSet caslsign)
          mappedPreds =
            Map.foldWithKey
              (\pid pts mp ->
                Set.fold
                  (\pt mp' ->
                    Set.insert
                      -- ((pid, pt), findUniqueName libname nodenum pid (inPreds pt))
                      ((pid, pt), findUniquePredName libname nodenum pid pt)
                      mp'
                  )
                  mp
                  pts
              )
              Set.empty
              (predMap caslsign)
          mappedOps =
            Map.foldWithKey
              (\oid ots mo ->
                Set.fold
                  (\ot mo' ->
                    Set.insert
                      --((oid, ot), findUniqueName libname nodenum oid (inOps ot))
                      ((oid, ot), findUniqueOpName libname nodenum oid ot)
                      mo'
                  )
                  mo
                  ots
              )
              Set.empty
              (opMap caslsign)
          (uniqueNodeName, sens, cons) =
            case
              Data.List.find
                (\ inm ->
                  (inmGetLibName inm) == libname && (inmGetNodeNum inm) == nodenum
                )
                uniqueNames
            of
              Nothing ->
                if isDGRef node
                  then
                    let
                      reallibname = dgn_libname node
                      realnodenum = dgn_node node
                    in
                      case
                        Data.List.find
                          (\ inm ->
                            (inmGetLibName inm) == reallibname
                            && (inmGetNodeNum inm) == realnodenum
                          )
                          uniqueNames
                      of
                        Nothing ->
                          error
                            (
                              "No unique name for refnode "
                                ++ (show (libname, nodename, nodenum))
                            )
                        (Just inm) -> (inmGetNodeId inm, inmGetIdNameSensSet inm, inmGetIdNameConsSet inm)
                  else
                    error ("No unique name for node " ++ (show (libname, nodename, nodenum)))
              (Just inm) -> (inmGetNodeId inm, inmGetIdNameSensSet inm, inmGetIdNameConsSet inm)
        in
          if isDGRef node 
            then
              let
                reallibname = dgn_libname node
                realnodenum = dgn_node node
                mrealtupel =
                  getLNGN
                    (uniqueNames ++ fullnames)
                    reallibname
                    realnodenum
              in
                case mrealtupel of
                  Nothing -> error "something is seriously wrong with the tracemarks..."
                  (Just (_, dgnnn, uNN, _, mS, mP, mO, s, c)) ->
                    fullnames ++ [(libname, dgnnn, uNN, nodenum, mS, mP, mO, s, c)]
            else
              fullnames ++
                [(
                    libname
                  , dgn_name node
                  , uniqueNodeName
                  , nodenum
                  , mappedSorts
                  , mappedPreds
                  , mappedOps
                  , sens
                  , cons
                )]
      )
      []
      tracemarks
  where
    inSorts::IdNameMapping->Set.Set (Id.Id, String)
    inSorts = inmGetIdNameSortSet
    inPreds::PredType->IdNameMapping->Set.Set (Id.Id, String)
    inPreds pt inm =
      Set.fold
        (\((id', pt'), name) s ->
          if pt' == pt
            then
              Set.insert (id', name) s
            else
              s
        )
        Set.empty
        (inmGetIdNamePredSet inm)
    inOps::OpType->IdNameMapping->Set.Set (Id.Id, String)
    inOps ot inm =
      Set.fold
        (\((id', ot'), name) s ->
          if ot' == ot
            then
              Set.insert (id', name) s
            else
              s
        )
        Set.empty
        (inmGetIdNameOpSet inm)

    getImportsLevelOrder::[(LIB_NAME, Graph.Node)]->LIB_NAME->Graph.Node->[(LIB_NAME, Graph.Node)]
    getImportsLevelOrder visited ln nn =
      let
        dg =
          devGraph
            $
            Map.findWithDefault (error "!") ln lenv
        indefs =
          filter
            (\(from, _, dgl) ->
              (defLink dgl)
              &&
              (from /= nn)
              &&
              (case
                Data.List.find
                  (\(ln', nn') -> ln' == ln && nn' == from)
                  visited
               of
                Nothing -> True
                _ -> False
              ) 
            )
            (Graph.inn dg nn)
        intrans =
          map
            (\(from, _, _) ->
              let
                fnode = (\(Just a) -> a) $ Graph.lab dg from
              in
                if isDGRef fnode
                  then
                    (dgn_libname fnode, dgn_node fnode)
                  else
                    (ln, from)
            )
            indefs
        nextlevel =
          concatMap
            (\(ln', nn') ->
              getImportsLevelOrder
                ((ln, nn):visited)
                ln'
                nn'
            )
            intrans
      in
        (ln, nn):nextlevel

    findUniqueSortName::LIB_NAME->Graph.Node->Id.Id->String
    findUniqueSortName ln nn sid =
      case findSortOrigin lenv ln nn sid of
        Nothing -> Debug.Trace.trace ("huarg!") (show sid)
        (Just (oln, onn)) ->
          case
            getLNGN uniqueNames oln onn
          of
            (Just inm) ->
              case
                Set.toList
                  $
                  Set.filter
                    (\(uid, _) -> uid == sid)
                    (inmGetIdNameSortSet inm)
              of
                (_, uniqueName):_ -> uniqueName
                _ -> Debug.Trace.trace ("huarg2!") (show sid)
            _ -> Debug.Trace.trace ("huarg3!") (show sid)
    
    findUniqueOpName::LIB_NAME->Graph.Node->Id.Id->OpType->String
    findUniqueOpName ln nn oid ot =
      case findOpOrigin lenv ln nn oid ot of
        Nothing -> Debug.Trace.trace ("huarg!") (show oid)
        (Just (oln, onn)) ->
          case
            getLNGN uniqueNames oln onn
          of
            (Just inm) ->
              case
                Set.toList
                  $
                  Set.filter
                    (\((uid, uot), _) -> uid == oid && uot == ot)
                    (inmGetIdNameOpSet inm)
              of
                (_, uniqueName):_ -> uniqueName
                _ -> Debug.Trace.trace ("huarg2!") (show oid)
            _ -> Debug.Trace.trace ("huarg3!") (show oid)
    
    findUniquePredName::LIB_NAME->Graph.Node->Id.Id->PredType->String
    findUniquePredName ln nn pid pt =
      case findPredOrigin lenv ln nn pid pt of
        Nothing -> Debug.Trace.trace ("huarg!") (show pid)
        (Just (oln, onn)) ->
          case
            getLNGN uniqueNames oln onn
          of
            (Just inm) ->
              case
                Set.toList
                  $
                  Set.filter
                    (\((uid, upt), _) -> uid == pid && upt == pt)
                    (inmGetIdNamePredSet inm)
              of
                (_, uniqueName):_ -> uniqueName
                _ -> Debug.Trace.trace ("huarg2!") (show pid)
            _ -> Debug.Trace.trace ("huarg3!") (show pid)


    findUniqueName::LIB_NAME->Graph.Node->Id.Id->(IdNameMapping->Set.Set (Id.Id, String))->String
    findUniqueName ln nn sid getSet =
      
      case findUniqueNameM ln nn sid getSet of
        Nothing -> Debug.Trace.trace ("Id was not taken... faking for " ++ show sid) (show sid)
        (Just uN) -> uN

    findUniqueNameM::LIB_NAME->Graph.Node->Id.Id->(IdNameMapping->Set.Set (Id.Id, String))->Maybe String
    findUniqueNameM ln nn sid getSet =
      let
        takenEntry = Map.findWithDefault Map.empty (ln, nn) takenMap
        takenByOneOf =
          map fst $
          filter
            (\(_, (takenSorts, takenPreds, takenOps)) ->
              if Set.member sid takenSorts
                then
                  True
                else
                  case Map.lookup sid takenPreds of
                    (Just _) -> True
                    _ ->
                      case Map.lookup sid takenOps of
                        (Just _) -> True
                        _ -> False
            )
            (Map.toList takenEntry)
        searchTaken =
          (\sT ->
            case sT of
              Nothing ->
                Debug.Trace.trace ("no result for " ++ show sid ++ " in " ++ show (ln, nn) ++ " with takenEntry of " ++ show takenEntry ++ " l " ++ show (length takenByOneOf)) sT
              _ -> sT
          ) $
          anything $ map (\(tln, tnn) -> findUniqueNameM tln tnn sid getSet) takenByOneOf
      in
        case
          getLNGN uniqueNames ln nn
        of
          (Just inm) ->
            case
              Set.toList
                $
                Set.filter
                  (\(uid, _) -> uid == sid)
                  (getSet inm)
            of
              (_, uniqueName):_ -> Just uniqueName
              _ -> searchTaken
          _ -> searchTaken

{-    findUniqueName::LIB_NAME->Graph.Node->Id.Id->(IdNameMapping->Set.Set (Id.Id, String))->String
    findUniqueName ln nn sid getSet =
      case
        traceUniqueName ln nn sid getSet
      of
        Nothing -> Debug.Trace.trace ("faking unique name for " ++ show sid) (show sid)
        (Just uname) -> uname
      
    traceUniqueName::LIB_NAME->Graph.Node->Id.Id->(IdNameMapping->Set.Set (Id.Id, String))->Maybe String
    traceUniqueName tlibname tnodenum sid getSet =
      let
        tdg =
          devGraph
            $
            Map.findWithDefault (error "No possible!") tlibname lenv
        tnode = (\(Just a) -> a) $ Graph.lab tdg tnodenum
        (dg, node, nodenum, libname) =
          if isDGRef tnode
            then
              let
                rln = dgn_libname tnode
                rnn = dgn_node tnode
                rdg =
                  devGraph
                    $
                    Map.findWithDefault (error "No possible!") rln lenv
                rnode = (\(Just a) -> a) $ Graph.lab rdg rnn
              in
                (rdg, rnode, rnn, rln)
            else
              (tdg, tnode, tnodenum, tlibname)
        imports = getImportsLevelOrder [] libname nodenum
        (mUnique, _) =
          until
            (\(mUN, r) -> case mUN of Nothing -> null r; _ -> True)
            (\(_, (iLN, iNN):r) ->
              case
                getLNGN uniqueNames iLN iNN
              of
                (Just inm) ->
                  case
                    Set.toList
                      $
                      Set.filter
                        (\(uid, _) -> uid == sid)
                        (getSet inm)
                  of
                    (_, uniqueName):_ -> (Just uniqueName, [])
                    _ -> (Nothing, r)
                _ -> (Nothing, r)
            )
            (Nothing, imports)
      in
        mUnique -}
--    findUniqueName::LIB_NAME->Graph.Node->Id.Id->(IdNameMapping->Set.Set (Id.Id, String))->String
--    findUniqueName = traceUniqueNameR
 {-   findUniqueName::LIB_NAME->Graph.Node->Id.Id->(IdNameMapping->Set.Set (Id.Id, String))->String
    findUniqueName libname nodenum sid getSet =
      let
        (thePast, _) =
          until
            (\(_,tm) -> null tm)
            (\(tP, (tm@(ln, _, nn, _)):r) ->
              if ln == libname && nn == nodenum
                then
                  (tP ++ [tm], [])
                else
                  (tP ++ [tm], r)
            )
            ([], tracemarks)
        (mUniqueName, _) =
          until
            (\(mUN, tp) -> case mUN of Nothing -> False; _ -> null tp)
            (\(_, (ln, nname, nn, _):r) ->
              case
                Data.List.find
                  (\ inm ->
                    (inmGetLibName inm) == ln && (inmGetNodeNum inm) == nn
                  )
                  uniqueNames
              of
                Nothing ->
                  let
                    dg =
                      devGraph
                        $
                        Map.findWithDefault
                          (error "This can't happen!")
                          ln
                          lenv
                    node = (\(Just a) -> a) $ Graph.lab dg nn
                  in
                    if isDGRef node
                      then
                        let
                          refnode = dgn_node node
                          reflibname = dgn_libname node
                        in
                          case
                            Data.List.find
                              (\ inm ->
                                (inmGetLibName inm) == reflibname
                                && (inmGetNodeNum inm) == refnode
                              )
                              uniqueNames
                          of
                            Nothing ->
                              error
                                (
                                  "Error while searching Id from DGRef ("
                                    ++  (show sid) ++ ")"
                                )
                            (Just inm) ->
                              case
                                Set.toList
                                  $
                                  Set.filter (\(uid, _) -> uid == sid) (getSet inm)
                              of
                                [] -> (Nothing, r)
                                (_, uniqueName):_ -> (Just uniqueName, [])
                      else
                        error
                          ("Unable to find Id-Set for current node "
                            ++ (show (ln, nname, nn))
                          )
                (Just inm) ->
                  case
                    Set.toList
                      $
                      Set.filter
                        (\(uid, _) -> uid == sid)
                        (getSet inm)
                  of
                    [] -> (Nothing, r)
                    (_, uniqueName):_ -> (Just uniqueName, [])
            )
            (Nothing, (reverse thePast))
      in
        case mUniqueName of
          Nothing -> error ("No unique name for " ++ (show sid) ++ "!")
          (Just uniqueName) -> uniqueName -}
    
findOriginInCurrentLib::
  forall a .
  LIB_NAME
  ->[IdNameMapping]
  ->[IdNameMapping]
  ->(IdNameMapping->Maybe a)
  ->Maybe a
findOriginInCurrentLib
  _
  []
  []
  _
  =
    Nothing

findOriginInCurrentLib
  ln
  (inm:uniqueNames)
  fullNames
  check
  =
    let
      nextsearch = findOriginInCurrentLib ln uniqueNames fullNames check
    in
      if (inmGetLibName inm == ln)
        then
          case check inm of
            Nothing -> nextsearch
            ja -> ja
        else
          nextsearch

findOriginInCurrentLib
  ln
  []
  fullNames
  check
  =
    findOriginInCurrentLib
      ln
      fullNames
      []
      check
