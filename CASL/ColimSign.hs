{- |
Module      :  $Header$
Description :  CASL signatures colimits
Copyright   :  (c) Mihai Codescu, and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  mcodescu@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

CASL signature colimits, computed component-wise. 
Supposed to be working for CASL extensions as well.

-}

module CASL.ColimSign(signColimit, extCASLColimit) where

import Common.SetColimit
import CASL.AS_Basic_CASL
import Common.Lib.Graph
import Data.Graph.Inductive.Graph
import Data.List
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import CASL.Sign
import CASL.Morphism
import CASL.Overload

extCASLColimit :: Gr () (Int, ()) ->((),Map.Map Int ())
extCASLColimit graph = ((),Map.fromList $ zip (nodes graph) (repeat ()))

--central function for computing CASL signature colimits
signColimit :: Gr (Sign f e)(Int,Morphism f e m) ->
               (Gr e (Int, m) -> (e, Map.Map Int m)) ->
               (Sign f e, Map.Map Int (Morphism f e m))
signColimit graph extColimit = let
 getSortMap (x, phi) = (x,sort_map phi)
 sortGraph = emap getSortMap $ nmap sortSet graph
 (setSort0, funSort0) = computeColimitSet sortGraph
 (setSort, funSort) = renameSorts (setSort0, funSort0)
 sigmaSort = (emptySign $ error "err"){sortSet=setSort}
 phiSort = Map.fromList $ 
  map(\(node, s)-> (node, (embedMorphism (error "err") s sigmaSort)
                          {sort_map = (Map.!) funSort node})) $ 
  labNodes graph
 relS = computeSubsorts graph funSort
 sigmaRel = sigmaSort{sortRel = relS}
 phiRel = Map.fromList $ map (\(node, phi) -> (node, phi{mtarget = sigmaRel}))$
          Map.toList phiSort
 (sigmaOp, phiOp) = computeColimitOp graph sigmaRel phiRel
 (sigmaPred, phiPred) =  computeColimitPred graph sigmaOp phiOp
 (sigAssoc, phiAssoc) = colimitAssoc graph sigmaPred phiPred
 extGraph = emap (\(i, phi) -> (i, extended_map phi))$ nmap extendedInfo graph
 (extInfo, extMaps) = extColimit extGraph
 sigmaExt = sigAssoc{extendedInfo = extInfo}
 phiExt = Map.fromList $ 
  map (\(node, phi) -> (node, phi{mtarget = sigmaExt, 
                                  extended_map = (Map.!) extMaps node})) $ 
  Map.toList phiAssoc
 in (sigmaExt, phiExt)

-- method for adding the number as suffix of the id it pairs
addSuffixToId :: (Id, Node) -> Id
addSuffixToId (idN, n) = appendNumber idN n

--method for applying the renaming to the colimit of sorts
renameSorts :: (Set.Set (Id, Node), Map.Map Node (Map.Map Id (Id, Node))) -> 
               (Set.Set Id, Map.Map Node (EndoMap Id))
renameSorts (set, fun) = let
  fstEqual (x1,_) (x2,_) = x1 == x2
  partList pairSet =  leqClasses fstEqual pairSet
  namePartitions elemList f0 s1 f1 = case elemList of
   [] -> (s1, f1)
   p:ps -> if length p == 1 then 
     -- a single element with this name,it can be kept
    let s2 = Set.insert (fst $ head p) s1
        updateF node = Map.union ((Map.!) f1 node) $
                       Map.fromList $ map (\x -> (x, fst $ head p)) $
                       filter (\x -> (Map.!)((Map.!) f0 node) x == head p) $
                       Map.keys $ (Map.!) f0 node
        f2 = Map.fromList $ zip (Map.keys f0) $ map updateF $ Map.keys f0
    in namePartitions ps f0 s2 f2
                else 
     --several elements with same name, the number is added at the end
    let s2 = Set.union s1 $ Set.fromList $ map addSuffixToId p
        updateF node = Map.union ((Map.!) f1 node) $ Map.fromList $
             map ( \x -> (x, addSuffixToId $ (Map.!)((Map.!) f0 node) x )) $
             filter (\x -> ((Map.!)((Map.!) f0 node) x) `elem` p) $ 
             Map.keys $ (Map.!) f0 node
        f2 = Map.fromList $ zip (Map.keys f0) $ map updateF $ Map.keys f0
    in namePartitions ps f0 s2 f2
 in namePartitions (partList set) fun (Set.empty) $ 
    Map.fromList $ zip (Map.keys fun) (repeat Map.empty)

-- computing subsorts in the colimit
-- the subsort relation in the colimit is the transitive closure 
-- of the subsort relations in the diagram
-- mapped along the structural morphisms of the colimit
computeSubsorts :: Gr (Sign f e)(Int,Morphism f e m) -> 
    Map.Map Node (EndoMap Id) -> Rel.Rel Id
computeSubsorts graph funSort = let 
  getPhiSort (x, phi) = (x,sort_map phi)
  graph1 = nmap sortSet $ emap getPhiSort $ graph
  rels = Map.fromList $ map (\(node, sign) -> (node, sortRel sign)) $ 
         labNodes graph
 in subsorts (nodes graph1) graph1 rels funSort Rel.empty

-- rels is a function assigning to each node
-- the subsort relation of its label's elements

subsorts :: [Node] -> Gr (Set.Set SORT)(Int,Sort_map) -> 
   Map.Map Node (Rel.Rel SORT) -> Map.Map Node (EndoMap Id) -> Rel.Rel SORT -> 
   Rel.Rel SORT
subsorts listNode graph rels colimF rel =
 case listNode of
  [] -> rel
  x:xs -> case lab graph x of
    Nothing -> subsorts xs graph rels colimF rel
    Just set -> subsorts xs graph rels colimF (Rel.transClosure $
             Rel.union rel (Rel.fromList [ ((Map.!)((Map.!) colimF x) m ,
                                           (Map.!)((Map.!) colimF x) n)
              | m <- Set.elems set, n <- Set.elems set, 
                Rel.member m n ((Map.!) rels x) ]))

-- CASL signatures colimit on operation symbols

computeColimitOp :: Gr (Sign f e)(Int,Morphism f e m) ->
                    Sign f e -> Map.Map Node (Morphism f e m) ->
                    (Sign f e, Map.Map Node (Morphism f e m))
computeColimitOp graph sigmaRel phiSRel = let
 oEdges = Map.fromList $ zip (nodes graph) $ map (outdeg graph) $ nodes graph
 clsFun = solveOverloading graph (markEquivClasses graph) oEdges
    -- mark the equivalence classes
 opSetsList = nonEmptyOpSets graph $ Map.fromList $ 
              map (\(n, phi) -> (n, sort_map phi)) $ Map.toList phiSRel
    -- compute the list of OpTypes which will be non-empty in the colimit
 (opsList, morMap) = loopOpSets graph clsFun sigmaRel phiSRel opSetsList [] 
                     (Map.fromList $ zip (nodes graph) (repeat Map.empty))
    -- for each OpType, compute the colimit in Set
 (sigmaOp, phiOp) = renameOpSymbols graph opsList morMap sigmaRel phiSRel
    -- rename the operation symbols according to overloadings
 in (sigmaOp, phiOp)

data OpSymbolLabel = OpSymbolLabel{
                        arity :: OpType, -- the arity (in the colimit)
                        originNodes :: [Node], 
  -- list of all nodes where there are elements mapped to the symbol
                        classLabelsList :: [String] } 
  -- labels of all elements which are mapped to the symbol
   deriving (Eq, Ord, Show)

data ColimitOpSymbWithLabel = ColimitOpSymbWithLabel {
                               symbolName :: Id,
                               opSymbolLabel :: OpSymbolLabel}
   deriving (Eq, Ord, Show)

--renaming operation symbols in the colimit
renameOpSymbols :: Gr (Sign f e)(Int,Morphism f e m)
                -> [ColimitOpSymbWithLabel]
                -> Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel)
                -> Sign f e
                -> Map.Map Node (Morphism f e m)
                -> (Sign f e, Map.Map Node (Morphism f e m))
renameOpSymbols graph opsList morMap sigmaRel phiSRel = let
  (partList, partMap) =  tempNames opsList morMap [] $ 
                         Map.fromList $ zip (nodes graph) (repeat Map.empty)
  lengthDesc (_,s1) (_,s2) =
     case compare (length $ Set.toList s1)(length $ Set.toList s2) of
       LT -> GT
       GT -> LT
       EQ -> EQ
  ordList = sortBy lengthDesc partList
  (rezList, rezMap) = finalNames [] ordList partMap sigmaRel phiSRel
  sigmaOp = sigmaRel{opMap = Map.fromList $ 
    map (\(idN,set)->
    (idN, Set.fromList $ map arity $ Set.toList$ foldl Set.union Set.empty set)
        ) rezList}
  phiOp = let
    getKeys node = Map.keys$ (Map.!) rezMap node
    nonId ((id1, optype),(id2, fkind)) = (id1/=id2) || (opKind optype /= fkind)
   in Map.fromList $ map (\n -> (n, ((Map.!) phiSRel n)
      {fun_map = Map.fromList$ 
                 map (\((i1,opT),(i2,k)) -> ((i1,opT{opKind=Partial}),(i2,k)))
      $ filter nonId $ 
      zip (getKeys n) 
      (map(\x -> (symbolName x, opKind $ arity $ opSymbolLabel x))
      $ map ((Map.!)$(Map.!)rezMap n) $ getKeys n)})) $ nodes graph
 in (sigmaOp, phiOp)

-- this method assigns names to operation symbols in the colimit,
-- such that no new overloading is introduced between symbols originating
-- from the same sigature
-- and names are kept as similar with the original ones as possible
-- i.e. if in a signature two symbols have the same name but not overloaded 
-- and their images in the colimit are not in the overloading relation
-- they will be asigned the same name

finalNames :: [(Id, [Set.Set OpSymbolLabel])]
           -> [(Id, Set.Set OpSymbolLabel)]
           -> Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel)
           -> Sign f e
           -> Map.Map Node (Morphism f e m)
           -> ([(Id, [Set.Set OpSymbolLabel])], 
                Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel))
finalNames rezList opList opsMap1 sigmaRel phiSRel = let
 updateMap opsMap id0 pairList =
   case  pairList of
     [] -> opsMap
     (idN, set):pairs -> let
       opsMap2 = Map.fromList $ map (\node -> (node,Map.union
        (Map.fromList $ 
         map (\x -> (x,((opsMap Map.! node)Map.! x){symbolName = idN}))
        $ filter (\x -> (opsMap Map.! node)Map.! x `elem`
        (map (\y -> ColimitOpSymbWithLabel{symbolName = id0, opSymbolLabel = y})
        $ Set.toList set))
        $ Map.keys$ (Map.!) opsMap node)
        (opsMap Map.! node)) ) $ Map.keys opsMap
      in updateMap opsMap2 id0 pairs
  in  case opList of
   [] -> (rezList, opsMap1)
   (id0, set):ops -> case filter (\(x,_) -> x == id0) rezList of
     [] -> let  -- id hasn't occurred in the list yet
       rezList1 = rezList ++ [(id0, [set])]
       opsMap2 = updateMap opsMap1 id0 [(id0,set)]
      in finalNames rezList1 ops opsMap2 sigmaRel phiSRel
     (_, setList):_ -> let
       opSet =  Set.fromList $ map arity $ Set.toList set
       getOpTypes oSet = Set.fromList $ map arity $ Set.toList oSet
       opSetList = map getOpTypes setList
       oldFunSymbols = foldl Set.union Set.empty opSetList
       funSymbols = Set.union opSet oldFunSymbols
       sigmaId = sigmaRel{opMap = Map.fromList [(id0,funSymbols)]}
       leqFSets = Set.fromList $ map Set.fromList $ 
                  leqClasses (leqF sigmaId) funSymbols
      in if (Set.member opSet leqFSets) 
            && (not $  opSet `elem` opSetList) 
         then let -- no additional overloading
        rezList1 = filter (\(x,_) -> x /= id0) rezList ++ [(id0, set:setList)]
        opsMap2 = updateMap opsMap1 id0 [(id0,set)]
       in finalNames rezList1 ops opsMap2 sigmaRel phiSRel
         else let 
     -- overloading, remove the sets which create conflicts and assign new names
        opSets1 = filter (\s -> Set.intersection opSet s /= Set.empty)$ 
                  Set.toList leqFSets
        cSets = filter (\s -> Set.intersection 
          (foldl Set.union Set.empty opSets1) 
          (Set.fromList $ map arity $ Set.toList s)/= Set.empty) setList
        setList1 = Set.difference (Set.fromList setList) (Set.fromList cSets)
        rezList1 = if setList1 /= Set.empty then
           filter (\(x,_) -> x /= id0) rezList ++ [(id0, Set.toList setList1)]
                   else filter (\(x,_) -> x /= id0) rezList
        genNewName set0 idN = if setList1 == Set.empty then idN 
                                  --try to keep old name
          else let
           nodeList = foldl (++) []$map originNodes $ Set.toList set0
           nodeNr = head $ head $ sort $ group $ sort nodeList
          in appendNumber idN nodeNr --stringToId $ (show idN) ++ (show nodeNr)
        generateNames oldId nameList csetsList = case csetsList of
          [] -> nameList
          set0:sets -> let
            newId = genNewName set0 oldId
           in if newId `elem` nameList then let 
            prefix name = isPrefixOf (show newId) (show name) 
               -- TO DO check how this works for compound identifiers
            nr = length $ filter prefix nameList
            newId1 = appendNumber newId nr
           in generateNames oldId (nameList ++ [newId1]) sets
           else generateNames oldId (nameList ++ [newId]) sets
        ops2 = zip (generateNames id0 [] $ set:cSets) $ set:cSets
        opsMap2 = updateMap opsMap1 id0 ops2
       in finalNames rezList1 (ops++ops2) opsMap2 sigmaRel phiSRel


-- this method assigns temporary names to operation symbols
-- by grouping symbols which have to be overloaded
-- and giving each group the name that is majoritary 
-- in the corresponding subgraph

tempNames :: [ColimitOpSymbWithLabel]
         ->  Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel)
         ->  [(Id, Set.Set OpSymbolLabel)]
         ->  Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel)
         ->  ([(Id, Set.Set OpSymbolLabel)], 
               Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel))
tempNames opsList morMap rezList morMap1 =  loopGroups (groupOps opsList) 
                                             morMap rezList morMap1

groupOps :: [ColimitOpSymbWithLabel] ->  [[ColimitOpSymbWithLabel]]
groupOps opsList = let
  classFNames = map classLabelsList$ map opSymbolLabel opsList
  nameFun = joinCls classFNames
  ovrl e1 e2 = (Map.!) nameFun (head $ classLabelsList $ opSymbolLabel e1) == 
               (Map.!) nameFun (head $ classLabelsList $ opSymbolLabel e2)
 in leqClasses ovrl $ Set.fromList opsList


isMappedTo :: (Ord x, Ord n, Ord y)=> [y] -> Map.Map n (Map.Map x y) 
              -> n -> x -> Bool
isMappedTo yList f n x = (Map.!)((Map.!) f n)x `elem` yList

loopGroups :: [[ColimitOpSymbWithLabel]]
         ->  Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel)
         ->  [(Id, Set.Set OpSymbolLabel)]
         ->  Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel)
         ->  ([(Id, Set.Set OpSymbolLabel)], 
              Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel))
loopGroups splitOps  morMap rezList morMap1 =
  case splitOps of
    [] -> (rezList, morMap1)
    opGrp:ops -> let
      nodeList = Map.keys morMap
      keys node = filter (isMappedTo opGrp morMap node) $ 
                  Map.keys $ (Map.!) morMap node
      eList = foldl (++) [] $ map keys nodeList
      idList = nub $ map fst eList
      sndCompDesc (_,x)(_, y) = case compare x y of
          LT -> GT
          EQ -> EQ
          GT -> LT
      idName = fst $ head $ sortBy sndCompDesc $ zip idList $ 
               map (\x -> length $ filter (\(y,_) -> y == x) eList ) idList
      opTypeSet = Set.fromList $ map opSymbolLabel opGrp
      fnode node = let
       opKeys = filter (\x -> x `elem` eList) $ Map.keys $ (Map.!) morMap node
       newVals = zip opKeys $ map (\x -> x{symbolName =idName}) $ 
                 map ((Map.!)((Map.!)morMap node)) opKeys
       in Map.union (Map.fromList newVals) ((Map.!) morMap1 node)
      morMap2 = Map.fromList$ zip (Map.keys morMap1) $ map fnode $ 
                Map.keys morMap1
       in loopGroups ops morMap ((idName, opTypeSet):rezList) morMap2


opSymbols :: Sign f e -> [(Id, OpType)]
-- returns the list of all operation symbols in a signature, 
-- as pairs (Id,OpType)
opSymbols sigma =  foldl (++) [] $ 
                map (\(idX, opTSet) -> map (\y -> (idX, y)) $ 
                     Set.toList opTSet) $ Map.toList $ opMap sigma

loopOpSets :: Gr (Sign f e)(Int, Morphism f e m)
           -> Map.Map Node (Map.Map (Id, OpType) String)
           -> Sign f e
           -> Map.Map Node (Morphism f e m)
           -> [OpType]
           -> [ColimitOpSymbWithLabel]
           -> Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel)
           -> ([ColimitOpSymbWithLabel],
               Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel))
loopOpSets graph clsFun sigmaRel phiSRel opSetsList opsList morMap =
 case opSetsList of
  [] -> (opsList, morMap)
  opSet:opSets -> let
   funSort = Map.fromList $ zip (nodes graph) $ map sort_map $ 
             map ((Map.!)phiSRel) $ nodes graph
   graph1 = buildOpGraphNodes graph (duplShape graph) funSort opSet $
            labNodes graph
   (setN, funN) =  computeColimitSet graph1
   (opsList1, morMap1) = labelColimitElements funSort clsFun setN funN
   opsList2 =  opsList ++ opsList1
   morMap2 = Map.fromList $ map (\n-> (n, Map.union (morMap1 Map.! n)
                                      (morMap Map.!n))) $ nodes graph
   in loopOpSets graph clsFun sigmaRel phiSRel opSets opsList2 morMap2

------------------------------------------------------------------
sameOpLabel :: Map.Map Node (Map.Map (Id,OpType) String) ->
             ((Id, OpType),Node) -> ((Id, OpType),Node) -> Bool
-- returns true if the opsymbols have the same name 
-- and the same label
sameOpLabel clsFun ((id1, op1),n1)((id2,op2),n2) = (id1 == id2) && 
   (clsFun Map.! n1) Map.! (id1, op1) == 
   (clsFun Map.! n2) Map.! (id2, op2)

labelColimitElements :: Map.Map Node Sort_map
        -> Map.Map Node (Map.Map (Id, OpType) String)
        -> Set.Set ((Id,OpType), Node)
        -> Map.Map Node (Map.Map (Id, OpType) ((Id, OpType), Node))
        -> ([ColimitOpSymbWithLabel], 
            Map.Map Node (Map.Map (Id, OpType) ColimitOpSymbWithLabel))
--here is where the colimit is transformed to our internal format
labelColimitElements funSort clsFun setN funN = let
  elemGroups = leqClasses (sameOpLabel clsFun) setN
  mapGrp opResList rList rFun = let
     ((idH,optypeH),nH) = head opResList
     nodeList = map snd opResList
     clsList = map (\((idX, optX),nX) -> (Map.!)((Map.!)clsFun nX)(idX, optX)) 
               opResList
     mappedElems = [(idX, optype) | node<- Map.keys funN, 
                   (idX, optype) <- Map.keys $ (Map.!) funN node,
                   (Map.!)((Map.!) funN node) (idX, optype) `elem` opResList]
     allPartial optypeList = let
       isTotal optype = opKind optype == Total
      in if filter isTotal optypeList == [] then Partial else Total
     fKind = allPartial $ map snd  mappedElems
     opTypeRes = (mapOpType ((Map.!)funSort nH) optypeH){opKind = fKind}
     res = ColimitOpSymbWithLabel{
           symbolName = idH, 
           opSymbolLabel = OpSymbolLabel{
              arity = opTypeRes,
              originNodes = nodeList,
              classLabelsList =clsList}}
     rList1 = res : rList
     rFun1 = Map.fromList $ 
             map (\n -> (n, Map.union
                            (Map.fromList$ map (\x ->(x,res))$ 
                            filter (isMappedTo opResList funN n)$
                            Map.keys $  funN Map.! n) $
                            rFun Map.! n)) 
             $ Map.keys funN    
   in (rList1, rFun1)
  loopGroupList grpList rList rFun =
    case grpList of
     [] -> (rList, rFun)
     grp : grps -> let (rList1, rFun1) = mapGrp grp rList rFun
                   in loopGroupList grps rList1 rFun1
 in loopGroupList elemGroups [] $ Map.fromList $ 
    zip (Map.keys funSort) (repeat Map.empty)

buildOpGraphNodes :: Gr (Sign f e)(Int, Morphism f e m)
       -> Gr (Set.Set (Id, OpType))(Int,EndoMap (Id, OpType))
       -> Map.Map Node (Map.Map SORT SORT)
       -> OpType
       -> [(Node, Sign f e)]
       -> Gr (Set.Set (Id, OpType))(Int,EndoMap (Id, OpType))
buildOpGraphNodes graph graph0 funSort oT lNodeList = case lNodeList of
  [] -> buildOpGraphEdges graph0 (labEdges graph)
  (node, sigma):lnodes -> let
     profile = getArityName oT
     arityList = preImageWord ((Map.!)funSort node) profile
     opsWithArity sigma1 ar = filter (\x -> getOpArityName x == ar) $ 
                              opSymbols sigma1
     graph1 = changeNodeLabel graph0 node $ Set.fromList $ 
              foldl (++) [] $ map (opsWithArity sigma) arityList
    in buildOpGraphNodes graph graph1 funSort oT lnodes

buildOpGraphEdges :: Gr (Set.Set (Id, OpType))(Int,EndoMap (Id, OpType)) -> 
  [LEdge (Int, Morphism f e m)] -> 
  Gr (Set.Set (Id, OpType))(Int,EndoMap (Id, OpType))
buildOpGraphEdges graph0 edgeList = case edgeList of
  [] -> graph0
  (sn, tn, (nr, phi)):edgeL -> case lab graph0 sn of
     Nothing -> buildOpGraphEdges graph0 edgeL
     Just opSet -> buildOpGraphEdges 
                   ( changeEdgeLabel graph0 (sn, tn, (nr, Map.empty))
                    (nr, Map.fromList $ map (\x -> (x, applyMor phi x)) $ 
                     Set.toList opSet)) 
                   edgeL

getOpArityName :: (Id, OpType) -> [SORT]
getOpArityName (_, optype) = (opRes optype):(opArgs optype)

getArityName :: OpType -> [SORT]
getArityName optype = (opRes optype):(opArgs optype)

getEquivClassesNames :: Map.Map (Id, OpType) String -> [String]
-- returns all the equivalence classes corresponding to a signature, 
-- which is given by the already partitioned set of operation symbols
getEquivClassesNames clsFun = nub $ Map.elems clsFun

markEquivClasses :: Gr (Sign f e)(Int, Morphism f e m) ->
                     Map.Map Node (Map.Map (Id,OpType) String)
markEquivClasses graph = Map.fromList $
 map (\(n, s)->(n, 
    nameClasses n (Map.keys $ opMap s)(equivFClasses s) Map.empty)) $ 
 labNodes graph

leqClasses :: Ord a => (a -> a -> Bool) -> Set.Set a -> [[a]]
--partition a set into classes according to a parameter relation eq
leqClasses eq os = map Set.toList $ Rel.partSet eq os

equivFClasses :: Sign f e -> Map.Map Id [[OpType]]
-- return all the equivalence classes in a signature
-- as a function from id to a list of lists of idtype, 
-- each member of the list is an equivalence class
equivFClasses sig = Map.fromList $ 
 map (\(idN, set) -> (idN, leqClasses (leqF sig) set)) $ Map.toList $ opMap sig

nameClasses :: Int -> [Id]-> Map.Map Id [[OpType]] -> Map.Map (Id,OpType) String
               -> Map.Map (Id, OpType) String
--assigns unique names to equivalence classes
nameClasses noNode idList clsFun nameFun = case idList of
 [] -> nameFun
 idN:xs -> nameClasses noNode xs clsFun $
          Map.union nameFun 
                    (nameId (noNode, 0) idN ((Map.!)clsFun idN) Map.empty)

showP :: OpType -> String
showP optype = (foldl (++) "" $ map show $ opArgs optype) ++ "->"++ 
               (show $ opRes optype)

nameId :: (Int, Int) -> Id -> [[OpType]] -> Map.Map (Id, OpType) String ->  
          Map.Map (Id, OpType) String
-- names equivalence classes of an id
-- each class gets the name idname_nodeNumber_Number
-- where the last Number starts at 0 and is increased for each class
nameId (x1,y1) idN clsList f = case clsList of
  [] -> f
  l:ls -> nameId (x1,y1+1) idN ls $ Map.union f $ 
          Map.fromList$ map (\optype -> ((idN,optype), 
         show idN ++ "_" ++ showP (head l)++ "_" ++ show x1 ++ "_"++show y1))l


solveOverloading :: Gr (Sign f e)(Int,Morphism f e m) -> 
                    Map.Map Node (Map.Map (Id, OpType) String) -> 
                    Map.Map Node Int -> 
                    Map.Map Node (Map.Map (Id, OpType) String)
solveOverloading graph clsFun oEdges= let 
   labEdgesList = orderByOutgoingEdges (labEdges graph) graph oEdges
  in fwdOverloading graph (loopMorphisms labEdgesList graph clsFun oEdges)

fwdOverloading :: Gr (Sign f e)(Int,Morphism f e m) -> 
                  Map.Map Node (Map.Map (Id, OpType) String) -> 
                  Map.Map Node (Map.Map (Id, OpType) String)
fwdOverloading graph clsFun = let 
  incomEdges = initialDegrees graph
  nodeList = orderByIncomingEdges (nodes graph) graph incomEdges
 in loopNodesOvr graph clsFun incomEdges nodeList

loopNodesOvr :: Gr (Sign f e)(Int,Morphism f e m) -> 
                Map.Map Node (Map.Map (Id, OpType) String) -> 
                Map.Map Node Int -> [Node] -> 
                Map.Map Node (Map.Map (Id, OpType) String)
loopNodesOvr graph clsFun incomEdges nodeList = case nodeList of
  [] -> clsFun
  node:nods -> let
    succs = lsuc graph node
    incomEdges1 = updateDegrees graph node incomEdges
    nodeList1 = orderByIncomingEdges (nods) graph incomEdges1
   in loopNodesOvr graph (loopSuccs clsFun succs node) incomEdges1 nodeList1

loopSuccs :: Map.Map Node (Map.Map (Id, OpType) String) -> 
             [(Node,(Int, Morphism f e m))] -> Node -> 
             Map.Map Node (Map.Map (Id, OpType) String)
loopSuccs clsFun succs node = case succs of
  [] -> clsFun
  (tn, (_, phi)):succs1 -> let
    opSyms = Map.keys $ (Map.!) clsFun node
    targetSyms = Map.keys $ (Map.!) clsFun tn
    sameClass y z = (Map.!)((Map.!) clsFun tn) y == (Map.!)((Map.!) clsFun tn) z
    fNode = Map.union
            (Map.fromList $ foldl (++) [] $
            map (\x -> let y = applyMor phi x in 
                  zip (filter (sameClass y) targetSyms)
                      (repeat $(Map.!)((Map.!) clsFun node) x)) opSyms)
            $ (Map.!) clsFun tn
    clsFun1 = Map.insert tn fNode clsFun
   in loopSuccs clsFun1  succs1 node

-- take a morphism from the list,
-- call of a function: for each class of the target signature, 
-- mark the elements in preimage with the name of the class
-- then 'remove' the morphism from graph and re-order list
-- repeat until list is empty
loopMorphisms :: [LEdge (Int, Morphism f e m)] -> 
                 Gr (Sign f e)(Int, Morphism f e m) -> 
                 Map.Map Node (Map.Map (Id, OpType) String) -> 
                 Map.Map Node Int -> Map.Map Node (Map.Map (Id, OpType) String)
loopMorphisms list graph clsFun oEdges= case list of
   [] -> clsFun
   (sn, tn, (_,phi)):xs -> let
     -- get the list of equiv classes in target node
     equivClassesList = getEquivClassesNames ((Map.!)clsFun tn)
     clsFun1 = renameViaMorphism graph (sn, tn, phi) equivClassesList clsFun
     val = (Map.!) oEdges sn
     oEdges1 = Map.insert sn (val-1) oEdges
     xs1 = orderByOutgoingEdges xs graph oEdges1
    in loopMorphisms xs1 graph clsFun1 oEdges1

renameViaMorphism :: Gr (Sign f e)(Int, Morphism f e m) -> 
                     (Node,Node, Morphism f e m) -> [String] -> 
                     Map.Map Node (Map.Map (Id, OpType) String) -> 
                     Map.Map Node (Map.Map (Id, OpType) String)
renameViaMorphism graph (sn, tn, phi) equivClassesList clsFun = 
 case equivClassesList of
   [] -> clsFun
   cls:xs -> let
     preIm = preImageCls  phi ((Map.!) clsFun sn) ((Map.!) clsFun tn) cls
     clsFun1 = Map.insert sn 
               (Map.union (Map.fromList$ map (\x -> (x, cls)) preIm) $ 
                           (Map.!) clsFun sn) 
               clsFun
    in renameViaMorphism graph (sn, tn, phi) xs clsFun1

preImageCls :: Morphism f e m -> Map.Map (Id, OpType) String -> 
               Map.Map (Id, OpType) String -> String ->  [(Id, OpType)]
--preimage of an equivalence class via a morphism
preImageCls phi clsFunS clsFunT cls = filter 
   (\(idN, opT) -> ((Map.!) clsFunT $ applyMor phi (idN,opT)) == cls) $
   Map.keys clsFunS

applyMor :: Morphism f e m -> (Id, OpType) -> (Id, OpType)
applyMor phi (i, optype) = mapOpSym (sort_map phi) (fun_map phi) (i, optype)

orderByOutgoingEdges :: [LEdge (Int,Morphism f e m)] -> 
     Gr (Sign f e)(Int, Morphism f e m) -> Map.Map Node Int -> 
     [LEdge (Int, Morphism f e m)]
orderByOutgoingEdges list graph oEdges =
  case list of
   [] -> []
   (sn, tn, (i,phi)):xs -> (orderByOutgoingEdges 
     (filter (\(_,tn1,(_,_))->((Map.!) oEdges tn1) <= ((Map.!) oEdges tn)) xs)
      graph oEdges)
    ++ [(sn,tn,(i, phi))] ++ 
    (orderByOutgoingEdges (
     filter (\(_,tn1,(_,_))->((Map.!) oEdges tn1) > ((Map.!) oEdges tn)) xs) 
    graph oEdges )

joinCls :: [[String]] -> Map.Map String String
joinCls classesF = let
  clsNames = Map.fromList $ map (\x -> (x,x)) $ nub $ foldl (++) [] classesF
  relCls = filter (\list -> length list > 1) classesF
  joinClasses clsNames0 relCls0 = case relCls0 of
    [] -> clsNames0
    list : lists -> joinClasses (Map.union 
                      (Map.fromList $ map (\x-> (x,head list)) list) clsNames0)
                    lists
 in joinClasses clsNames relCls

nonEmptyOpSets :: Gr (Sign f e)(Int, Morphism f e m) ->
                Map.Map Node Sort_map ->
                [OpType]
nonEmptyOpSets graph funSort = let
  nodeList = labNodes graph
  opSets fSort (node, sigma) = map (mapOpType ((Map.!) fSort node)) $ 
       Set.toList $ foldl Set.union Set.empty $ Map.elems $ opMap sigma
 in Set.toList $ Set.fromList $ 
    map (makeTotal Total) $ foldl (++) [] $  map (opSets funSort) nodeList

productList :: [[a]] -> [[a]] -> [[a]]
productList l1 l2 = [x++y | x<-l1, y <-l2]

preImageWord :: Sort_map -> [SORT] -> [[SORT]]
preImageWord fs w = let
  preImage f s = filter (\x -> (Map.!) f x == s) $ Map.keys f
  lists l = case l of
    [] -> []
    x:xs -> [x]:(lists xs)
   in foldl productList [[]] $ map lists $ map (preImage fs) w

-- auxiliaries for working with a graph

changeNodeLabel :: Gr a b -> Node -> a -> Gr a b
changeNodeLabel graph node label = let
  graphFun = convertToMap graph
  (iedges, _, oedges) = (IntMap.!) graphFun node
  updFun = IntMap.insert node (iedges, label, oedges) graphFun
 in unsafeConstructGr updFun

changeEdgeLabel :: (Eq b) => Gr a (Int, b) -> LEdge(Int, b) -> (Int,b) -> 
  Gr a (Int,b)
changeEdgeLabel graph (sn,tn,olab) label = let
   graphFun = convertToMap graph
   (incS, lS, outS) = (IntMap.!) graphFun sn
   outS' = [(label,tn)] ++ (filter (/= (olab,tn)) outS)
   (incT, lT, outT) = (IntMap.!) graphFun tn
   incT' = [(label, sn)] ++ (filter (/= (olab,sn)) incT)
   graphFun' = IntMap.insert sn (incS, lS, outS') $ 
               IntMap.insert tn (incT', lT, outT) graphFun
 in unsafeConstructGr graphFun'

duplShape :: Gr a (Int,b) -> Gr (Set.Set c) (Int,Map.Map c c)
duplShape graph = emap (\(nr,_) -> (nr, Map.empty)) $ 
                  nmap (\_ -> Set.empty) graph

{--CASL signatures colimit on predicate symbols
almost identical with operation symbols, 
only minor changes because of different types
--}

computeColimitPred :: Gr (Sign f e)(Int,Morphism f e m) -> Sign f e -> 
      Map.Map Node (Morphism f e m) -> (Sign f e, Map.Map Node (Morphism f e m))
computeColimitPred graph sigmaOp phiOp = let 
  oEdges = Map.fromList $ zip (nodes graph) $ map (outdeg graph) (nodes graph)
  clsFun = solvePOverloading graph (markEquivPClasses graph) oEdges  
           -- mark the equivalence classes and join them 
  predSetsList = nonEmptyPredSets graph $ Map.fromList $ 
                 map (\(n,phi) -> (n, sort_map phi)) $  Map.toList phiOp
  (predList, morMap) = loopPredSets graph clsFun sigmaOp phiOp predSetsList [] 
                       (Map.fromList $ zip (nodes graph) (repeat Map.empty))
  (sigmaPred, phiPred) = renamePredSymbols graph predList morMap sigmaOp phiOp
 in (sigmaPred, phiPred)

getEquivPClassesNames :: Map.Map (Id, PredType) String -> [String]
-- returns all the equivalence classes corresponding to a signature, 
-- which is given by the already partitioned set of operation symbols
getEquivPClassesNames clsFun = nub $ Map.elems clsFun

markEquivPClasses :: Gr (Sign f e)(Int, Morphism f e m) -> 
                     Map.Map Node (Map.Map (Id,PredType) String)
markEquivPClasses graph = Map.fromList $ 
   map (\(node, sigma) -> (node, namePClasses node (Map.keys (predMap sigma)) (
                                 equivPClasses sigma)  Map.empty)) $ 
   labNodes graph

equivPClasses :: Sign f e -> Map.Map Id [[PredType]]
-- return all the equivalence classes in a signature
-- as a function from id to a list of lists of idtype, 
-- each member of the list is an equivalence class
equivPClasses sigma = Map.fromList $ 
  map (\(i, set)->(i, leqClasses (leqP sigma) set)) $ Map.toList $ predMap sigma

namePClasses :: Int -> [Id]-> Map.Map Id [[PredType]] -> 
   Map.Map (Id,PredType) String -> Map.Map (Id, PredType) String
--assigns unique names to equivalence classes
namePClasses noNode idList clsFun nameFun = case idList of
  [] -> nameFun
  i:xs -> namePClasses noNode xs clsFun $
          Map.union nameFun (namePId (noNode, 0) i (clsFun Map.! i) Map.empty)

showPred :: PredType -> String
showPred predtype = foldl (++) "" $ map show $ predArgs predtype

namePId :: (Int, Int) -> Id -> [[PredType]] -> Map.Map (Id, PredType) String ->
           Map.Map (Id, PredType) String
-- names equivalence classes of an id
-- each class gets the name idname_nodeNumber_Number, 
-- where the last Number starts at 0 and is increased for each class
namePId (x1,y1) i clsList f = case clsList of
  [] -> f
  l:ls -> namePId (x1,y1+1) i ls $ 
          Map.union f $ Map.fromList $ 
          map (\pT -> ((i,pT), 
          show i ++ "_" ++ showPred (head l)++ "_" ++show x1++ "_"++show y1)) l

solvePOverloading :: Gr (Sign f e)(Int,Morphism f e m) -> 
   Map.Map Node (Map.Map (Id, PredType) String) -> Map.Map Node Int -> 
   Map.Map Node (Map.Map (Id, PredType) String)
solvePOverloading graph clsFun oEdges = let 
  labEdgesList = orderByOutgoingEdges (labEdges graph) graph oEdges
 in fwdPOverloading graph (loopMorphismsP labEdgesList graph clsFun oEdges)

fwdPOverloading :: Gr (Sign f e)(Int,Morphism f e m) -> 
  Map.Map Node (Map.Map (Id, PredType) String) -> 
  Map.Map Node (Map.Map (Id, PredType) String)
fwdPOverloading graph clsFun = let 
   incomEdges = initialDegrees graph
   nodeList = orderByIncomingEdges (nodes graph) graph incomEdges
 in loopNodesOvrP graph clsFun incomEdges nodeList

loopNodesOvrP :: Gr (Sign f e)(Int,Morphism f e m) -> 
  Map.Map Node (Map.Map (Id, PredType) String) -> Map.Map Node Int -> 
  [Node] -> Map.Map Node (Map.Map (Id, PredType) String)
loopNodesOvrP graph clsFun incomEdges nodeList = case nodeList of
  [] -> clsFun
  node:nods -> let
    succs = lsuc graph node
    incomEdges1 = updateDegrees graph node incomEdges
    nodeList1 = orderByIncomingEdges (nods) graph incomEdges1
   in loopNodesOvrP graph (loopSuccsP clsFun succs node) incomEdges1 nodeList1

loopSuccsP :: Map.Map Node (Map.Map (Id, PredType) String) -> 
  [(Node,(Int, Morphism f e m))] -> Node -> 
  Map.Map Node (Map.Map (Id, PredType) String)
loopSuccsP clsFun succs node = case succs of
  [] -> clsFun
  (tn, (_, phi)):succs1 -> let
     predSyms = Map.keys $ (Map.!) clsFun node
     targetSyms = Map.keys $ (Map.!) clsFun tn
     sameClass y z = (Map.!)((Map.!) clsFun tn) y == 
                     (Map.!)((Map.!) clsFun tn) z
     fNode = Map.union (Map.fromList $ foldl (++) [] $
         map (\x -> let y = applyMorP phi x in 
              zip (filter (sameClass y) targetSyms)
                  (repeat $(Map.!)((Map.!) clsFun node) x)) 
         predSyms) ((Map.!) clsFun tn)
     clsFun1 = Map.insert tn fNode clsFun
    in loopSuccsP clsFun1  succs1 node

applyMorP :: Morphism f e m -> (Id, PredType) -> (Id, PredType)
applyMorP phi (i, predtype) = mapPredSym (sort_map phi) (pred_map phi) 
                              (i, predtype)

-- take a morphism from the list,
-- call of a function: 
--     for each class of the target signature, 
--     mark the elements in preimage with the name of the class
-- then 'remove' the morphism from graph and re-order list
-- repeat until list is empty
loopMorphismsP :: [LEdge (Int, Morphism f e m)]
              -> Gr (Sign f e)(Int, Morphism f e m)
              -> Map.Map Node (Map.Map (Id, PredType) String)
              -> Map.Map Node Int
              -> Map.Map Node (Map.Map (Id, PredType) String)
loopMorphismsP list graph clsFun oEdges= case list of
   [] -> clsFun
   (sn, tn, (_,phi)):xs -> let
                 -- get the list of equiv classes in target node
      equivClassesList = getEquivPClassesNames ((Map.!)clsFun tn)
      clsFun1 = renameViaMorphismP graph (sn, tn, phi) equivClassesList clsFun
      val = (Map.!) oEdges sn
      oEdges1 = Map.insert sn (val-1) oEdges
      xs1 = orderByOutgoingEdges xs graph oEdges1
     in loopMorphismsP xs1 graph clsFun1 oEdges1

renameViaMorphismP :: Gr (Sign f e)(Int, Morphism f e m) -> 
   (Node, Node, Morphism f e m) -> [String] -> 
   Map.Map Node (Map.Map (Id, PredType) String)
   -> Map.Map Node (Map.Map (Id, PredType) String)
renameViaMorphismP graph (sn, tn, phi) equivClassesList clsFun = 
  case equivClassesList of
    [] -> clsFun
    cls:xs -> let
      preIm = preImageClsP  phi ((Map.!) clsFun sn) ((Map.!) clsFun tn) cls
      clsFun1 = Map.insert sn 
                (Map.union (Map.fromList$ map (\x -> (x, cls))preIm) 
                 ((Map.!) clsFun sn)) 
                clsFun
     in renameViaMorphismP graph (sn, tn, phi) xs clsFun1

preImageClsP :: Morphism f e m -> Map.Map (Id, PredType) String -> 
   Map.Map (Id, PredType) String -> String ->  [(Id, PredType)]
--preimage of an equivalence class via a morphism
preImageClsP phi clsFunS clsFunT cls = filter 
  (\(i, pT) -> ((Map.!) clsFunT $ applyMorP phi (i,pT))==cls) $ Map.keys clsFunS

nonEmptyPredSets :: Gr (Sign f e)(Int, Morphism f e m) ->
          Map.Map Node Sort_map ->
          [PredType]
nonEmptyPredSets graph funSort = let
  nodeList = labNodes graph
  predSets (node, sigma) = map (mapPredType ((Map.!) funSort node)) $ 
         Set.toList $ foldl Set.union Set.empty $ Map.elems $ predMap sigma
 in nub $ foldl (++) [] $  map predSets  nodeList

data PredSymbolLabel = PredSymbolLabel{
   arityP :: PredType,
   originNodesP :: [Node],
   classLabelsListP :: [String]}
 deriving (Eq, Ord)

data ColimitPredSymbWithLabel = ColimitPredSymbWithLabel {
    symbolNameP :: Id,
    predSymbolLabel :: PredSymbolLabel}
 deriving (Eq, Ord)

renamePredSymbols :: Gr (Sign f e)(Int,Morphism f e m) -> 
    [ColimitPredSymbWithLabel] ->
    Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel) ->
    Sign f e -> Map.Map Node (Morphism f e m) -> 
    (Sign f e, Map.Map Node (Morphism f e m))
renamePredSymbols graph predsList morMap sigmaRel phiSRel = let
  (partList, partMap) = tempPNames predsList morMap [] $ Map.fromList $ 
                        zip (nodes graph) (repeat Map.empty)
  lengthDesc (_,s1) (_,s2) = 
     case compare (length $ Set.toList s1)(length $ Set.toList s2) of
       LT -> GT
       GT -> LT
       EQ -> EQ
  ordList = sortBy lengthDesc partList
  (rezList, rezMap) = finalPNames [] ordList partMap sigmaRel phiSRel
  sigmaPred = sigmaRel{predMap = Map.fromList $ map (\(idN, set) ->
              (idN, Set.fromList $ map arityP $ Set.toList$ 
                    foldl Set.union Set.empty set)
              ) rezList }
  phiPred = let
     getKeys node = Map.keys$ (Map.!) rezMap node
    in Map.fromList $ map (\node -> (node, ((Map.!) phiSRel node)
          {pred_map = Map.fromList $ filter (\((id1,_),id2) -> id1 /= id2) $ 
          zip (getKeys node) (map symbolNameP $ map ((Map.!)$(Map.!)rezMap node)
          $ getKeys node)})) $ nodes graph
 in (sigmaPred, phiPred)

-- this method assigns names to operation symbols in the colimit,
-- such that no new overloading is introduced between symbols originating
-- from the same sigature
-- and names are kept as similar with the original ones as possible
-- i.e. if in a signature two symbols have the same name but not overloaded 
-- and their images in the colimit are not in the overloading relation
-- they will be asigned the same name

finalPNames :: [(Id, [Set.Set PredSymbolLabel])]
           -> [(Id, Set.Set PredSymbolLabel)]
           -> Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel)
           -> Sign f e
           -> Map.Map Node (Morphism f e m)
           -> ([(Id, [Set.Set PredSymbolLabel])], 
              Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel))
finalPNames rezList predList predsMap1 sigmaRel phiSRel = let
  updateMap predsMap id0 pairList = case  pairList of
    [] -> predsMap
    (idN, set):pairs -> let
       predsMap2 = Map.fromList $ map (\node -> (node,Map.union
          (Map.fromList $ map (\x -> (x,((predsMap Map.! node)Map.! x)
                                        {symbolNameP = idN}))
          $ filter (\x -> (predsMap Map.! node)Map.! x `elem` 
             (map (\y -> ColimitPredSymbWithLabel
              {symbolNameP = id0, predSymbolLabel = y}) $ Set.toList set))
           $ Map.keys$ (Map.!) predsMap node) (predsMap Map.! node))) $ 
           Map.keys predsMap
      in updateMap predsMap2 id0 pairs
 in case predList of
  [] -> (rezList, predsMap1)
  (id0, set):preds -> case filter (\(x,_) -> x == id0) rezList of
     [] -> let  -- id hasn't occurred in the list yet
        rezList1 = rezList ++ [(id0, [set])]
        predsMap2 = updateMap predsMap1 id0 [(id0,set)]
       in finalPNames rezList1 preds predsMap2 sigmaRel phiSRel
     (_, setList):_ -> let
        predSet =  Set.fromList $ map arityP $ Set.toList set
        getPredTypes pSet = Set.fromList $ map arityP $ Set.toList pSet
        predSetList = map getPredTypes setList
        funSymbols = Set.union predSet $ foldl Set.union Set.empty predSetList
        sigmaId = sigmaRel{predMap = Map.fromList [(id0,funSymbols)]}
        leqPSets = Set.fromList $ map Set.fromList $ 
                   leqClasses (leqP sigmaId) funSymbols
       in if Set.member predSet leqPSets && 
             (not $ predSet `elem` predSetList)
          then let-- no additional overloading
           rezList1 = filter (\(x,_)->x /= id0) rezList ++ [(id0, set:setList)]
           predsMap2 = updateMap predsMap1 id0 [(id0,set)]
          in finalPNames rezList1 preds predsMap2 sigmaRel phiSRel
          else let 
     -- overloading, remove the sets which create conflicts and assign new names
           predSets1 = filter (\s -> Set.intersection predSet s /= Set.empty)$ 
                       Set.toList leqPSets
           cSets = filter (\s -> Set.intersection 
                                 (foldl Set.union Set.empty predSets1) 
                                 (Set.fromList $ map arityP $ Set.toList s)/= 
                                 Set.empty) setList
           setList1 = Set.difference (Set.fromList setList) (Set.fromList cSets)
           rezList1 = if setList1 /= Set.empty then
             filter (\(x,_) -> x /= id0) rezList ++ [(id0, Set.toList setList1)]
                      else filter (\(x,_) -> x /= id0) rezList
           genNewName set0 idN = if setList1 == Set.empty then idN 
                                      --try to keep old name
              else let
                nodeList = foldl (++) []$map originNodesP $ Set.toList set0
                nodeNr = head $ head $ sort $ group $ sort nodeList
               in appendNumber idN nodeNr
           generateNames oldId nameList csetsList = case csetsList of
              [] -> nameList
              set0:sets -> let
                 newId = genNewName set0 oldId
               in if newId `elem` nameList then let 
                  prefix name = isPrefixOf (show newId) (show name)
                  nr = length $ filter prefix nameList
                  newId1 = appendNumber newId nr
                 in generateNames oldId (nameList ++ [newId1]) sets
                else generateNames oldId (nameList ++ [newId]) sets
           preds2 = zip (generateNames id0 [] $ set:cSets) $ set:cSets
           predsMap2 = updateMap predsMap1 id0 preds2
         in finalPNames rezList1 (preds++preds2) predsMap2 sigmaRel phiSRel


-- this method assigns temporary names to operation symbols
-- by grouping symbols which have to be overloaded
-- and giving each group the name that is majoritary 
-- in the corresponding subgraph

tempPNames :: [ColimitPredSymbWithLabel]
         ->  Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel)
         ->  [(Id, Set.Set PredSymbolLabel)]
         ->  Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel)
         ->  ([(Id, Set.Set PredSymbolLabel)], 
             Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel))
tempPNames predsList morMap rezList morMap1 =  loopPGroups 
        (groupPreds predsList)  morMap rezList morMap1

groupPreds :: [ColimitPredSymbWithLabel] ->  [[ColimitPredSymbWithLabel]]
groupPreds predsList = let
  classFNames = map classLabelsListP $ map predSymbolLabel predsList
  nameFun = joinCls classFNames
  ovrl e1 e2 = (Map.!) nameFun (head $ classLabelsListP $ predSymbolLabel e1) ==
               (Map.!) nameFun (head $ classLabelsListP $ predSymbolLabel e2)
 in leqClasses ovrl $ Set.fromList predsList

loopPGroups :: [[ColimitPredSymbWithLabel]]
         ->  Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel)
         ->  [(Id, Set.Set PredSymbolLabel)]
         ->  Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel)
         ->  ([(Id, Set.Set PredSymbolLabel)], 
             Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel))
loopPGroups splitPreds  morMap rezList morMap1 = case splitPreds of
   [] -> (rezList, morMap1)
   predGrp:preds -> let
     nodeList = Map.keys morMap
     keys node = filter (isMappedTo predGrp morMap node) $ 
                 Map.keys $ (Map.!) morMap node
     eList = foldl (++) [] $ map keys nodeList
     idList = nub $ map fst eList
     sndCompDesc (_,x)(_, y) = case compare x y of
       LT -> GT
       EQ -> EQ
       GT -> LT
     idName = fst $ head $ sortBy sndCompDesc $ zip idList $ 
              map (\x -> length $ filter (\(y,_) -> y == x) eList ) idList
     predTypeSet = Set.fromList $ map predSymbolLabel predGrp
     fnode node = let
        predKeys = filter (\x -> x `elem` eList) $ 
                   Map.keys $ (Map.!) morMap node
        newVals = zip predKeys $ map (\x -> x{symbolNameP =idName}) $ 
                      map ((Map.!)((Map.!)morMap node)) predKeys
       in Map.union (Map.fromList newVals) ((Map.!) morMap1 node)
     morMap2 = Map.fromList $ zip (Map.keys morMap1) 
                             $ map fnode $ Map.keys morMap1
    in loopPGroups preds morMap ((idName, predTypeSet):rezList) morMap2

predSymbols :: Sign f e -> [(Id, PredType)]
predSymbols sigma =  foldl (++) [] $ 
 map (\(idX, predTSet) -> map (\y -> (idX, y)) $ Set.toList predTSet) $
  Map.toList $ predMap sigma

loopPredSets :: Gr (Sign f e)(Int, Morphism f e m)
           -> Map.Map Node (Map.Map (Id, PredType) String)
           -> Sign f e
           -> Map.Map Node (Morphism f e m)
           -> [PredType]
           -> [ColimitPredSymbWithLabel]
           -> Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel)
           -> ([ColimitPredSymbWithLabel],
               Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel))
loopPredSets graph clsFun sigmaRel phiSRel predSetsList predsList morMap =
 case predSetsList of
   [] -> (predsList, morMap)
   predSet:predSets -> let
      funSort = Map.fromList $ zip (nodes graph) 
                $ map sort_map $ map ((Map.!)phiSRel) $ nodes graph
      graph1 = buildPredGraphNodes graph (duplShape graph) funSort predSet $ 
               labNodes graph
      (setN, funN) = computeColimitSet graph1
      (predsList1, morMap1) = labelColimitElementsP funSort clsFun setN funN []
                          (Map.fromList $ zip (nodes graph) (repeat Map.empty))
      predsList2 = predsList ++ predsList1
      morMap2 = Map.fromList $ map (\n-> (n,Map.union (morMap1 Map.! n)
                                                   (morMap Map.! n))) $ 
                               nodes graph
    in loopPredSets graph clsFun sigmaRel phiSRel predSets predsList2 morMap2

samePredLabel :: Map.Map Node (Map.Map (Id,PredType) String) -> 
                ((Id,PredType),Node) -> 
                ((Id,PredType),Node) -> Bool
samePredLabel clsFun ((id1, pr1),n1)((id2,pr2),n2) = (id1 == id2) && 
   (clsFun Map.! n1) Map.! (id1,pr1) ==
   (clsFun Map.! n2) Map.! (id2,pr2)
  --(mapPredType ((Map.!)funSort n1) pr1 == mapPredType ((Map.!)funSort n2) pr2)

labelColimitElementsP :: Map.Map Node Sort_map
        -> Map.Map Node (Map.Map (Id, PredType) String)
        -> Set.Set ((Id,PredType), Node)
        -> Map.Map Node (Map.Map (Id, PredType) ((Id, PredType), Node))
        -> [ColimitPredSymbWithLabel]
        -> Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel)
        -> ([ColimitPredSymbWithLabel], 
            Map.Map Node (Map.Map (Id, PredType) ColimitPredSymbWithLabel))
labelColimitElementsP funSort clsFun setN funN resList resFun = let
  elemGroups = leqClasses (samePredLabel clsFun) setN
  mapGrp predResList rList rFun = let
    ((idH,predtypeH),nH) = head predResList
    nodeList = map snd predResList
    clsList = map (\((idX, ptX),nX) -> (Map.!)((Map.!)clsFun nX)(idX, ptX)) 
              predResList
    predTypeRes = mapPredType ((Map.!)funSort nH) predtypeH
    res = ColimitPredSymbWithLabel{symbolNameP = idH, 
            predSymbolLabel = PredSymbolLabel{
                arityP = predTypeRes,
                originNodesP = nodeList, 
                classLabelsListP =clsList}}
    rList1 = res : rList
    rFun1 = Map.fromList $ 
     map (\node -> (node, Map.union (Map.fromList$ map (\x -> (x,res)) $ 
     filter (isMappedTo predResList funN node)$ Map.keys $ (Map.!) funN node)
     ((Map.!)rFun node))) $ Map.keys funN
   in (rList1, rFun1)
  loopGroupList grpList rList rFun = case grpList of
     [] -> (rList, rFun)
     grp : grps -> let (rList1, rFun1) = mapGrp grp rList rFun
                    in loopGroupList grps rList1 rFun1
 in loopGroupList elemGroups resList resFun

buildPredGraphNodes :: Gr (Sign f e)(Int, Morphism f e m)
       -> Gr (Set.Set (Id, PredType))(Int,EndoMap (Id, PredType))
       -> Map.Map Node (Map.Map SORT SORT)
       -> PredType
       -> [(Node, Sign f e)]
       -> Gr (Set.Set (Id, PredType))(Int,EndoMap (Id, PredType))
buildPredGraphNodes graph graph0 funSort cls lNodeList = case lNodeList of
  [] -> buildPredGraphEdges graph0 (labEdges graph)
  (node, sigma):lnodes -> let
     clsName = getArityNameP cls
     arityList = preImageWord ((Map.!)funSort node) clsName
     predsWithArity sigma1 ar = filter (\x -> getPredArityName x == ar) $ 
                                predSymbols sigma1
     graph1 = changeNodeLabel graph0 node $ Set.fromList 
              $ foldl (++) [] $ map (predsWithArity sigma) arityList
    in buildPredGraphNodes graph graph1 funSort cls lnodes

buildPredGraphEdges :: Gr (Set.Set (Id, PredType))(Int,EndoMap (Id, PredType))
    -> [LEdge (Int, Morphism f e m)] -> 
    Gr (Set.Set (Id, PredType))(Int,EndoMap (Id, PredType))
buildPredGraphEdges graph0 edgeList = case edgeList of
  [] -> graph0
  (sn, tn, (nr, phi)):edgeL -> case lab graph0 sn of
     Nothing -> buildPredGraphEdges graph0 edgeL
     Just predSet -> buildPredGraphEdges 
         (changeEdgeLabel graph0 (sn, tn, (nr, Map.empty)) 
                      (nr, Map.fromList $ map (\x -> (x, applyMorP phi x)) 
          $ Set.toList predSet)) edgeL

getPredArityName :: (Id, PredType) -> [SORT]
getPredArityName (_, predtype) = predArgs predtype

getArityNameP :: PredType -> [SORT]
getArityNameP predtype = predArgs predtype

-- associative operations

assocSymbols :: Sign f e-> [(Id, OpType)]
assocSymbols sigma = foldl (++) [] $ 
   map (\(idX, opTSet) -> map (\y -> (idX, y)) $ Set.toList opTSet) $ 
   Map.toList $ assocOps sigma

colimitAssoc :: Gr (Sign f e) (Int,Morphism f e m) -> Sign f e -> 
   Map.Map Int (Morphism f e m) -> (Sign f e, Map.Map Int (Morphism f e m))
colimitAssoc graph sig morMap =  let
  assocOpList = nub $ foldl (++) [] $ 
    map (\(node, sigma) -> map (applyMor ((Map.!)morMap node)) $ 
    assocSymbols sigma ) $ labNodes graph
  idList = nub $ map fst assocOpList
  sig1 = sig{assocOps = Map.fromList $ 
   map (\sb -> (sb,Set.fromList $ map snd $ filter (\(i,_) -> i==sb) 
                                            assocOpList )) idList}
  morMap1 = Map.fromList $ map (\( node, phi) -> (node, phi{mtarget = sig1})) $
            Map.toList morMap
 in (sig1, morMap1)

