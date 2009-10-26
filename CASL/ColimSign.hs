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
based on
<http://www.informatik.uni-bremen.de/~till/papers/colimits.ps>

-}

module CASL.ColimSign(signColimit, extCASLColimit) where

import CASL.Sign
import CASL.Morphism
import CASL.Overload
import CASL.AS_Basic_CASL

import Common.Id
import Common.SetColimit
import Common.Utils (number)
import qualified Common.Lib.Rel as Rel
import Common.Lib.Graph

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

import Logic.Logic

extCASLColimit :: Gr () (Int, ()) ->
                  Map.Map Int CASLMor ->
                  ((),Map.Map Int ())
extCASLColimit graph _ = ((),Map.fromList $ zip (nodes graph) (repeat ()))

--central function for computing CASL signature colimits
signColimit :: (Category (Sign f e) (Morphism f e m)) =>
               Gr (Sign f e)(Int,Morphism f e m) ->
               ( Gr e (Int, m) ->
                 Map.Map Int (Morphism f e m)
                 -> (e, Map.Map Int m)
               )
               ->
               (Sign f e, Map.Map Int (Morphism f e m))
signColimit graph extColimit =
 case labNodes graph of
  [] -> error "empty graph"
  (n,sig):[] -> (sig, Map.fromAscList[(n, ide sig)])
  _ -> let
   getSortMap (x, phi) = (x,sort_map phi)
   sortGraph = emap getSortMap $ nmap sortSet graph
   (setSort0, funSort0) = computeColimitSet sortGraph
   (setSort, funSort) = addIntToSymbols (setSort0, funSort0)
   sigmaSort = (emptySign $ error "err"){sortSet=setSort}
   phiSort = Map.fromList
    $ map (\ (node, s)-> (node, (embedMorphism (error "err") s sigmaSort)
           {sort_map = Map.findWithDefault (error "sort_map") node funSort}))
    $ labNodes graph
   relS = computeSubsorts graph funSort
   sigmaRel = sigmaSort{sortRel = relS}
   phiRel = Map.map (\ phi -> phi{mtarget = sigmaRel}) phiSort
   (sigmaOp, phiOp) = computeColimitOp graph sigmaRel phiRel
   (sigmaPred, phiPred) = computeColimitPred graph sigmaOp phiOp
   (sigAssoc, phiAssoc) = colimitAssoc graph sigmaPred phiPred
   extGraph = emap (\(i, phi) -> (i, extended_map phi)) $
              nmap extendedInfo graph
   (extInfo, extMaps) = extColimit extGraph phiAssoc
   sigmaExt = sigAssoc{extendedInfo = extInfo}
   phiExt = Map.mapWithKey
     (\ node phi -> phi{mtarget = sigmaExt,
                       sort_map = Map.filterWithKey (/=) $ sort_map phi,
                       extended_map = Map.findWithDefault (error "ext_map")
                                         node extMaps})
     phiAssoc
   in (sigmaExt, phiExt)

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
    Just set -> let
                  f = Map.findWithDefault (error "subsorts") x colimF
                in subsorts xs graph rels colimF (Rel.transClosure $
             Rel.union rel (Rel.fromList [ (
                             Map.findWithDefault (error "f(m)") m f,
                             Map.findWithDefault (error "f(n)") n f
                                           )
              | m <- Set.elems set, n <- Set.elems set,
                Rel.member m n (Map.findWithDefault (error "rels(x)") x rels)]))

-- CASL signatures colimit on operation symbols

--algorithm description:
-- 1. project the graph on operation symbols
-- i.e. set of (Id, OpType)s in nodes and corresponding maps on edges
-- 2. compute colimit in Set of the graph => a set of ((Id, OpType), Node)
-- 3. build the overloading relation in colimit
--     two symbols are overloaded in the colimit
--     if there is some node and two opsymbols there
--     that are mapped in them and are overloaded
--    collect the names entering each symbol (try to keep names)
--    collect information about totality: a symbol must be total in the colimit
--    if we have a total symbol in the graph which is mapped to it
-- 4. assign names to each partition, in order of size
--    (i.e. the equivalence class with most symbols
--     will be prefered to keep name):
--    if there is available a name of a symbol entering the class,
--    then assign that name to the class, otherwise generate a name
--   also the morphisms have to be built

computeColimitOp :: Gr (Sign f e)(Int,Morphism f e m) ->
                    Sign f e -> Map.Map Node (Morphism f e m) ->
                    (Sign f e, Map.Map Node (Morphism f e m))
computeColimitOp graph sigmaRel phiSRel = let
 graph' = buildOpGraph graph
 (colim, morMap') = computeColimitSet graph'
 (ovrl, names, totalOps) = buildColimOvrl graph graph' colim morMap'
 (colim1, morMap1) = nameSymbols graph' morMap' phiSRel names ovrl totalOps
 morMap2 = Map.map (\f -> Map.map (\((i,o),_) -> (i, opKind o)) f) morMap1
 morMap3 = Map.map (\f -> Map.fromAscList $
                          map (\((i,o),y) -> ((i,o{opKind = Partial}), y)) $
                          Map.toList f) morMap2
 sigmaOps = sigmaRel{opMap = colim1}
 phiOps = Map.mapWithKey
          (\n phi -> phi{op_map =
                         Map.findWithDefault (error "op_map") n morMap3})
          phiSRel
 in (sigmaOps, phiOps)

buildOpGraph :: Gr (Sign f e) (Int, Morphism f e m) ->
                Gr (Set.Set (Id, OpType))
                   (Int, Map.Map (Id, OpType) (Id, OpType))
buildOpGraph graph = let
  getOps sign = foldl
                 (\s (i, opset) ->
                     Set.union s $ Set.map (\x -> (i, x)) opset)
                 Set.empty $ Map.toList $ opMap sign
  getOpFun mor = let
                  ssign = msource mor
                  smap = sort_map mor
                  omap = op_map mor
                 in foldl (\f x -> let y = mapOpSym smap omap x
                                  in if x == y then f else Map.insert x y f)
                  Map.empty $ Set.toList $ getOps ssign
 in nmap getOps $ emap (\ (i, m) -> (i,getOpFun m)) graph

buildColimOvrl :: Gr (Sign f e) (Int, Morphism f e m) ->
                  Gr (Set.Set (Id, OpType))(Int, EndoMap (Id, OpType)) ->
                  Set.Set ((Id, OpType), Int) ->
                  Map.Map Int (Map.Map (Id, OpType) ((Id, OpType), Int)) ->
                  (Rel.Rel ((Id, OpType), Int),
                   Map.Map ((Id, OpType), Int)
                           (Map.Map Id Int),
                   Map.Map ((Id, OpType), Int) Bool)
buildColimOvrl graph graph' colim morMap = let
   (ovrl, names) = (Rel.empty, Map.fromList $ zip (Set.toList colim) $
                                                  repeat Map.empty )
   (ovrl', names', totalF') =  buildOvrlAtNode graph' colim morMap
                      ovrl names Map.empty $ labNodes graph
  in (Rel.transClosure ovrl', names', totalF')

buildOvrlAtNode :: Gr (Set.Set (Id, OpType))(Int, EndoMap (Id, OpType)) ->
                   Set.Set ((Id, OpType), Int) ->
                   Map.Map Int (Map.Map (Id, OpType) ((Id, OpType), Int)) ->
                   Rel.Rel ((Id, OpType), Int) ->
                   Map.Map ((Id, OpType), Int) (Map.Map Id Int) ->
                   Map.Map ((Id, OpType), Int) Bool ->
                   [(Int, Sign f e)] ->
                   (Rel.Rel ((Id, OpType), Int),
                   Map.Map ((Id, OpType), Int)(Map.Map Id Int),
                   Map.Map ((Id, OpType), Int) Bool )
buildOvrlAtNode graph' colim morMap ovrl names totalF nodeList =
 case nodeList of
   [] -> (ovrl, names, totalF)
   (n, sig):lists -> let
       Just oSet = lab graph' n
       names' = foldl (\g x@(idN,_) -> let
                                 y = Map.findWithDefault (x,n) x $
                                     Map.findWithDefault (error $ show n)
                                         n morMap
                                 altF v = case v of
                                      Nothing -> Just 1
                                      Just m -> Just $ m+1
                                in Map.adjust (\gy -> Map.alter altF idN gy)
                                   y g)
                       names $ Set.toList oSet
       equivF (id1, ot1) (id2, ot2) = (id1 == id2) && leqF sig ot1 ot2
       parts = leqClasses equivF oSet
       addParts rel equivList =
         foldl (\(r, f) l -> let l1 = map (\x -> Map.findWithDefault (x,n) x $
                                            Map.findWithDefault
                                              (error "morMap(n)") n morMap) l
                        in case l1 of
                   [] -> error "addParts"
                   x:xs -> let
                             (r', ly) = foldl
                              (\(rl,lx) y -> (Rel.insert lx y rl, y))
                              (r,x) xs
                             f' = foldl (\g ((_i,o),((i',o'),n')) ->
                                   if opKind o == Total then
                                    Map.insert ((i',o'{opKind=Partial}), n')
                                               True g
                                    else g ) f $ zip l l1
                            in (Rel.insert ly x r', f')
                          )
               (rel, totalF) equivList
       (ovrl', totalF') = addParts ovrl parts
     in buildOvrlAtNode graph' colim morMap ovrl' names' totalF' lists

assignName :: (Set.Set ((Id, OpType), Int), Int) -> [Id] ->
              Map.Map ((Id, OpType), Int) (Map.Map Id Int) ->
              (Id, [Id])
assignName (opSet,idx) givenNames namesFun =
 let opSetNames = Set.fold (\x f -> Map.unionWith (\a b -> a + b) f
                                                 ( Map.findWithDefault
                                                    (error "namesFun") x
                                                     namesFun))
                           Map.empty opSet
     availNames = filter (\x -> not $ x `elem` givenNames) $
                  Map.keys opSetNames
 in case availNames of
     [] -> let
       -- must generate name with the most frequent name idx and an origin
        sndOrd x y= compare
                      (Map.findWithDefault (error "assignName") x opSetNames)
                      (Map.findWithDefault (error "assignName") y opSetNames)
        avail' = sortBy sndOrd $ Map.keys opSetNames
        idN = head avail'
       in (appendNumber idN idx, givenNames)
     _ -> -- must take the most frequent available name and give it to the class
          -- and this name becomes given
          let
         sndOrd x y = compare
                       (Map.findWithDefault (error "assignName") x opSetNames)
                       (Map.findWithDefault (error "assignName") y opSetNames)
         avail' = sortBy sndOrd availNames
         idN = head $ reverse avail'
        in (idN, idN:givenNames)

nameSymbols :: Gr (Set.Set (Id, OpType))
                   (Int, Map.Map (Id,OpType)(Id, OpType)) ->
               Map.Map Int (Map.Map (Id, OpType) ((Id, OpType), Int)) ->
               Map.Map Int (Morphism f e m) ->
               Map.Map ((Id, OpType), Int) (Map.Map Id Int) ->
               Rel.Rel ((Id, OpType), Int) ->
               Map.Map ((Id, OpType), Int) Bool ->
               (Map.Map Id (Set.Set OpType),
                Map.Map Int (Map.Map (Id, OpType) ((Id, OpType),Int)))
nameSymbols graph morMap phi names ovrl totalOps = let
  colimOvrl = Rel.sccOfClosure $ ovrl
  nameClass opFun gNames (set, idx) morFun = let
    (newName, gNames') = assignName (set, idx) gNames names
    opTypes = Set.map (\((oldId,ot),i) -> let
                 oKind' = if Map.findWithDefault False
                             ((oldId,ot{opKind = Partial}), i)
                             totalOps
                           then Total else Partial
                 imor = Map.findWithDefault (error "imor") i phi
                in mapOpType (sort_map imor) ot{opKind = oKind'}) $
              set
    renameSymbols n f = let
        Just opSyms = lab graph n
        setKeys = filter (\x -> let y = Map.findWithDefault (x, n) x f
                                in Set.member y set) $ Set.toList opSyms
        updateAtKey (i,o) ((i', o'), n') = let
          nmor = Map.findWithDefault (error "nmor") n phi
          o'' = mapOpType (sort_map nmor) o'
          oKind = if Map.findWithDefault False
                             ((i',o'{opKind = Partial}), n')
                             totalOps
                           then Total else Partial
          z = (newName, o''{opKind = oKind})
         in if (i,o) == z then
               Nothing
                          else
               Just (z,n')
       in foldl (\g x -> Map.update (updateAtKey x) x g)
                 f setKeys
-- -- i have to map symbols entering set
-- -- to (newName, their otype mapped)
    morFun' = Map.mapWithKey renameSymbols morFun
   in (Map.insert newName opTypes opFun, gNames', morFun')
  colimOvrl' = reverse $
               sortBy (\ s1 s2 -> compare (Set.size s1)(Set.size s2)) colimOvrl
  (opFuns, _, renMap) = foldl (\(oF,gN, mM) x -> nameClass oF gN x mM)
                                  (Map.empty,[], morMap)
                                  $ number colimOvrl'
 in (opFuns , renMap)

{--CASL signatures colimit on predicate symbols
almost identical with operation symbols,
only minor changes because of different types
--}

computeColimitPred :: Gr (Sign f e)(Int,Morphism f e m) -> Sign f e ->
      Map.Map Node (Morphism f e m) -> (Sign f e, Map.Map Node (Morphism f e m))
computeColimitPred graph sigmaOp phiOp = let
  graph' = buildPredGraph graph
  (colim, morMap') = computeColimitSet graph'
  (ovrl, names) = buildPColimOvrl graph graph' colim morMap'
  (colim1, morMap1) = namePSymbols graph' morMap' phiOp names ovrl
  morMap2 = Map.map (\f -> Map.map (\((i,_p),_) -> i) f) morMap1
  sigmaPreds = sigmaOp{predMap = colim1}
  phiPreds = Map.mapWithKey
          (\n phi -> phi{pred_map =
                         Map.findWithDefault (error "pred_map") n morMap2})
          phiOp
 in (sigmaPreds, phiPreds)

buildPredGraph :: Gr (Sign f e) (Int, Morphism f e m) ->
                Gr (Set.Set (Id, PredType))
                   (Int, Map.Map (Id, PredType) (Id, PredType))
buildPredGraph graph = let
  getPreds sign = foldl
                 (\s (i, pset) ->
                     Set.union s $ Set.map (\x -> (i, x)) pset)
                 Set.empty $ Map.toList $ predMap sign
  getPredFun mor = let
                  ssign = msource mor
                  smap = sort_map mor
                  pmap = pred_map mor
                 in foldl (\f x -> let y = mapPredSym smap pmap x
                                  in if x == y then f else Map.insert x y f)
                  Map.empty $ Set.toList $ getPreds ssign
 in nmap getPreds $ emap (\ (i, m) -> (i,getPredFun m)) graph


buildPColimOvrl :: Gr (Sign f e) (Int, Morphism f e m) ->
                  Gr (Set.Set (Id, PredType))(Int, EndoMap (Id, PredType)) ->
                  Set.Set ((Id, PredType), Int) ->
                  Map.Map Int (Map.Map (Id, PredType) ((Id, PredType), Int)) ->
                  (Rel.Rel ((Id, PredType), Int),
                   Map.Map ((Id, PredType), Int) (Map.Map Id Int))
buildPColimOvrl graph graph' colim morMap = let
   (ovrl, names) = (Rel.empty, Map.fromList $ zip (Set.toList colim) $
                                                  repeat Map.empty )
   (ovrl', names') =  buildPOvrlAtNode graph' colim morMap
                      ovrl names $ labNodes graph
  in (Rel.transClosure ovrl', names')

buildPOvrlAtNode :: Gr (Set.Set (Id, PredType))(Int, EndoMap (Id, PredType)) ->
                   Set.Set ((Id, PredType), Int) ->
                   Map.Map Int (Map.Map (Id, PredType) ((Id, PredType), Int)) ->
                   Rel.Rel ((Id, PredType), Int) ->
                   Map.Map ((Id, PredType), Int) (Map.Map Id Int) ->
                   [(Int, Sign f e)] ->
                   (Rel.Rel ((Id, PredType), Int),
                   Map.Map ((Id, PredType), Int)(Map.Map Id Int))
buildPOvrlAtNode graph' colim morMap ovrl names nodeList =
 case nodeList of
   [] -> (ovrl, names)
   (n, sig):lists -> let
       Just pSet = lab graph' n
       names' = foldl (\g x@(idN,_) -> let
                                 y = Map.findWithDefault (x,n) x $
                                     Map.findWithDefault (error $ show n)
                                         n morMap
                                 altF v = case v of
                                      Nothing -> Just 1
                                      Just m -> Just $ m+1
                                in Map.adjust (\gy -> Map.alter altF idN gy)
                                   y g)
                       names $ Set.toList pSet
       equivP (id1, pt1) (id2, pt2) = (id1 == id2) && leqP sig pt1 pt2
       parts = leqClasses equivP pSet
       nmor = Map.findWithDefault (error "buildAtNode") n morMap
       addParts rel equivList =
         foldl (\r l -> let l1 = map (\x ->
                                  Map.findWithDefault (x,n) x nmor) l
                        in case l1 of
                   [] -> error "addParts"
                   x:xs -> let
                             (r', ly) = foldl
                              (\(rl,lx) y -> (Rel.insert lx y rl, y))
                              (r,x) xs
                            in Rel.insert ly x r'
                          )
               rel equivList
       ovrl' = addParts ovrl parts
     in buildPOvrlAtNode graph' colim morMap ovrl' names' lists

assignPName :: (Set.Set ((Id, PredType), Int), Int) -> [Id] ->
              Map.Map ((Id, PredType), Int) (Map.Map Id Int) ->
              (Id, [Id])
assignPName (pSet,idx) givenNames namesFun =
 let pSetNames = Set.fold (\x f -> Map.unionWith (\a b -> a + b) f
                            (Map.findWithDefault (error "pname") x namesFun))
                           Map.empty pSet
     availNames = filter (\x -> not $ x `elem` givenNames) $
                  Map.keys pSetNames
 in case availNames of
     [] -> let
       -- must generate name with the most frequent name idx and an origin
        sndOrd x y= compare (pSetNames Map.! x) (pSetNames Map.! y)
        avail' = sortBy sndOrd $ Map.keys pSetNames
        idN = head avail'
       in (appendNumber idN idx, givenNames)
     _ -> -- must take the most frequent available name and give it to the class
          -- and this name becomes given
          let
         sndOrd x y= compare (pSetNames Map.! x) (pSetNames Map.! y)
         avail' = sortBy sndOrd availNames
         idN = head $ reverse avail'
        in (idN, idN:givenNames)

namePSymbols :: Gr (Set.Set (Id, PredType))
                   (Int, Map.Map (Id,PredType)(Id, PredType)) ->
               Map.Map Int (Map.Map (Id, PredType) ((Id, PredType), Int)) ->
               Map.Map Int (Morphism f e m) ->
               Map.Map ((Id, PredType), Int) (Map.Map Id Int) ->
               Rel.Rel ((Id, PredType), Int) ->
               (Map.Map Id (Set.Set PredType),
                Map.Map Int (Map.Map (Id, PredType) ((Id, PredType),Int)))
namePSymbols graph morMap phi names ovrl = let
  colimOvrl = Rel.sccOfClosure $ ovrl
  nameClass pFun gNames (set, idx) morFun = let
    (newName, gNames') = assignPName (set, idx) gNames names
    pTypes = Set.map (\((_oldId,pt), i) -> let
                in mapPredType (sort_map $ phi Map.! i) pt) $
              set
    renameSymbols n f = let
        Just pSyms = lab graph n
        setKeys = filter (\x -> let y = Map.findWithDefault (x, n) x f
                                in Set.member y set) $ Set.toList pSyms
        updateAtKey (i,p) ((_i', p'), n') = let
          p'' = mapPredType (sort_map $ phi Map.! n) p'
          z = (newName, p'')
         in if (i,p) == z then
               Nothing
                          else
               Just (z,n')
       in foldl (\g x -> Map.update (updateAtKey x) x g)
                 f setKeys
-- -- i have to map symbols entering set
-- -- to (newName, their predtype mapped)
    morFun' = Map.mapWithKey renameSymbols morFun
   in (Map.insert newName pTypes pFun, gNames', morFun')
  colimOvrl' = reverse $
               sortBy (\ s1 s2 -> compare (Set.size s1)(Set.size s2)) colimOvrl
  (pFuns, _, renMap) = foldl (\(pF,gN, mM) x -> nameClass pF gN x mM)
                                  (Map.empty,[], morMap)
                                  $ number colimOvrl'
 in (pFuns , renMap)

opSymbolsOf :: OpMap -> [(Id, OpType)]
-- returns the list of all operation symbols in a signature,
-- as pairs (Id,OpType)
opSymbolsOf = concatMap
  (\ (idX, opTSet) -> map (\y -> (idX, y)) $ Set.toList opTSet)
  . Map.toList

applyMor :: Morphism f e m -> (Id, OpType) -> (Id, OpType)
applyMor phi (i, optype) = mapOpSym (sort_map phi) (op_map phi) (i, optype)

-- associative operations

assocSymbols :: Sign f e -> [(Id, OpType)]
assocSymbols = opSymbolsOf . assocOps

colimitAssoc :: Gr (Sign f e) (Int,Morphism f e m) -> Sign f e ->
   Map.Map Int (Morphism f e m) -> (Sign f e, Map.Map Int (Morphism f e m))
colimitAssoc graph sig morMap = let
  assocOpList = nub $ concatMap
    (\ (node, sigma) -> map (applyMor ((Map.!)morMap node)) $
    assocSymbols sigma ) $ labNodes graph
  idList = nub $ map fst assocOpList
  sig1 = sig{assocOps = Map.fromList $
   map (\sb -> (sb,Set.fromList $ map snd $ filter (\(i,_) -> i==sb)
                                            assocOpList )) idList}
  morMap1 = Map.map (\ phi -> phi{mtarget = sig1}) morMap
 in (sig1, morMap1)
