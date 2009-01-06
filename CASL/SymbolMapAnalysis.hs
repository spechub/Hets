{- |
Module      :  $Header$
Description :  symbol map analysis for the CASL logic.
Copyright   :  (c) Till Mossakowski, C. Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Symbol map analysis for the CASL logic.
  Follows Sect. III:4.1 of the CASL Reference Manual.
-}

module CASL.SymbolMapAnalysis
    ( inducedFromMorphism
    , inducedFromToMorphism
    , cogeneratedSign
    , generatedSign
    , finalUnion
    )  where

import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Overload (leqF, leqP)

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.Id
import Common.Result

import Data.List (partition, find)
import Data.Maybe (catMaybes)

{-
inducedFromMorphism :: RawSymbolMap -> sign -> Result morphism

Here is Bartek Klin's algorithm that has benn used for CATS.
Our algorithm deviates from it. The exact details need to be checked.

Inducing morphism from raw symbol map and signature

Input:  raw symbol map "Rsm"
        signature "Sigma1"
Output: morphims "Mrph": Sigma1 -> "Sigma2".

//preparation
1. let "Ssm" be an empty list of pairs (symbol, raw symbol).
2. for each pair "Rsym1,Rsym2" in Rsm do:
        2.1. if there is no symbol in Sigma1 matching Rsym1, return error.
        2.2. for each symbol "Sym" from Sigma1 matching Rsym1
                2.2.1. add a pair "Sym,Rsym2" to Ssm.
//computing the "sort part" of the morphism
3. let Sigma2 be an empty signature.
4. let Mrph be an empty "morphism" from Sigma1 to Sigma2.
5. for each pair "Sym,Rsym2" in Ssm such that Sym is a sort symbol
        5.1. if Rsym2 is not a sort raw symbol, return error.
        5.2. if in Mrph there is a mapping of sort in Sym to sort with
                name other than that in Rsym2, return error.
        5.3. if in Mrph there is no mappinh of sort in Sym
                5.3.1. add sort from Rsym2 to Sigma2
                5.3.2. add mapping from sort(Sym) to sort(Rsym2) to Mrph.
6. for each sort symbol "S" in Sigma1
        6.1. if S is not mapped by Mrph,
                6.1.1. add sort S to Sigma2
                6.1.2. add mapping from S to S to Mrph.
//computing the "function/predicate part" of the morphism
7. for each pair "Sym,Rsym2" in Ssm such that Sym is a function/predicate
   symbol
        7.1. let "F" be name contained in Sym, let "Fprof" be the profile.
        7.2. let "Fprof1" be the value of Fprof via Mrph
                (it can be computed, as we already have the "sort" part of
                 morphism)
        7.3. if Rsym2 is not of appriopriate type, return error, otherwise
             let "F2" be the name of the symbol.
        7.4. if Rsym2 enforces the profile of the symbol (i.e., it is not
             an implicit symbol), compare the profile to Fprof1. If it is
             not equal, return error.
        7.5. if in Mrph there is a mapping of F1 with profile Fprof to
             some name different than F2, return error.
        7.6. add an operation/predicate with name F2 and profile Fprof1 to
             Sigma2. If it is a partial function and if in Sigma2 there
             exists a total function with the same name and profile, do not
             add it. Otherwise if it is a total function and if in Sigma2
             there exists a partial function with the same name and profile,
             add the total function removing the partial one.
        7.7. add to Mrph a mapping from operation/predicate of name F1 and
             profile Fprof to name F2.
8. for each operation/predicate symbol "F" with profile "Fprof" in Sigma1
   that is not mapped by Mrph,
        8.1. as in 7.2
        8.2. as in 7.6, replacing F2 with F1.
        8.3. as in 7.7, replacing F2 with F1.
9. for each sort relation "S1,S2" in Sigma1,
        9.1. compute S3=(S1 via Mrph) and S4=(S2 via Mrph)
        9.2. add sort relation "S3,S4" in Sigma2.
10. Compute transitive closure of subsorting relation in Sigma2.
-}

inducedFromMorphism :: (Pretty e, Pretty f) => m -> (e -> e -> Bool)
                    -> RawSymbolMap -> Sign f e -> Result (Morphism f e m)
inducedFromMorphism extEm _isSubExt rmap sigma = do
  -- ??? Missing: check preservation of overloading relation
  -- first check: do all source raw symbols match with source signature?
  let syms = Set.toList $ symOf sigma
      sortsSigma = sortSet sigma
      incorrectRsyms = Map.foldWithKey
        (\ rsy _ -> if any (matchesND rsy) syms
                    then id
                    else Set.insert rsy)
        Set.empty
        rmap
      matchesND rsy sy =
        sy `matches` rsy &&
        case rsy of
          ASymbol _ -> True
          -- unqualified raw symbols need some matching symbol
          -- that is not directly mapped
          _ -> Map.lookup (ASymbol sy) rmap == Nothing
  -- ... if not, generate an error
  if Set.null incorrectRsyms then return () else fatal_error
       ("the following symbols: "
        ++ showDoc incorrectRsyms
        "\nare already mapped directly or do not match with signature\n"
        ++ showDoc sigma "")
       $ getRange incorrectRsyms

  -- compute the sort map (as a Map)
  sort_Map <- Set.fold (\ s m -> do
                s' <- sortFun rmap s
                m1 <- m
                return $ if s' == s then m1 else Map.insert s s' m1)
              (return Map.empty) sortsSigma
  -- compute the op map (as a Map)
  op_Map <- Map.foldWithKey (opFun rmap sort_Map)
              (return Map.empty) (opMap sigma)
  -- compute the pred map (as a Map)
  pred_Map <- Map.foldWithKey (predFun rmap sort_Map)
              (return Map.empty) (predMap sigma)
  -- compute target signature
  let smap = mapSort sort_Map
      omap = mapOps sort_Map op_Map
      sigma' =
        sigma
            {sortSet = Set.map smap sortsSigma,
             emptySortSet = Set.map smap $ emptySortSet sigma,
             sortRel = Rel.irreflex $ Rel.transClosure $
                         Rel.map smap (sortRel sigma),
             opMap = Map.foldWithKey omap Map.empty (opMap sigma),
             assocOps = Map.foldWithKey omap Map.empty (assocOps sigma),
             predMap = Map.foldWithKey (mapPreds sort_Map pred_Map)
                       Map.empty (predMap sigma),
             varMap = Map.empty}
  -- return assembled morphism
  return (embedMorphism extEm sigma sigma')
    { sort_map = sort_Map
    , op_map = op_Map
    , pred_map = pred_Map }

  -- the sorts of the source signature
  -- sortFun is the sort map as a Haskell function
sortFun :: RawSymbolMap -> Id -> Result Id
sortFun rmap s =
    -- rsys contains the raw symbols to which s is mapped to
    if Set.null rsys then return s -- use default = identity mapping
    else if Set.null $ Set.deleteMin rsys then
          return $ rawSymName $ Set.findMin rsys -- take the unique rsy
          else plain_error s  -- ambiguity! generate an error
                 ("Sort " ++ showId s
                  " is mapped ambiguously: "  ++ showDoc rsys "")
                 $ getRange rsys
    where
    -- get all raw symbols to which s is mapped to
    rsys = Set.fromList $ catMaybes $ map (flip Map.lookup rmap)
               [ ASymbol $ idToSortSymbol s
               , AKindedSymb Implicit s
               , AKindedSymb Sorts_kind s ]

  {- to a Op_map, add everything resulting from mapping (id, ots)
  according to rmap -}
opFun :: RawSymbolMap -> Sort_map -> Id -> Set.Set OpType
      -> Result Op_map -> Result Op_map
opFun rmap sort_Map ide ots m =
    -- first consider all directly mapped profiles
    let (ots1,m1) = Set.fold (directOpMap rmap sort_Map ide) (Set.empty,m) ots
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedSymb Ops_kind ide) rmap,
                Map.lookup (AKindedSymb Implicit ide) rmap) of
       (Just rsy1, Just rsy2) ->
          do m' <- m
             plain_error m'
               ("Operation " ++ showId ide
                " is mapped twice: "
                ++ showDoc (rsy1, rsy2) "")
               $ appRange (getRange rsy1) $ getRange rsy2
       (Just rsy, Nothing) ->
          Set.fold (insertmapOpSym sort_Map ide rsy) m1 ots1
       (Nothing, Just rsy) ->
          Set.fold (insertmapOpSym sort_Map ide rsy) m1 ots1
       -- Anything not mapped explicitly is left unchanged
       (Nothing,Nothing) -> m1

    -- try to map an operation symbol directly
    -- collect all opTypes that cannot be mapped directly
directOpMap :: RawSymbolMap -> Sort_map -> Id -> OpType
            -> (Set.Set OpType, Result Op_map)
            -> (Set.Set OpType, Result Op_map)
directOpMap rmap sort_Map ide' ot (ots',m') =
  case lookupOpSymbol rmap ide' ot of
    Just rsy -> (ots', insertmapOpSym sort_Map ide' rsy ot m')
    Nothing -> (Set.insert ot ots', m')

lookupOpSymbol :: RawSymbolMap -> Id -> OpType -> Maybe RawSymbol
lookupOpSymbol rmap ide' ot = let mkS = idToOpSymbol ide' in
  case Map.lookup (ASymbol (mkS $ mkPartial ot)) rmap of
    Nothing -> Map.lookup
      (ASymbol (mkS $ mkTotal ot)) rmap
    res -> res

    -- map op symbol (ide,ot) to raw symbol rsy
mappedOpSym :: Sort_map -> Id -> OpType -> RawSymbol -> Result (Id, OpKind)
mappedOpSym sort_Map ide ot rsy =
    let opSym = "Operation symbol " ++ showDoc (idToOpSymbol ide ot)
                " is mapped to "
        kind = opKind ot
    in case rsy of
      ASymbol (Symbol ide' (OpAsItemType ot')) ->
        if compatibleOpTypes (mapOpType sort_Map ot) ot'
           then return (ide', opKind ot')
           else plain_error (ide, kind)
             (opSym ++ "type " ++ showDoc ot'
              " but should be mapped to type " ++
              showDoc (mapOpType sort_Map ot)"") $ getRange rsy
      AKindedSymb k ide' | elem k [Implicit, Ops_kind] -> return (ide', kind)
      _ -> plain_error (ide, kind)
               (opSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

    -- insert mapping of op symbol (ide,ot) to raw symbol rsy into m
insertmapOpSym :: Sort_map -> Id -> RawSymbol -> OpType
               -> Result Op_map -> Result Op_map
insertmapOpSym sort_Map ide rsy ot m = do
      m1 <- m
      (ide', kind') <- mappedOpSym sort_Map ide ot rsy
      return $ if ide == ide' && kind' == opKind ot then m1 else
                   Map.insert (ide, mkPartial ot) (ide', kind') m1
    -- insert mapping of op symbol (ide, ot) to itself into m

-- map the ops in the source signature
mapOps :: Sort_map -> Op_map -> Id -> Set.Set OpType -> OpMap -> OpMap
mapOps sort_Map op_Map ide ots m =
    Set.fold mapOp m ots
    where
    mapOp ot m1 =
      let (ide',ot') = mapOpSym sort_Map op_Map (ide,ot)
      in Rel.setInsert ide' ot' m1

  {- to a Pred_map, add evering resulting from mapping (ide,pts)
  according to rmap -}

predFun :: RawSymbolMap -> Sort_map -> Id -> Set.Set PredType
               -> Result Pred_map -> Result Pred_map
predFun rmap sort_Map ide pts m =
    -- first consider all directly mapped profiles
    let (pts1,m1) = Set.fold (directPredMap rmap sort_Map ide)
                    (Set.empty,m) pts
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedSymb Preds_kind ide) rmap,
                Map.lookup (AKindedSymb Implicit ide) rmap) of
       (Just rsy1, Just rsy2) ->
          do m' <- m
             plain_error m'
               ("Predicate " ++ showId ide
                " is mapped twice: " ++
                showDoc (rsy1, rsy2) "")
               $ appRange (getRange rsy1) $ getRange rsy2
       (Just rsy, Nothing) ->
          Set.fold (insertmapPredSym sort_Map ide rsy) m1 pts1
       (Nothing, Just rsy) ->
          Set.fold (insertmapPredSym sort_Map ide rsy) m1 pts1
       -- Anything not mapped explicitly is left unchanged
       (Nothing,Nothing) -> m1

    -- try to map a predicate symbol directly
    -- collect all predTypes that cannot be mapped directly
directPredMap :: RawSymbolMap -> Sort_map -> Id -> PredType
              -> (Set.Set PredType, Result Pred_map)
              -> (Set.Set PredType, Result Pred_map)
directPredMap rmap sort_Map ide pt (pts,m) =
      case Map.lookup (ASymbol (idToPredSymbol ide pt)) rmap of
        Just rsy ->
          (pts,insertmapPredSym sort_Map ide rsy pt m)
        Nothing -> (Set.insert pt pts,m)

    -- map pred symbol (ide,pt) to raw symbol rsy
mappedPredSym :: Sort_map -> Id -> PredType -> RawSymbol -> Result Id
mappedPredSym sort_Map ide pt rsy =
    let predSym = "Predicate symbol " ++ showDoc (idToPredSymbol ide pt)
                  " is mapped to "
    in case rsy of
      ASymbol (Symbol ide' (PredAsItemType pt')) ->
        if mapPredType sort_Map pt == pt'
           then return ide'
           else plain_error ide
             (predSym ++ "type " ++ showDoc pt'
              " but should be mapped to type " ++
              showDoc (mapPredType sort_Map pt) "") $ getRange rsy
      AKindedSymb k ide' | elem k [Implicit, Preds_kind] -> return ide'
      _ -> plain_error ide
               (predSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

    -- insert mapping of pred symbol (ide,pt) to raw symbol rsy into m
insertmapPredSym :: Sort_map -> Id -> RawSymbol -> PredType
                 -> Result Pred_map -> Result Pred_map
insertmapPredSym sort_Map ide rsy pt m = do
      m1 <- m
      ide' <- mappedPredSym sort_Map ide pt rsy
      return $ if ide' == ide then m1 else Map.insert (ide, pt) ide' m1
    -- insert mapping of pred symbol (ide,pt) to itself into m

  -- map the preds in the source signature
mapPreds :: Sort_map -> Pred_map -> Id -> Set.Set PredType
         -> Map.Map Id (Set.Set PredType) -> Map.Map Id (Set.Set PredType)
mapPreds sort_Map pred_Map ide pts m =
    Set.fold mapPred m pts
    where
    mapPred pt m1 =
      let (ide',pt') = mapPredSym sort_Map pred_Map (ide,pt)
      in Rel.setInsert ide' pt' m1

{-
inducedFromToMorphism :: RawSymbolMap -> sign -> sign -> Result morphism

Algorithm adapted from Bartek Klin's algorithm for CATS.

Inducing morphisms from raw symbol map and source and target signature.

This problem is NP-hard (The problem of 3-colouring can be reduced to it).
This means that we have exponential runtime in the worst case.
However, in many cases the runtime can be kept rather short by
using some basic principles of constraint programming.
We use a depth-first search with some weak form of constraint
propagation and MRV (minimum remaining values), see
Stuart Russell and Peter Norvig:
Artificial Intelligence - A Modern Approach.
Prentice Hall International
The algorithm has additionally to take care of default values (i.e.
symbol names are mapped identically be default, and the number of
identitically mapped names should be maximized). Moreover, it does
not suffice to find just one solution, but also its uniqueness
(among those maximizing he number of identitically mapped names)
must be checked (still, MRV is useful here).

The algorithm

Input:  raw symbol map "rmap"
        signatures "sigma1,sigma2"
Output: morphism "mor": sigma1 -> sigma2

1. compute the morphism mor1 induced by rmap and sigma1 (i.e. the renaming)
1.1. if target mor1 is a subsignature of sigma2, return the composition
     of this inclusion with mor1
     (cf. Theorem 6 of Bartek Klin's Master's Thesis)
2. let "posmap" be a map, mapping each symbol "sym1" from sigma1 to a pair
   of sets of symbols (symset1, symset2) from sigma2 such that sym1
   can be mapped to each sym2 in symset1 union symset2 (i.e., they are
   both sorts or operations/predicates of the same arity, and
   moreover, if there is a pair (rsym1,rsym2) in rmap such that sym1
   matches rsym1, then rsym2 must match rsym2). Moreover, symset1
   contains only symbols with names equal to that of sym1,
   whereas symset2 contains only symbols with names different from
   that of sym1.
3. let "akmap" (from Actually Known Map) be an empty symbol map.
//DEPTH-FIRST MRV SEARCH
//recursively called procedure, returning a symbol map or a special
//"No_map" value. Parameters are: sigma1, sigma2, akmap, posmap.
GET MRV (minimun remaining values) "VARIABLE"
4a. if posmap is empty
        4a.1. check if akmap defines a mapping from every symbol in
              source mor1.  (this should be vacuously true - Bartek?)
        4a.2. if yes, return akmap, otherwise return "No_map".
4b. take a pair sym1 |-> (symset1,symset2) with MRV from posmap
   (i.e. one with minimal cardinality of symset1 union symset2).
   But: prefer those with non-empty symset1!
   Remove it from posmap.
   (For efficiency reasons, we also carry around an indexing of posmap
   according to the cardinalities. Hence, posmap really is a pair
   (posmap1,posmap2).)
5. for each symbol "sym2" from symset1
        CONSISTENCY CHECK
        5.1. check if mapping sym1 to sym2 clashes with akmap
                (it can clash if sym1 and sym2 are operations/predicates,
                 and mapping on their profiles clashes with what is already
                 known in akmap)
        5.2. if yes, proceed with the next sym2 in step 5.
        5.3. add mapping of sym1 to sym2 to akmap.
        CONSTRAINT PROPAGATION (forward checking)
        5.4. if sym1 and sym2 are sorts
             5.5. for each sub/supersort s of sym1, restrict the possible
                  mappings of s in posmap to sub/supersorts of sym2
             5.6. for each operation/predicate f in dom(posmap) involving
                  sym1 in its argument or result sorts, restrict the
                  possible mappings of f in posmap accordingly
                  (5.6. can be omitted for the sake of simplicity,
                        since 5.1. does the necessary check as well)
        5.7. if sym1 and sym2 are operations/predicates,
                5.8. For corresponding sorts in their profiles,
                     remove incompatible mappings of the sorts from posmap
                5.9. For each sym in overloading relation with sym1,
                     remove incompatible mappings of sym from posmap
        CONTINUE DEPTH FIRST SERACH
        5.10. call recursively point 4.
6. if for exactly one sym2 step 5 gave a map, return this map.
7. if step 5 gave more than one map, raise an exception. Morphism is
   not unique.
8. (only) if for no sym2 step 5 gave a map,
   repeat steps 5-7 with symset2 instead of symset1
   if this does not give a map either, return "No_map".
//end of the recursive procedure
9. if procedure returned "No_map" or raised an exception, return error
10. otherwise, return computed morphism from target mor1 to sigma2
    composed with mor1.
-}

-- Some auxiliary functions for inducedFromToMorphism
testMatch :: RawSymbolMap -> Symbol -> Symbol -> Bool
testMatch rmap sym1 sym2 =
  Map.foldWithKey match1 True rmap
  where
  match1 rsy1 rsy2 b = b && ((sym1 `matches` rsy1) <= (sym2 `matches`rsy2))

canBeMapped :: RawSymbolMap -> Symbol -> Symbol -> Bool
canBeMapped rmap sym1@(Symbol {symbType = SortAsItemType})
                 sym2@(Symbol {symbType = SortAsItemType}) =
   testMatch rmap sym1 sym2
canBeMapped rmap sym1@(Symbol {symbType = OpAsItemType ot1})
                 sym2@(Symbol {symbType = OpAsItemType ot2}) =
   length (opArgs ot1) == length (opArgs ot2) && -- same arity
   opKind ot1 >= opKind ot2 && -- preservation of totality
   testMatch rmap sym1 sym2
canBeMapped rmap sym1@(Symbol {symbType = PredAsItemType pt1})
                 sym2@(Symbol {symbType = PredAsItemType pt2}) =
   length (predArgs pt1) == length (predArgs pt2) && -- same arity
   testMatch rmap sym1 sym2
canBeMapped _ _ _ = False

preservesName :: Symbol -> Symbol -> Bool
preservesName sym1 sym2 = symName sym1 == symName sym2

compatibleSorts :: SymbolMap -> (SORT, SORT) -> Bool
compatibleSorts smap (s1,s2) =
  case Map.lookup (idToSortSymbol s1) smap of
    Nothing -> True
    Just sym -> symName sym == s2

-- try to extend a symbol map with a yet unmapped symbol
-- (this can fail if sym1 and sym2 are operations/predicates,
--  and mapping on their profiles clashes with what is already
--  known in akmap)
extendSymbMap :: SymbolMap -> Symbol -> Symbol -> Maybe SymbolMap
extendSymbMap akmap sym1 sym2 =
  if case symbType sym1 of
    SortAsItemType -> True
    OpAsItemType ot1 -> case symbType sym2 of
      OpAsItemType ot2 -> all (compatibleSorts akmap)
                           $ zip (opRes ot1:opArgs ot1) (opRes ot2:opArgs ot2)
      _ -> False
    PredAsItemType pt1 -> case symbType sym2 of
      PredAsItemType pt2 -> all (compatibleSorts akmap)
                              $ zip (predArgs pt1) (predArgs pt2)
      _ -> False
    _ -> False
  then Just $ Map.insert sym1 sym2 akmap
  else Nothing

-- Type for posmap
-- Each symbol is mapped to the set symbols it possibly can be mapped to
-- Additionally, we store a flag meaning "no default map" and the
-- cardinality of the symobl set
-- For efficiency reasons, we also carry around an indexing of posmap
-- according to the pairs (flag,cardinality). Since several symbols
-- may lead to the same pair, we have to associate a list of symbols
-- (and corresponding symbol sets) with each pair.
-- Hence, PosMap really is a pair to two maps.
type PosMap = (Map.Map Symbol (SymbolSet, (Bool, Int)),
               Map.Map (Bool, Int) [(Symbol, SymbolSet)])

-- Some basic operations on PosMap

-- postpone entries with no default mapping and size > 1
postponeEntry :: Symbol -> SymbolSet -> Bool
postponeEntry sym symset =
  Set.null (Set.filter (preservesName sym) symset) && Set.size symset > 1

removeFromPosmap :: Symbol -> (Bool, Int) -> PosMap -> PosMap
removeFromPosmap sym card (posmap1,posmap2) =
  (Map.delete sym posmap1,
   Map.update removeSym1 card posmap2)
  where
  removeSym [] = []
  removeSym ((x,y):l) = if x == sym then l else (x, y) : removeSym l
  removeSym1 l = case removeSym l of
    [] -> Nothing
    l1 -> Just l1

addToPosmap :: Symbol -> SymbolSet -> PosMap -> PosMap
addToPosmap sym symset (posmap1,posmap2) =
  (Map.insert sym (symset,card) posmap1,
   listInsert card (sym,symset) posmap2)
  where card = (postponeEntry sym symset, Set.size symset)

-- restrict posmap such that each symbol from symset1 is only mapped
-- to symbols from symset2
restrictPosMap :: SymbolSet -> SymbolSet -> PosMap -> PosMap
restrictPosMap symset1' symset2 posmap' =
  Set.fold restrictPosMap1 posmap' symset1'
  where
  restrictPosMap1 sym1 posmap@(posmap1, _posmap2)  =
    case Map.lookup sym1 posmap1 of
      Nothing -> posmap
      Just (symset1, card) ->
         addToPosmap sym1 (symset1 `Set.intersection` symset2)
          $ removeFromPosmap sym1 card posmap

-- for each sub/supersort s of sym1 in sigma1, restrict the possible
-- mappings of s in posmap to sub/supersorts of sym2 in sigma2
restrictSorts :: Symbol -> Symbol -> Sign f e -> Sign f e -> PosMap -> PosMap
restrictSorts sym1 sym2 sigma1 sigma2 posmap =
  restrictPosMap subsyms1 subsyms2
    $ restrictPosMap supersyms1 supersyms2 posmap
  where
  s1 = symName sym1
  s2 = symName sym2
  sub1 = Set.insert s1 $ subsortsOf s1 sigma1
  sub2 = Set.insert s2 $ subsortsOf s2 sigma2
  subsyms1 = Set.map idToSortSymbol sub1
  subsyms2 = Set.map idToSortSymbol sub2
  super1 = Set.insert s1 $ supersortsOf s1 sigma1
  super2 = Set.insert s2 $ supersortsOf s2 sigma2
  supersyms1 = Set.map idToSortSymbol super1
  supersyms2 = Set.map idToSortSymbol super2

-- remove all sort mappings that map s1 to a sort different from s2
removeIncompatibleSortMaps :: Maybe PosMap -> (SORT, SORT) -> Maybe PosMap
removeIncompatibleSortMaps Nothing _ = Nothing
removeIncompatibleSortMaps (Just posmap@(posmap1,_posmap2)) (s1,s2) =
  case Map.lookup sym1 posmap1 of
    Nothing -> Just posmap
    Just (symset,card) ->
      -- is there some remaining possibility to map the sort?
      if sym2 `Set.member` symset
         then Just $ addToPosmap sym1 (Set.singleton sym2)
                   $ removeFromPosmap sym1 card posmap
         -- if not, there is no map!
         else Nothing
  where
  sym1 = idToSortSymbol s1
  sym2 = idToSortSymbol s2

-- For corresponding sorts in profiles of sym1 and sym2,
-- remove incompatible mappings of the sorts from posmap
restrictOps :: Symbol -> Symbol -> PosMap -> Maybe PosMap
restrictOps sym1 sym2 posmap =
  foldl removeIncompatibleSortMaps (Just posmap) $ zip sort1 sorts2
  where
  (sort1,sorts2) = case (symbType sym1,symbType sym2) of
    (OpAsItemType ot1,OpAsItemType ot2) ->
       (opRes ot1:opArgs ot1,opRes ot2:opArgs ot2)
    (PredAsItemType pt1,PredAsItemType pt2) ->
       (predArgs pt1,predArgs pt2)
    _ -> ([],[])

-- the main function
inducedFromToMorphism :: (Eq e, Eq f, Pretty f, Pretty e, Pretty m)
                      => m -- ^ extended morphism
                      -> (e -> e -> Bool) -- ^ subsignature test of extensions
                      -> (e -> e -> e) -- ^ difference of extensions
                      -> RawSymbolMap
                      -> ExtSign (Sign f e) Symbol
                      -> ExtSign (Sign f e) Symbol -> Result (Morphism f e m)
inducedFromToMorphism extEm isSubExt diffExt rmap (ExtSign sigma1 sy1)
  (ExtSign sigma2 sy2) = do
  let symset1 = symOf sigma1
      symset2 = symOf sigma2
  -- 1. use rmap to get a renaming...
  mor1 <- inducedFromMorphism extEm isSubExt rmap sigma1
  -- 1.1 ... is the renamed source signature contained in the target signature?
  let inducedSign = mtarget mor1
  if isSubSig isSubExt inducedSign sigma2
   -- yes => we are done
   then composeM (\ _ _ -> return extEm) mor1
            $ idOrInclMorphism isSubExt
            $ embedMorphism extEm inducedSign sigma2
   -- no => OK, we've to take the hard way
   else let so1 = Set.findMin sy1
            so2 = Set.findMin sy2 in
        if Map.null rmap && Set.size sy1 == 1 && Set.size sy2 == 1
           && symbType so1 == SortAsItemType && symbType so1 == SortAsItemType
           then return mor1
                    { mtarget = sigma2
                    , sort_map = Map.singleton (symName so1)
                                 $ symName so2 }
   else do -- 2. Compute initial posmap, using all possible mappings of symbols
     let addCard sym s = (s,(postponeEntry sym s,Set.size s))
         ins1 sym = Map.insert sym
                   (addCard sym $ Set.filter (canBeMapped rmap sym) symset2)
         posmap1 = Set.fold ins1 Map.empty symset1
         ins2 sym1a (symset,card) = listInsert card (sym1a,symset)
         posmap2 = Map.foldWithKey ins2 Map.empty posmap1
         posmap = (posmap1,posmap2)
     -- Are there symbols that cannot be mapped at all?
     -- Then generate an error immediately
     --trace ("posmap1= "++showDoc posmap1 "") (return ())
     case Map.lookup (True,0) posmap2 of
       Nothing -> return ()
       Just syms -> fail $ "No symbol mapping for "
                    ++ showDoc (map fst syms) ""
     -- 3. call recursive function with empty akmap and initial posmap
     smap <- tryToInduce sigma1 sigma2 Map.empty posmap
     smap1 <- case smap of
       Nothing -> fatal_error
         ("No signature morphism for symbol map found.\n" ++
          "The following mapped symbols are missing in the target signature:\n"
          ++ showDoc (diffSig diffExt inducedSign sigma2) "")
          $ concatMapRange getRange $ Map.keys rmap
       Just x -> return x
     -- 9./10. compute and return the resulting morphism
     symbMapToMorphism extEm sigma1 sigma2 smap1

     -- 4. recursive depth first function
     -- ambiguous map leads to fatal error (similar to exception)
tryToInduce :: Sign f e -> Sign f e -> SymbolMap -> PosMap
            -> Result (Maybe SymbolMap)
tryToInduce sigma1 sigma2 akmap (posmap1, posmap2) = do
       --trace("akmap: "++showDoc akmap "") (return ())
       if Map.null posmap2 then return $ Just akmap -- 4a.
        else do
          --trace ("trying to map: "++showDoc sym1 "") (return ())
          akmap1 <-
             tryToInduce1 sigma1 sigma2 akmap posmap' sym1 symset1
          case akmap1 of
             -- 6. no map for symset1, hence try symset2
            Nothing -> tryToInduce1 sigma1 sigma2 akmap posmap' sym1 symset2
            Just _ -> return akmap1
       where
       -- 4b. take symbol with minimal remaining values (MRV)
       (card,(sym1,symset):_symsets) = Map.findMin posmap2
       (symset1,symset2) = Set.partition (preservesName sym1) symset
       posmap' = removeFromPosmap sym1 card (posmap1,posmap2)

     -- 5. to 7.
tryToInduce1 :: Sign f e -> Sign f e -> SymbolMap -> PosMap -> Symbol
             -> Set.Set Symbol -> Result (Maybe SymbolMap)
tryToInduce1 sigma1 sigma2 akmap posmap sym1 symset = do
       Set.fold (tryToInduce2 sigma1 sigma2 akmap posmap sym1)
                       (return Nothing) symset

tryToInduce2 :: Sign f e -> Sign f e -> SymbolMap -> PosMap -> Symbol
             -> Symbol -> Result (Maybe SymbolMap)
             -> Result (Maybe SymbolMap)
tryToInduce2 sigma1 sigma2 akmap posmap sym1 sym2 akmapSoFar = do
       -- 5.1. to 5.3. consistency check
       akmapSoFar1 <- akmapSoFar
       {-(trace ("map "++(case akmapSoFar1 of
                         Just x -> showDoc x " + "
                         Nothing -> "")
        ++showDoc sym1 " |-> " ++showDoc sym2 "; stopBackTrack: "
        ++show stopBackTrack) (return ())) -}
       akmap' <-
        case extendSymbMap akmap sym1 sym2 of
         Nothing -> return Nothing
         -- constraint propagation
         Just akmap1 -> do
           let posmap1 = case symbType sym1 of
                -- 5.4./5.5. constraint propagation for a sort symbol
                SortAsItemType ->
                  Just $ restrictSorts sym1 sym2 sigma1 sigma2 posmap
                -- 5.6. omitted so far (not really necessary)
                -- 5.7./5.8. constraint propagation
                --           for an operation/predicate symbol
                _ -> restrictOps sym1 sym2 posmap
                 -- 5.9. omitted until overload relation will be available !!??
           -- 5.10.
           case posmap1 of
             Just posmap2 -> do
                tryToInduce sigma1 sigma2 akmap1 posmap2
             _ -> return Nothing
       -- 6./7. uniqueness check
       case (akmap', akmapSoFar1) of
         -- stop backtracking next time if there haven't been new sort maps
         (Nothing, Nothing) -> return Nothing
         (Just smap, Nothing) -> return $ Just smap
         (Nothing, Just smap) -> return $ Just smap
         (Just smap1, Just smap2) ->
            let shorten = Map.filterWithKey (/=) in
            fatal_error (shows
             (text "Ambiguous symbol map" $+$
              text "Map1" <+> pretty (shorten smap1) $+$
              text "Map2" <+> pretty (shorten smap2) $+$
              text "Please, supply a unique fitting morphism")
             "") $ concatMapRange getRange $ Map.elems $ shorten smap1

{-
Computing signature generated by a symbol set.

Algorithm adapted from Bartek Klin's algorithm for CATS.

Input:  symbol set "Syms"
        signature "Sigma"
Output: signature "Sigma1"<=Sigma.

1. get a set "Sigma_symbols" of symbols in Sigma.
2. if Syms is not a subset of Sigma_symbols, return error.
3. let Sigma1 be an empty signature.
4. for each symbol "Sym" in Syms do:
        4.1. if Sym is a:
                4.1.1. sort "S": add sort S to Sigma1.
                4.1.2. total function "F" with profile "Fargs,Fres":
                        4.1.2.1. add all sorts from Fargs to Sigma1.
                        4.1.2.2. add sort Fres to Sigma1.
                        4.1.2.3. add F with the needed profile to Sigma1.
                4.1.3. partial function: as in 4.1.2.
                4.1.4. predicate: as in 4.1.2., except that Fres is omitted.
5. get a list "Sig_sub" of subsort relations in Sigma.
6. for each pair "S1,S2" in Sig_sub do:
        6.1. if S1,S2 are sorts in Sigma1, add "S1,S2" to sort relations in
                Sigma1.
7. return the inclusion of sigma1 into sigma.
-}

generatedSign :: m -> (e -> e -> Bool) -> SymbolSet -> Sign f e
              -> Result (Morphism f e m)
generatedSign extEm isSubExt sys sigma =
  if not (sys `Set.isSubsetOf` symset)   -- 2.
   then let diffsyms = sys Set.\\ symset in
        fatal_error ("Revealing: The following symbols "
                     ++ showDoc diffsyms " are not in the signature")
        $ getRange diffsyms
   else return $ idOrInclMorphism isSubExt $ embedMorphism extEm sigma2 sigma
  -- 7.
  where
  symset = symOf sigma   -- 1.
  sigma1 = Set.fold revealSym (sigma { sortSet = Set.empty
                                     , opMap = Map.empty
                                     , predMap = Map.empty }) sys  -- 4.
  sigma2 = sigma1
    { sortRel = sortRel sigma `Rel.restrict` sortSet sigma1
    , emptySortSet = Set.intersection (sortSet sigma1) $ emptySortSet sigma }

revealSym :: Symbol -> Sign f e -> Sign f e
revealSym sy sigma1 = case symbType sy of  -- 4.1.
    SortAsItemType ->      -- 4.1.1.
      sigma1 {sortSet = Set.insert (symName sy) $ sortSet sigma1}
    OpAsItemType ot ->     -- 4.1.2./4.1.3.
      sigma1 { sortSet = foldr Set.insert (sortSet sigma1)
               $ opRes ot : opArgs ot
             , opMap = Rel.setInsert (symName sy) ot $ opMap sigma1 }
    PredAsItemType pt ->   -- 4.1.4.
      sigma1 { sortSet = foldr Set.insert (sortSet sigma1) $ predArgs pt
             , predMap = Rel.setInsert (symName sy) pt $ predMap sigma1 }
    _ -> sigma1 -- extend this for the type variable e
  -- 5./6.

{-
Computing signature co-generated by a raw symbol set.

Algorithm adapted from Bartek Klin's algorithm for CATS.

Input:  symbol set "Syms"
        signature "Sigma"
Output: signature "Sigma1"<=Sigma.

1. get a set "Sigma_symbols" of symbols in Sigma.
2. if Syms is not a subset of Sigma_symbols, return error.
3. for each symbol "Sym" in Syms do:
        3.1. if Sym is a:
                3.1.1. sort "S":
                        3.1.1.1. Remove S from Sigma_symbols
                        3.1.1.2. For each function/predicate symbol in
                                Sigma_symbols, if its profile contains S
                                remove it from Sigma_symbols.
                3.1.2. any other symbol: remove if from Sigma_symbols.
4. let Sigma1 be a signature generated by Sigma_symbols in Sigma.
5. return the inclusion of sigma1 into sigma.
-}

cogeneratedSign :: m -> (e -> e -> Bool) -> SymbolSet -> Sign f e
                -> Result (Morphism f e m)
cogeneratedSign extEm isSubExt symset sigma =
  if {-trace ("symset "++show symset++"\nsymset0 "++show symset0)-}
           (not (symset `Set.isSubsetOf` symset0))   -- 2.
   then let diffsyms = symset Set.\\ symset0 in
        fatal_error ("Hiding: The following symbols "
            ++ showDoc diffsyms " are not in the signature")
        $ getRange diffsyms
   else generatedSign extEm isSubExt symset1 sigma -- 4./5.
  where
  symset0 = symOf sigma   -- 1.
  symset1 = Set.fold revealSym' symset0 symset  -- 3.
  revealSym' sy symset1' = case symbType sy of  -- 3.1.
    SortAsItemType ->      -- 3.1.1.
      Set.filter (not . profileContains (symName sy) . symbType)
        $ Set.delete sy symset1'
    OpAsItemType _ ->     -- 3.1.2
      Set.delete sy symset1'
    PredAsItemType _ ->   -- 3.1.2
      Set.delete sy symset1'
    _ ->  symset1'
  profileContains s symbT = elem s $ case symbT of
    OpAsItemType ot -> opRes ot : opArgs ot
    PredAsItemType pt -> predArgs pt
    _ -> [] -- for other kinds the profiles need to be looked up

finalUnion :: (e -> e -> e) -- ^ join signature extensions
           -> Sign f e -> Sign f e -> Result (Sign f e)
finalUnion addSigExt s1 s2 =
 let leCl eq = Map.map (Rel.partSet eq)
     mkp = Map.map makePartial
     extP = Map.map (map $ \ s -> (s, [], False))
     o1 = extP $ leCl (leqF s1) $ mkp $ opMap s1
     o2 = extP $ leCl (leqF s2) $ mkp $ opMap s2
     p1 = extP $ leCl (leqP s1) $ predMap s1
     p2 = extP $ leCl (leqP s2) $ predMap s2
     s3 = addSig addSigExt s1 s2
     o3 = leCl (leqF s3) $ mkp $ opMap s3
     p3 = leCl (leqP s3) $ predMap s3
     d1 = Map.differenceWith (listOfSetDiff True) o1 o3
     d2 = Map.union d1 $ Map.differenceWith (listOfSetDiff False) o2 o3
     e1 = Map.differenceWith (listOfSetDiff True) p1 p3
     e2 = Map.union e1 $ Map.differenceWith (listOfSetDiff False) p2 p3
     prL (s, l, b) = fsep
       $ text ("(" ++ (if b then "left" else "right")
               ++ " side of union)")
       : map pretty l ++ [mapsto <+> pretty s]
     prM str = ppMap ((text str <+>) . pretty)
               (vcat . map prL) id vcat (\ v1 v2 -> sep [v1, v2])
 in if Map.null d2 && Map.null e2 then return s3
    else fail $ "illegal overload relation identifications for profiles of:\n"
         ++ show (prM "op" d2 $+$ prM "pred" e2)

listOfSetDiff :: Ord a => Bool -> [(Set.Set a, [Set.Set a], Bool)]
              -> [Set.Set a]-> Maybe [(Set.Set a, [Set.Set a], Bool)]
listOfSetDiff b rl1 l2 = let
  fst3 (s, _, _) = s
  l1 = map fst3 rl1 in
  (\ l3 -> if null l3 then Nothing else Just l3)
  $ fst $ foldr
  (\ s (l, r) ->
         let sIn = Set.isSubsetOf s
             (r1, r2) = partition sIn r in
         case r1 of
           [] -> case find sIn l2 of
             Nothing -> error "CASL.finalUnion.listOfSetDiff1"
             Just s2 -> (if elem s2 $ map fst3 l then l else
                         (s2, filter (flip Set.isSubsetOf s2) l1, b) : l, r)
           [_] -> (l, r2)
           _ -> error "CASL.finalUnion.listOfSetDiff2")
  ([], l2) l1

-- | Insert into a list of values
listInsert :: Ord k => k -> a -> Map.Map k [a] -> Map.Map k [a]
listInsert kx x t = Map.insert kx (x : Map.findWithDefault [] kx t) t
