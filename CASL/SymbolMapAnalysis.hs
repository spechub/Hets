{- |
Module      :  $Header$
Description :  symbol map analysis for the CASL logic.
Copyright   :  (c) Till Mossakowski, C. Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Symbol map analysis for the CASL logic.
  Follows Sect. III:4.1 of the CASL Reference Manual.
-}

module CASL.SymbolMapAnalysis
    ( inducedFromMorphism
    , inducedFromToMorphism
    , inducedFromMorphismExt
    , inducedFromToMorphismExt
    , cogeneratedSign
    , generatedSign
    , finalUnion
    , constMorphExt
    ) where

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
import Data.Maybe

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

type InducedMorphism e m = RawSymbolMap -> e -> Result m

constMorphExt :: m -> InducedMorphism e m
constMorphExt m _ _ = return m

inducedFromMorphism :: (Pretty e, Show f) => m -> RawSymbolMap -> Sign f e
                    -> Result (Morphism f e m)
inducedFromMorphism =
  inducedFromMorphismExt (\ _ _ _ _ -> extendedInfo) . constMorphExt

inducedFromMorphismExt :: (Pretty e, Show f) => InducedSign f e m e
                       -> InducedMorphism e m
                       -> RawSymbolMap -> Sign f e -> Result (Morphism f e m)
inducedFromMorphismExt extInd extEm rmap sigma = do
  -- ??? Missing: check preservation of overloading relation
  -- compute the sort map (as a Map)
  sort_Map <- Set.fold (\ s m -> do
                s' <- sortFun rmap s
                m1 <- m
                return $ if s' == s then m1 else Map.insert s s' m1)
              (return Map.empty) (sortSet sigma)
  -- compute the op map (as a Map)
  op_Map <- Map.foldrWithKey (opFun sigma rmap sort_Map)
              (return Map.empty) (opMap sigma)
  -- compute the pred map (as a Map)
  pred_Map <- Map.foldrWithKey (predFun sigma rmap sort_Map)
              (return Map.empty) (predMap sigma)
  em <- extEm rmap $ extendedInfo sigma
  -- return assembled morphism
  return (embedMorphism em sigma $ closeSortRel
          $ inducedSignAux extInd sort_Map op_Map pred_Map em sigma)
    { sort_map = sort_Map
    , op_map = op_Map
    , pred_map = pred_Map }

  -- the sorts of the source signature
  -- sortFun is the sort map as a Haskell function
sortFun :: RawSymbolMap -> Id -> Result Id
sortFun rmap s
    -- rsys contains the raw symbols to which s is mapped to
  | Set.null rsys = return s -- use default = identity mapping
  | Set.null $ Set.deleteMin rsys =
          return $ rawSymName $ Set.findMin rsys -- take the unique rsy
  | otherwise = plain_error s  -- ambiguity! generate an error
                 ("sort " ++ showId s
                  " is mapped ambiguously: " ++ showDoc rsys "")
                 $ getRange rsys
    where
    -- get all raw symbols to which s is mapped to
    rsys = Set.fromList $ mapMaybe (`Map.lookup` rmap)
               [ ASymbol $ idToSortSymbol s
               , AKindedSymb Implicit s ]

  {- to a Op_map, add everything resulting from mapping (id, ots)
  according to rmap -}
opFun :: Sign f e -> RawSymbolMap -> Sort_map -> Id -> Set.Set OpType
      -> Result Op_map -> Result Op_map
opFun src rmap sort_Map ide ots m =
    -- first consider all directly mapped profiles
    let otls = Rel.partSet (leqF src) ots
        m1 = foldr (directOpMap rmap sort_Map ide) m otls
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedSymb Ops_kind ide) rmap,
                Map.lookup (AKindedSymb Implicit ide) rmap) of
       (Just rsy1, Just rsy2) -> let
          m2 = Set.fold (insertmapOpSym sort_Map ide rsy1) m1 ots
          in Set.fold (insertmapOpSym sort_Map ide rsy2) m2 ots
       (Just rsy, Nothing) ->
          Set.fold (insertmapOpSym sort_Map ide rsy) m1 ots
       (Nothing, Just rsy) ->
          Set.fold (insertmapOpSym sort_Map ide rsy) m1 ots
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

    -- try to map an operation symbol directly
    -- collect all opTypes that cannot be mapped directly
directOpMap :: RawSymbolMap -> Sort_map -> Id -> Set.Set OpType
            -> Result Op_map -> Result Op_map
directOpMap rmap sort_Map ide ots m =
  let ol = Set.toList ots
      rl = map (lookupOpSymbol rmap ide) ol
      (ms, os) = partition (isJust . fst) $ zip rl ol
  in case ms of
       l@((Just rsy, _) : rs) ->
         foldr (\ (_, ot) ->
           insertmapOpSym sort_Map ide
              (ASymbol $ idToOpSymbol (rawSymName rsy)
                       $ mapOpType sort_Map ot) ot)
         (foldr (\ (Just rsy2, ot) ->
           insertmapOpSym sort_Map ide rsy2 ot) m l)
         $ rs ++ os
       _ -> m

lookupOpSymbol :: RawSymbolMap -> Id -> OpType -> Maybe RawSymbol
lookupOpSymbol rmap ide' ot = let mkS = idToOpSymbol ide' in
  case Map.lookup (ASymbol (mkS $ mkPartial ot)) rmap of
    Nothing -> Map.lookup
      (ASymbol (mkS $ mkTotal ot)) rmap
    res -> res

    -- map op symbol (ide, ot) to raw symbol rsy
mappedOpSym :: Sort_map -> Id -> OpType -> RawSymbol -> Result (Id, OpKind)
mappedOpSym sort_Map ide ot rsy =
    let opSym = "operation symbol " ++ showDoc (idToOpSymbol ide ot)
                " is mapped to "
        kind = opKind ot
    in case rsy of
      ASymbol (Symbol ide' (OpAsItemType ot')) ->
        if compatibleOpTypes (mapOpType sort_Map ot) ot'
           then return (ide', opKind ot')
           else plain_error (ide, kind)
             (opSym ++ "type " ++ showDoc ot'
              " but should be mapped to type " ++
              showDoc (mapOpType sort_Map ot) "") $ getRange rsy
      AKindedSymb k ide' | elem k [Implicit, Ops_kind] -> return (ide', kind)
      _ -> plain_error (ide, kind)
               (opSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

    -- insert mapping of op symbol (ide, ot) to raw symbol rsy into m
insertmapOpSym :: Sort_map -> Id -> RawSymbol -> OpType
               -> Result Op_map -> Result Op_map
insertmapOpSym sort_Map ide rsy ot m = do
      m1 <- m
      (ide', kind') <- mappedOpSym sort_Map ide ot rsy
      let otsy = Symbol ide $ OpAsItemType ot
          pos = getRange rsy
          m2 = Map.insert (ide, mkPartial ot) (ide', kind') m1
      case Map.lookup (ide, mkPartial ot) m1 of
        Nothing -> if ide == ide' && kind' == opKind ot then
            case rsy of
              ASymbol _ -> return m1
              _ -> hint m1 ("identity mapping of "
                               ++ showDoc otsy "") pos
            else return m2
        Just (ide'', kind'') -> if ide' == ide'' then
             warning (if kind' < kind'' then m2 else m1)
             ("ignoring duplicate mapping of " ++ showDoc otsy "")
             pos
            else plain_error m1
             ("conflicting mapping of " ++ showDoc otsy " to " ++
               show ide' ++ " and " ++ show ide'') pos

  {- to a Pred_map, add evering resulting from mapping (ide,pts)
  according to rmap -}

predFun :: Sign f e -> RawSymbolMap -> Sort_map -> Id -> Set.Set PredType
               -> Result Pred_map -> Result Pred_map
predFun src rmap sort_Map ide pts m =
    -- first consider all directly mapped profiles
    let ptls = Rel.partSet (leqP src) pts
        m1 = foldr (directPredMap rmap sort_Map ide) m ptls
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (AKindedSymb Preds_kind ide) rmap,
                Map.lookup (AKindedSymb Implicit ide) rmap) of
       (Just rsy1, Just rsy2) -> let
          m2 = Set.fold (insertmapPredSym sort_Map ide rsy1) m1 pts
          in Set.fold (insertmapPredSym sort_Map ide rsy2) m2 pts
       (Just rsy, Nothing) ->
          Set.fold (insertmapPredSym sort_Map ide rsy) m1 pts
       (Nothing, Just rsy) ->
          Set.fold (insertmapPredSym sort_Map ide rsy) m1 pts
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

    -- try to map a predicate symbol directly
    -- collect all predTypes that cannot be mapped directly
directPredMap :: RawSymbolMap -> Sort_map -> Id -> Set.Set PredType
              -> Result Pred_map -> Result Pred_map
directPredMap rmap sort_Map ide pts m =
  let pl = Set.toList pts
      rl = map (\ pt -> Map.lookup (ASymbol $ idToPredSymbol ide pt) rmap) pl
      (ms, ps) = partition (isJust . fst) $ zip rl pl
  in case ms of
       l@((Just rsy, _) : rs) ->
         foldr (\ (_, pt) ->
           insertmapPredSym sort_Map ide
              (ASymbol $ idToPredSymbol (rawSymName rsy)
                       $ mapPredType sort_Map pt) pt)
         (foldr (\ (Just rsy2, pt) ->
           insertmapPredSym sort_Map ide rsy2 pt) m l)
         $ rs ++ ps
       _ -> m

    -- map pred symbol (ide,pt) to raw symbol rsy
mappedPredSym :: Sort_map -> Id -> PredType -> RawSymbol -> Result Id
mappedPredSym sort_Map ide pt rsy =
    let predSym = "predicate symbol " ++ showDoc (idToPredSymbol ide pt)
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
      let ptsy = Symbol ide $ PredAsItemType pt
          pos = getRange rsy
          m2 = Map.insert (ide, pt) ide' m1
      case Map.lookup (ide, pt) m1 of
        Nothing -> if ide == ide' then
            case rsy of
              ASymbol _ -> return m1
              _ -> hint m1 ("identity mapping of "
                               ++ showDoc ptsy "") pos
            else return m2
        Just ide'' -> if ide' == ide'' then
            warning m1
             ("ignoring duplicate mapping of " ++ showDoc ptsy "") pos
            else plain_error m1
             ("conflicting mapping of " ++ showDoc ptsy " to " ++
               show ide' ++ " and " ++ show ide'') pos

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
otherwise some heuristics is needed, because merely forgetting one renaming
may lead to unacceptable run-time for signatures with just about 10 symbols
-}

-- the main function
inducedFromToMorphism :: (Eq e, Show f, Pretty e, Pretty m)
                      => m -- ^ extended morphism
                      -> (e -> e -> Bool) -- ^ subsignature test of extensions
                      -> (e -> e -> e) -- ^ difference of extensions
                      -> RawSymbolMap
                      -> ExtSign (Sign f e) Symbol
                      -> ExtSign (Sign f e) Symbol -> Result (Morphism f e m)
inducedFromToMorphism m =
  inducedFromToMorphismExt (\ _ _ _ _ -> extendedInfo) (constMorphExt m)
  (\ _ _ _ -> return m)

inducedFromToMorphismExt
  :: (Eq e, Show f, Pretty e, Pretty m)
  => InducedSign f e m e
  -> InducedMorphism e m -- ^ compute extended morphism
  -> (e -> m -> m -> Result m) -- ^ composition of extensions
  -> (e -> e -> Bool) -- ^ subsignature test of extensions
  -> (e -> e -> e) -- ^ difference of extensions
  -> RawSymbolMap
  -> ExtSign (Sign f e) Symbol
  -> ExtSign (Sign f e) Symbol
  -> Result (Morphism f e m)
inducedFromToMorphismExt extInd extEm compM isSubExt diffExt rmap
  sig1@(ExtSign _ sy1) sig2@(ExtSign _ sy2) =
    let iftm rm = (inducedFromToMorphismAuxExt extInd extEm compM isSubExt
                   diffExt rm sig1 sig2, rm)
        isOk = isJust . resultToMaybe
        res = fst $ iftm rmap
        pos = concatMapRange getRange $ Map.keys rmap
    in if isOk res then res else
       let ss1 = Set.filter (\ s -> Set.null $ Set.filter
                             (compatibleSymbols True s) sy2)
             $ Set.filter (\ s -> not $ any (matches s) $ Map.keys rmap)
                 sy1
           fcombs = filteredPairs compatibleRawSymbs
                    (map ASymbol $ Set.toList ss1)
                    $ map ASymbol $ Set.toList sy2
       in if null (drop 20 fcombs) then
          case filter (isOk . fst) $ map (iftm . Map.union rmap . Map.fromList)
               fcombs of
            [] -> res
            [(r, m)] -> (if length fcombs > 1 then warning else hint)
              () ("derived symbol map:\n" ++ showDoc m "") pos >> r
            l -> fatal_error
              ("ambiguous symbol maps:\n" ++ show
                  (vcat $ map (pretty . snd) l)) pos
          else warning () "too many possibilities for symbol maps" pos >> res

compatibleSymbTypes :: SymbType -> SymbType -> Bool
compatibleSymbTypes s1 s2 = case (s1, s2) of
  (SortAsItemType, SortAsItemType) -> True
  (OtherTypeKind t1, OtherTypeKind t2) -> t1 == t2
  (OpAsItemType t1, OpAsItemType t2) ->
     length (opArgs t1) == length (opArgs t2)
  (PredAsItemType p1, PredAsItemType p2) ->
      length (predArgs p1) == length (predArgs p2)
  _ -> False

compatibleSymbols :: Bool -> Symbol -> Symbol -> Bool
compatibleSymbols alsoId (Symbol i1 k1) (Symbol i2 k2) =
  compatibleSymbTypes k1 k2 && (not alsoId || i1 == i2)

compatibleRawSymbs :: RawSymbol -> RawSymbol -> Bool
compatibleRawSymbs r1 r2 = case (r1, r2) of
  (ASymbol s1, ASymbol s2) -> compatibleSymbols False s1 s2
  _ -> False -- irrelevant

filteredPairs :: (a -> b -> Bool) -> [a] -> [b] -> [[(a, b)]]
filteredPairs p s l = sequence [[(a, b) | b <- filter (p a) l] | a <- s]
-- http://www.haskell.org/pipermail/haskell-cafe/2009-December/069957.html

inducedFromToMorphismAuxExt
  :: (Eq e, Show f, Pretty e, Pretty m)
  => InducedSign f e m e
  -> InducedMorphism e m -- ^ compute extended morphism
  -> (e -> m -> m -> Result m) -- ^ composition of extensions
  -> (e -> e -> Bool) -- ^ subsignature test of extensions
  -> (e -> e -> e) -- ^ difference of extensions
  -> RawSymbolMap
  -> ExtSign (Sign f e) Symbol
  -> ExtSign (Sign f e) Symbol
  -> Result (Morphism f e m)
inducedFromToMorphismAuxExt extInd extEm compM isSubExt diffExt rmap
  (ExtSign sigma1 _) (ExtSign sigma2 _) = do
  -- 1. use rmap to get a renaming...
  mor1 <- inducedFromMorphismExt extInd extEm rmap sigma1
  -- 1.1 ... is the renamed source signature contained in the target signature?
  let inducedSign = mtarget mor1
      em = extended_map mor1
  if isSubSig isSubExt inducedSign sigma2
   -- yes => we are done
   then composeM (compM $ extendedInfo $ msource mor1) mor1 $ idOrInclMorphism
     $ embedMorphism em inducedSign sigma2
     -- here the empty mapping should be used, but it will be overwritten
     -- by the first argument of composeM
   else fatal_error
         ("No signature morphism for symbol map found.\n" ++
          "The following mapped symbols are missing in the target signature:\n"
          ++ showDoc (diffSig diffExt inducedSign sigma2) "")
          $ concatMapRange getRange $ Map.keys rmap

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

generatedSign :: m -> SymbolSet -> Sign f e
              -> Result (Morphism f e m)
generatedSign extEm sys sigma =
  if not (sys `Set.isSubsetOf` symset)   -- 2.
   then let diffsyms = sys Set.\\ symset in
        fatal_error ("Revealing: The following symbols "
                     ++ showDoc diffsyms " are not in the signature")
        $ getRange diffsyms
   else return $ idOrInclMorphism $ embedMorphism extEm sigma2 sigma
  -- 7.
  where
  symset = symsetOf sigma   -- 1.
  sigma1 = Set.fold revealSym (sigma { sortSet = Set.empty
                                     , opMap = Map.empty
                                     , predMap = Map.empty }) sys  -- 4.
  sigma2 = sigma1
    { sortRel = sortRel sigma `Rel.restrict` sortSet sigma1
    , emptySortSet = Set.intersection (sortSet sigma1) $ emptySortSet sigma }

revealSym :: Symbol -> Sign f e -> Sign f e
revealSym sy sigma1 = case symbType sy of
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

cogeneratedSign :: m -> SymbolSet -> Sign f e
                -> Result (Morphism f e m)
cogeneratedSign extEm symset sigma =
  if Set.isSubsetOf symset symset0   -- 2.
   then generatedSign extEm symset1 sigma -- 4./5.
   else let diffsyms = symset Set.\\ symset0 in
        fatal_error ("Hiding: The following symbols "
            ++ showDoc diffsyms " are not in the signature")
        $ getRange diffsyms
  where
  symset0 = symsetOf sigma   -- 1.
  symset1 = Set.fold revealSym' symset0 symset  -- 3.
  revealSym' sy symset1' = case symbType sy of
    SortAsItemType ->      -- 3.1.1.
      Set.filter (not . profileContains (symName sy) . symbType)
        $ Set.delete sy symset1'
    OpAsItemType _ ->     -- 3.1.2
      Set.delete sy symset1'
    PredAsItemType _ ->   -- 3.1.2
      Set.delete sy symset1'
    _ -> symset1'
  profileContains s symbT = elem s $ case symbT of
    OpAsItemType ot -> opRes ot : opArgs ot
    PredAsItemType pt -> predArgs pt
    _ -> [] -- for other kinds the profiles need to be looked up

leCl :: Ord a => (a -> a -> Bool) -> Map.Map Id (Set.Set a)
     -> Map.Map Id [Set.Set a]
leCl = Map.map . Rel.partSet

mkp :: Map.Map Id (Set.Set OpType) -> Map.Map Id (Set.Set OpType)
mkp = Map.map makePartial

finalUnion :: (e -> e -> e) -- ^ join signature extensions
           -> Sign f e -> Sign f e -> Result (Sign f e)
finalUnion addSigExt s1 s2 =
 let extP = Map.map (map $ \ s -> (s, [], False))
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
              -> [Set.Set a] -> Maybe [(Set.Set a, [Set.Set a], Bool)]
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
                         (s2, filter (`Set.isSubsetOf` s2) l1, b) : l, r)
           [_] -> (l, r2)
           _ -> error "CASL.finalUnion.listOfSetDiff2")
  ([], l2) l1
