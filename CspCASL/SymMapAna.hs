{- |
Module      :  $Header$
Description :  symbol map analysis for the CspCASL logic.
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CspCASL.SymMapAna where

import CspCASL.AS_CspCASL_Process
import CspCASL.Morphism
import CspCASL.SignCSP
import CspCASL.SymbItems
import CspCASL.Symbol

import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.SymbolMapAnalysis

import Common.DocUtils
import Common.Id
import Common.Result
import qualified Common.Lib.Rel as Rel

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (partition)
import Data.Maybe

type CspRawMap = Map.Map CspRawSymbol CspRawSymbol

cspInducedFromMorphism :: CspRawMap -> CspCASLSign -> Result CspCASLMorphism
cspInducedFromMorphism rmap sigma = do
  let (crm, _) = splitSymbolMap rmap
  m <- inducedFromMorphism emptyCspAddMorphism crm sigma
  let sm = sort_map m
      om = op_map m
      pm = pred_map m
      csig = extendedInfo sigma
  -- compute the channel name map (as a Map)
  cm <- Map.foldWithKey (chanFun sigma rmap sm)
              (return Map.empty) (chans csig)
  -- compute the process name map (as a Map)
  proc_Map <- Map.foldWithKey (procFun sigma rmap sm cm)
              (return Map.empty) (procSet csig)
  let em = emptyCspAddMorphism
        { channelMap = cm
        , processMap = proc_Map }
  return (embedMorphism em sigma $ closeSortRel
          $ inducedSignAux inducedCspSign sm om pm em sigma)
    { sort_map = sm
    , op_map = om
    , pred_map = pm }

chanFun :: CspCASLSign -> CspRawMap -> Sort_map -> Id -> Set.Set SORT
  -> Result ChanMap -> Result ChanMap
chanFun sig rmap sm cn ss m =
  let sls = Rel.partSet (relatedSorts sig) ss
      m1 = foldr (directChanMap rmap sm cn) m sls
  in case (Map.lookup (CspKindedSymb ChannelKind cn) rmap,
                Map.lookup (CspKindedSymb (CaslKind Implicit) cn) rmap) of
       (Just rsy1, Just rsy2) -> let
          m2 = Set.fold (insertChanSym sm cn rsy1) m1 ss
          in Set.fold (insertChanSym sm cn rsy2) m2 ss
       (Just rsy, Nothing) ->
          Set.fold (insertChanSym sm cn rsy) m1 ss
       (Nothing, Just rsy) ->
          Set.fold (insertChanSym sm cn rsy) m1 ss
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

directChanMap :: CspRawMap -> Sort_map -> Id -> Set.Set SORT
  -> Result ChanMap -> Result ChanMap
directChanMap rmap sm cn ss m =
  let sl = Set.toList ss
      rl = map (\ s -> Map.lookup (ACspSymbol $ toChanSymbol (cn, s)) rmap) sl
      (ms, ps) = partition (isJust . fst) $ zip rl sl
  in case ms of
       l@((Just rsy, _) : rs) ->
         foldr (\ (_, s) ->
           insertChanSym sm cn
              (ACspSymbol $ toChanSymbol
               (rawId rsy, mapSort sm s)) s)
         (foldr (\ (rsy2, s) ->
           insertChanSym sm cn (fromJust rsy2) s) m l)
         $ rs ++ ps
       _ -> m

insertChanSym :: Sort_map -> Id -> CspRawSymbol -> SORT -> Result ChanMap
  -> Result ChanMap
insertChanSym sm cn rsy s m = do
      m1 <- m
      c1 <- mappedChanSym sm cn s rsy
      let ptsy = CspSymbol cn $ ChanAsItemType s
          pos = getRange rsy
          m2 = Map.insert (cn, s) c1 m1
      case Map.lookup (cn, s) m1 of
        Nothing -> if cn == c1 then
            case rsy of
              ACspSymbol _ -> return m1
              _ -> hint m1 ("identity mapping of "
                               ++ showDoc ptsy "") pos
            else return m2
        Just c2 -> if c1 == c2 then
            warning m1
             ("ignoring duplicate mapping of " ++ showDoc ptsy "") pos
            else plain_error m1
             ("conflicting mapping of " ++ showDoc ptsy " to " ++
               show c1 ++ " and " ++ show c2) pos

mappedChanSym :: Sort_map -> Id -> SORT -> CspRawSymbol -> Result Id
mappedChanSym sm cn s rsy =
    let chanSym = "channel symbol " ++ showDoc (toChanSymbol (cn, s))
                  " is mapped to "
    in case rsy of
      ACspSymbol (CspSymbol ide (ChanAsItemType s1)) ->
        let s2 = mapSort sm s
        in if s1 == s2
           then return ide
           else plain_error cn
             (chanSym ++ "sort " ++ showDoc s1
              " but should be mapped to type " ++
              showDoc s2 "") $ getRange rsy
      CspKindedSymb k ide | elem k [CaslKind Implicit, ChannelKind] ->
        return ide
      _ -> plain_error cn
               (chanSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

procFun :: CspCASLSign -> CspRawMap -> Sort_map -> ChanMap -> Id
  -> Set.Set ProcProfile -> Result ProcessMap -> Result ProcessMap
procFun sig rmap sm cm pn ps m =
    let pls = Rel.partSet (relatedProcs sig) ps
        m1 = foldr (directProcMap sig rmap sm cm pn) m pls
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (CspKindedSymb ProcessKind pn) rmap,
                Map.lookup (CspKindedSymb (CaslKind Implicit) pn) rmap) of
       (Just rsy1, Just rsy2) -> let
          m2 = Set.fold (insertProcSym sig sm cm pn rsy1) m1 ps
          in Set.fold (insertProcSym sig sm cm pn rsy2) m2 ps
       (Just rsy, Nothing) ->
          Set.fold (insertProcSym sig sm cm pn rsy) m1 ps
       (Nothing, Just rsy) ->
          Set.fold (insertProcSym sig sm cm pn rsy) m1 ps
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

directProcMap :: CspCASLSign -> CspRawMap -> Sort_map -> ChanMap -> Id ->
  Set.Set ProcProfile -> Result ProcessMap -> Result ProcessMap
directProcMap sig rmap sm cm pn ps m =
  let pl = Set.toList ps
      rl = map (lookupProcSymbol sig rmap pn) pl
      (ms, os) = partition (isJust . fst) $ zip rl pl
  in case ms of
       l@((Just rsy, _) : rs) ->
         foldr (\ (_, p) ->
           insertProcSym sig sm cm pn
              (ACspSymbol $ toProcSymbol
                (rawId rsy, mapProcProfile sm cm p)) p)
         (foldr (\ (rsy2, p) ->
           insertProcSym sig sm cm pn (fromJust rsy2) p) m l)
         $ rs ++ os
       _ -> m

lookupProcSymbol :: CspCASLSign -> CspRawMap -> Id -> ProcProfile
  -> Maybe CspRawSymbol
lookupProcSymbol sig rmap pn p = case
  filter (\ (k, _) -> case k of
    ACspSymbol (CspSymbol i (ProcAsItemType pf)) ->
      i == pn && compatibleProcTypes (Just sig) p pf
    _ -> False) $ Map.toList rmap of
  [(_, r)] -> Just r
  [] -> Nothing
       -- in case of ambiguities try to find an exact match
  l -> lookup (ACspSymbol $ toProcSymbol (pn, p)) l

insertProcSym :: CspCASLSign -> Sort_map -> ChanMap -> Id -> CspRawSymbol
  -> ProcProfile -> Result ProcessMap -> Result ProcessMap
insertProcSym sig sm cm pn rsy pf@(ProcProfile _ al) m = do
      m1 <- m
      (p1, al1) <- mappedProcSym sig sm cm pn pf rsy
      let otsy = toProcSymbol (pn, pf)
          pos = getRange rsy
          m2 = Map.insert (pn, pf) (p1, al1) m1
      case Map.lookup (pn, pf) m1 of
        Nothing -> if pn == p1 && al == al1 then
            case rsy of
              ACspSymbol _ -> return m1
              _ -> hint m1 ("identity mapping of "
                               ++ showDoc otsy "") pos
            else return m2
        Just (p2, al2) -> if p1 == p2 then
             warning (if al1 /= al2 then m2 else m1)
             ("ignoring duplicate mapping of " ++ showDoc otsy "")
             pos
            else plain_error m1
             ("conflicting mapping of " ++ showDoc otsy " to " ++
               show p1 ++ " and " ++ show p2) pos

mappedProcSym :: CspCASLSign -> Sort_map -> ChanMap -> Id -> ProcProfile
  -> CspRawSymbol -> Result (Id, CommAlpha)
mappedProcSym sig sm cm pn pf rsy =
    let procSym = "process symbol " ++ showDoc (toProcSymbol (pn, pf))
                " is mapped to "
        pf2@(ProcProfile _ al2) = mapProcProfile sm cm pf
    in case rsy of
      ACspSymbol (CspSymbol ide (ProcAsItemType pf1@(ProcProfile _ al1))) ->
        if compatibleProcTypes (Just sig) pf1 pf2
           then return (ide, al1)
           else plain_error (pn, al2)
             (procSym ++ "type " ++ showDoc pf1
              " but should be mapped to type " ++
              showDoc pf2 "") $ getRange rsy
      CspKindedSymb k ide | elem k [CaslKind Implicit, ProcessKind] ->
        return (ide, al2)
      _ -> plain_error (pn, al2)
               (procSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

compatibleProcTypes :: Maybe CspCASLSign -> ProcProfile -> ProcProfile -> Bool
compatibleProcTypes msig (ProcProfile l1 al1) (ProcProfile l2 al2) =
  l1 == l2 && relatedCommAlpha (fromMaybe emptyCspCASLSign msig) al1 al2

cspMatches :: CspSymbol -> CspRawSymbol -> Bool
cspMatches (CspSymbol i t) rsy = case rsy of
  ACspSymbol (CspSymbol j t2) -> i == j && case (t, t2) of
    (CaslSymbType t1, CaslSymbType t3) -> matches (Symbol i t1)
      $ ASymbol $ Symbol j t3
    (ChanAsItemType s1, ChanAsItemType s2) -> s1 == s2
    (ProcAsItemType p1, ProcAsItemType p2) -> compatibleProcTypes Nothing p1 p2
    _ -> False
  CspKindedSymb k j -> let res = i == j in case (k, t) of
    (CaslKind ck, CaslSymbType t1) -> matches (Symbol i t1)
      $ AKindedSymb ck j
    (ChannelKind, ChanAsItemType _) -> res
    (ProcessKind, ProcAsItemType _) -> res
    (CaslKind Implicit, _) -> res
    _ -> False

commType2Sort :: CommType -> SORT
commType2Sort c = case c of
  CommTypeSort s -> s
  CommTypeChan (TypedChanName _ s) -> s

procProfile2Sorts :: ProcProfile -> Set.Set SORT
procProfile2Sorts (ProcProfile sorts al) =
  Set.union (Set.fromList sorts) $ Set.map commType2Sort al

cspRevealSym :: CspSymbol -> CspCASLSign -> CspCASLSign
cspRevealSym sy sig = let
  n = cspSymName sy
  ss = sortSet sig
  ext = extendedInfo sig
  cs = chans ext
  in case cspSymbType sy of
    CaslSymbType t -> revealSym (Symbol n t) sig
    ChanAsItemType s -> sig
      { sortSet = Set.insert s ss
      , extendedInfo = ext { chans = Rel.setInsert n s cs }}
    ProcAsItemType p@(ProcProfile _ al) -> sig
      { sortSet = Set.fold Set.insert ss $ procProfile2Sorts p
      , extendedInfo = ext
        { chans = Set.fold (\ ct -> case ct of
            CommTypeSort _ -> id
            CommTypeChan (TypedChanName c s) -> Rel.setInsert c s) cs al
        , procSet = Rel.setInsert n p $ procSet ext }
      }

cspGeneratedSign :: Set.Set CspSymbol -> CspCASLSign -> Result CspCASLMorphism
cspGeneratedSign sys sigma = let
  symset = Set.unions $ symSets sigma
  sigma1 = Set.fold cspRevealSym sigma
    { sortSet = Set.empty
    , opMap = Map.empty
    , predMap = Map.empty
    , extendedInfo = emptyCspSign } sys
  sigma2 = sigma1
    { sortRel = sortRel sigma `Rel.restrict` sortSet sigma1
    , emptySortSet = Set.intersection (sortSet sigma1) $ emptySortSet sigma }
  in if not $ Set.isSubsetOf sys symset
   then let diffsyms = sys Set.\\ symset in
        fatal_error ("Revealing: The following symbols "
                     ++ showDoc diffsyms " are not in the signature")
        $ getRange diffsyms
   else cspSubsigInclusion sigma2 sigma

cspCogeneratedSign :: Set.Set CspSymbol -> CspCASLSign -> Result CspCASLMorphism
cspCogeneratedSign symset sigma = let
  symset0 = Set.unions $ symSets sigma
  symset1 = Set.fold cspHideSym symset0 symset
  in if Set.isSubsetOf symset symset0
   then cspGeneratedSign symset1 sigma
   else let diffsyms = symset Set.\\ symset0 in
        fatal_error ("Hiding: The following symbols "
            ++ showDoc diffsyms " are not in the signature")
        $ getRange diffsyms

cspHideSym :: CspSymbol -> Set.Set CspSymbol -> Set.Set CspSymbol
cspHideSym sy set1 = let
  set2 = Set.delete sy set1
  n = cspSymName sy
  in case cspSymbType sy of
  CaslSymbType SortAsItemType ->
    Set.filter (not . cspProfileContains n . cspSymbType) set2
  ChanAsItemType s ->
    Set.filter (unusedChan n s) set2
  _ -> set2

cspProfileContains :: Id -> CspSymbType -> Bool
cspProfileContains s ty = case ty of
  CaslSymbType t -> profileContainsSort s t
  ChanAsItemType s2 -> s == s2
  ProcAsItemType p -> Set.member s $ procProfile2Sorts p

unusedChan :: Id -> SORT -> CspSymbol -> Bool
unusedChan c s sy = case cspSymbType sy of
  ProcAsItemType (ProcProfile _ al) ->
    Set.fold (\ ct b -> case ct of
       CommTypeSort _ -> b
       CommTypeChan (TypedChanName c2 s2) -> b && (c, s) /= (c2, s2)) True al
  _ -> True
