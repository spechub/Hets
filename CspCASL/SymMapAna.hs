{- |
Module      :  ./CspCASL/SymMapAna.hs
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
import Common.ExtSign
import Common.Id
import Common.Result
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List (partition)
import Data.Maybe

type CspRawMap = Map.Map CspRawSymbol CspRawSymbol

cspInducedFromToMorphism :: CspRawMap -> ExtSign CspCASLSign CspSymbol
  -> ExtSign CspCASLSign CspSymbol -> Result CspCASLMorphism
cspInducedFromToMorphism rmap (ExtSign sSig sy) (ExtSign tSig tSy) =
  let (crm, rm) = splitSymbolMap rmap
  in if Map.null rm then
         inducedFromToMorphismExt inducedCspSign
         (constMorphExt emptyCspAddMorphism)
         composeMorphismExtension isCspSubSign diffCspSig
         crm (ExtSign sSig $ getCASLSymbols sy)
         $ ExtSign tSig $ getCASLSymbols tSy
     else do
       mor <- cspInducedFromMorphism rmap sSig
       let iSig = mtarget mor
       if isSubSig isCspSubSign iSig tSig then do
          incl <- sigInclusion emptyCspAddMorphism iSig tSig
          composeM composeMorphismExtension mor incl
         else
           fatal_error
         ("No signature morphism for csp symbol map found.\n" ++
          "The following mapped symbols are missing in the target signature:\n"
          ++ showDoc (diffSig diffCspSig iSig tSig) "")
          $ concatMapRange getRange $ Map.keys rmap

cspInducedFromMorphism :: CspRawMap -> CspCASLSign -> Result CspCASLMorphism
cspInducedFromMorphism rmap sigma = do
  let (crm, _) = splitSymbolMap rmap
  m <- inducedFromMorphism emptyCspAddMorphism crm sigma
  let sm = sort_map m
      om = op_map m
      pm = pred_map m
      csig = extendedInfo sigma
      newSRel = Rel.transClosure . sortRel $ mtarget m
  -- compute the channel name map (as a Map)
  cm <- Map.foldrWithKey (chanFun sigma rmap sm)
              (return Map.empty) (MapSet.toMap $ chans csig)
  -- compute the process name map (as a Map)
  proc_Map <- Map.foldrWithKey (procFun sigma rmap sm newSRel cm)
              (return Map.empty) (MapSet.toMap $ procSet csig)
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

procFun :: CspCASLSign -> CspRawMap -> Sort_map -> Rel.Rel SORT -> ChanMap -> Id
  -> Set.Set ProcProfile -> Result ProcessMap -> Result ProcessMap
procFun sig rmap sm rel cm pn ps m =
    let pls = Rel.partSet (relatedProcs sig) ps
        m1 = foldr (directProcMap rmap sm rel cm pn) m pls
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (CspKindedSymb ProcessKind pn) rmap,
                Map.lookup (CspKindedSymb (CaslKind Implicit) pn) rmap) of
       (Just rsy1, Just rsy2) -> let
          m2 = Set.fold (insertProcSym sm rel cm pn rsy1) m1 ps
          in Set.fold (insertProcSym sm rel cm pn rsy2) m2 ps
       (Just rsy, Nothing) ->
          Set.fold (insertProcSym sm rel cm pn rsy) m1 ps
       (Nothing, Just rsy) ->
          Set.fold (insertProcSym sm rel cm pn rsy) m1 ps
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

directProcMap :: CspRawMap -> Sort_map -> Rel.Rel SORT -> ChanMap
  -> Id -> Set.Set ProcProfile -> Result ProcessMap -> Result ProcessMap
directProcMap rmap sm rel cm pn ps m =
  let pl = Set.toList ps
      rl = map (lookupProcSymbol rmap pn) pl
      (ms, os) = partition (isJust . fst) $ zip rl pl
  in case ms of
       l@((Just rsy, _) : rs) ->
         foldr (\ (_, p) ->
           insertProcSym sm rel cm pn
              (ACspSymbol $ toProcSymbol
                (rawId rsy, mapProcProfile sm cm p)) p)
         (foldr (\ (rsy2, p) ->
           insertProcSym sm rel cm pn (fromJust rsy2) p) m l)
         $ rs ++ os
       _ -> m

lookupProcSymbol :: CspRawMap -> Id -> ProcProfile
  -> Maybe CspRawSymbol
lookupProcSymbol rmap pn p = case
  filter (\ (k, _) -> case k of
    ACspSymbol (CspSymbol i (ProcAsItemType pf)) ->
      i == pn && matchProcTypes p pf
    _ -> False) $ Map.toList rmap of
  [(_, r)] -> Just r
  [] -> Nothing
       -- in case of ambiguities try to find an exact match
  l -> lookup (ACspSymbol $ toProcSymbol (pn, p)) l

insertProcSym :: Sort_map -> Rel.Rel SORT -> ChanMap -> Id -> CspRawSymbol
  -> ProcProfile -> Result ProcessMap -> Result ProcessMap
insertProcSym sm rel cm pn rsy pf@(ProcProfile _ al) m = do
      m1 <- m
      (p1, al1) <- mappedProcSym sm rel cm pn pf rsy
      let otsy = toProcSymbol (pn, pf)
          pos = getRange rsy
          m2 = Map.insert (pn, pf) p1 m1
      case Map.lookup (pn, pf) m1 of
        Nothing -> if pn == p1 && al == al1 then
            case rsy of
              ACspSymbol _ -> return m1
              _ -> hint m1 ("identity mapping of "
                               ++ showDoc otsy "") pos
            else return m2
        Just p2 -> if p1 == p2 then
             warning m1
             ("ignoring duplicate mapping of " ++ showDoc otsy "")
             pos
            else plain_error m1
             ("conflicting mapping of " ++ showDoc otsy " to " ++
               show p1 ++ " and " ++ show p2) pos

mappedProcSym :: Sort_map -> Rel.Rel SORT -> ChanMap -> Id
  -> ProcProfile -> CspRawSymbol -> Result (Id, CommAlpha)
mappedProcSym sm rel cm pn pfSrc rsy =
    let procSym = "process symbol " ++ showDoc (toProcSymbol (pn, pfSrc))
                " is mapped to "
        pfMapped@(ProcProfile _ al2) = reduceProcProfile rel
          $ mapProcProfile sm cm pfSrc
    in case rsy of
      ACspSymbol (CspSymbol ide (ProcAsItemType pf)) ->
        let pfTar@(ProcProfile _ al1) = reduceProcProfile rel pf
        in if compatibleProcTypes rel pfMapped pfTar
           then return (ide, al1)
           else plain_error (pn, al2)
             (procSym ++ "type " ++ showDoc pfTar
              "\nbut should be mapped to type " ++
              showDoc pfMapped
              "\npossibly using a sub-alphabet of " ++
              showDoc (closeCspCommAlpha rel al2) ".")
             $ getRange rsy
      CspKindedSymb k ide | elem k [CaslKind Implicit, ProcessKind] ->
        return (ide, al2)
      _ -> plain_error (pn, al2)
               (procSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

compatibleProcTypes :: Rel.Rel SORT -> ProcProfile -> ProcProfile -> Bool
compatibleProcTypes rel (ProcProfile l1 al1) (ProcProfile l2 al2) =
  l1 == l2 && liamsRelatedCommAlpha rel al1 al2

liamsRelatedCommAlpha :: Rel.Rel SORT -> CommAlpha -> CommAlpha -> Bool
liamsRelatedCommAlpha rel al1 al2 =
  all (\ a2 -> any (\ a1 -> liamsRelatedCommTypes rel a1 a2) $ Set.toList al1)
  $ Set.toList al2

liamsRelatedCommTypes :: Rel.Rel SORT -> CommType -> CommType -> Bool
liamsRelatedCommTypes rel ct1 ct2 = case (ct1, ct2) of
  (CommTypeSort s1, CommTypeSort s2)
    -> s1 == s2 || s1 `Set.member` Rel.succs rel s2
  (CommTypeChan (TypedChanName c1 s1), CommTypeChan (TypedChanName c2 s2))
    -> c1 == c2 && s1 == s2
  _ -> False

matchProcTypes :: ProcProfile -> ProcProfile -> Bool
matchProcTypes (ProcProfile l1 al1) (ProcProfile l2 al2) = l1 == l2
  && (Set.null al2 || Set.null al1 || not (Set.null $ Set.intersection al1 al2))

cspMatches :: CspSymbol -> CspRawSymbol -> Bool
cspMatches (CspSymbol i t) rsy = case rsy of
  ACspSymbol (CspSymbol j t2) -> i == j && case (t, t2) of
    (CaslSymbType t1, CaslSymbType t3) -> matches (Symbol i t1)
      $ ASymbol $ Symbol j t3
    (ChanAsItemType s1, ChanAsItemType s2) -> s1 == s2
    (ProcAsItemType p1, ProcAsItemType p2) -> matchProcTypes p1 p2
    _ -> False
  CspKindedSymb k j -> let res = i == j in case (k, t) of
    (CaslKind ck, CaslSymbType t1) -> matches (Symbol i t1)
      $ AKindedSymb ck j
    (ChannelKind, ChanAsItemType _) -> res
    (ProcessKind, ProcAsItemType _) -> res
    (CaslKind Implicit, _) -> res
    _ -> False

procProfile2Sorts :: ProcProfile -> Set.Set SORT
procProfile2Sorts (ProcProfile sorts al) =
  Set.union (Set.fromList sorts) $ Set.map commType2Sort al

cspRevealSym :: CspSymbol -> CspCASLSign -> CspCASLSign
cspRevealSym sy sig = let
  n = cspSymName sy
  r = sortRel sig
  ext = extendedInfo sig
  cs = chans ext
  in case cspSymbType sy of
    CaslSymbType t -> revealSym (Symbol n t) sig
    ChanAsItemType s -> sig
      { sortRel = Rel.insertKey s r
      , extendedInfo = ext { chans = MapSet.insert n s cs }}
    ProcAsItemType p@(ProcProfile _ al) -> sig
      { sortRel = Rel.union (Rel.fromKeysSet $ procProfile2Sorts p) r
      , extendedInfo = ext
        { chans = Set.fold (\ ct -> case ct of
            CommTypeSort _ -> id
            CommTypeChan (TypedChanName c s) -> MapSet.insert c s) cs al
        , procSet = MapSet.insert n p $ procSet ext }
      }

cspGeneratedSign :: Set.Set CspSymbol -> CspCASLSign -> Result CspCASLMorphism
cspGeneratedSign sys sigma = let
  symset = Set.unions $ symSets sigma
  sigma1 = Set.fold cspRevealSym sigma
    { sortRel = Rel.empty
    , opMap = MapSet.empty
    , predMap = MapSet.empty
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
