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
  cm <- Map.foldWithKey (chanFun rmap sm)
              (return Map.empty) (chans csig)
  -- compute the process name map (as a Map)
  proc_Map <- Map.foldWithKey (procFun rmap sm cm)
              (return Map.empty) (procSet csig)
  let em = emptyCspAddMorphism
        { channelMap = cm
        , processMap = proc_Map }
  return (embedMorphism em sigma $ closeSortRel
          $ inducedSignAux inducedCspSign sm om pm em sigma)
    { sort_map = sm
    , op_map = om
    , pred_map = pm }

chanFun :: CspRawMap -> Sort_map -> Token -> Set.Set SORT -> Result ChanMap
  -> Result ChanMap
chanFun rmap sm cn ss m =
  -- assume no overload relation
  let sls = map Set.singleton $ Set.toList ss
      m1 = foldr (directChanMap rmap sm cn) m sls
      ide = simpleIdToId cn
  in case (Map.lookup (CspKindedSymb ChannelKind ide) rmap,
                Map.lookup (CspKindedSymb (CaslKind Implicit) ide) rmap) of
       (Just rsy1, Just rsy2) -> let
          m2 = Set.fold (insertChanSym sm cn rsy1) m1 ss
          in Set.fold (insertChanSym sm cn rsy2) m2 ss
       (Just rsy, Nothing) ->
          Set.fold (insertChanSym sm cn rsy) m1 ss
       (Nothing, Just rsy) ->
          Set.fold (insertChanSym sm cn rsy) m1 ss
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

directChanMap :: CspRawMap -> Sort_map -> Token -> Set.Set SORT
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
               (idToSimpleId $ rawId rsy, mapSort sm s)) s)
         (foldr (\ (rsy2, s) ->
           insertChanSym sm cn (fromJust rsy2) s) m l)
         $ rs ++ ps
       _ -> m

insertChanSym :: Sort_map -> Token -> CspRawSymbol -> SORT -> Result ChanMap
  -> Result ChanMap
insertChanSym sm cn rsy s m = do
      m1 <- m
      c1 <- mappedChanSym sm cn s rsy
      let ptsy = CspSymbol (simpleIdToId cn) $ ChanAsItemType s
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

mappedChanSym :: Sort_map -> Token -> SORT -> CspRawSymbol -> Result Token
mappedChanSym sm cn s rsy =
    let chanSym = "channel symbol " ++ showDoc (toChanSymbol (cn, s))
                  " is mapped to "
    in case rsy of
      ACspSymbol (CspSymbol ide (ChanAsItemType s1)) ->
        let s2 = mapSort sm s
        in if s1 == s2
           then return $ idToSimpleId ide
           else plain_error cn
             (chanSym ++ "sort " ++ showDoc s1
              " but should be mapped to type " ++
              showDoc s2 "") $ getRange rsy
      CspKindedSymb k ide | elem k [CaslKind Implicit, ChannelKind] ->
        return $ idToSimpleId ide
      _ -> plain_error cn
               (chanSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

procFun :: CspRawMap -> Sort_map -> ChanMap -> Token -> Set.Set ProcProfile
  -> Result ProcessMap -> Result ProcessMap
procFun rmap sm cm pn ps m =
    let pls = map Set.singleton $ Set.toList ps
        m1 = foldr (directProcMap rmap sm cm pn) m pls
        ide = simpleIdToId pn
    -- now try the remaining ones with (un)kinded raw symbol
    in case (Map.lookup (CspKindedSymb ProcessKind ide) rmap,
                Map.lookup (CspKindedSymb (CaslKind Implicit) ide) rmap) of
       (Just rsy1, Just rsy2) -> let
          m2 = Set.fold (insertProcSym sm cm pn rsy1) m1 ps
          in Set.fold (insertProcSym sm cm pn rsy2) m2 ps
       (Just rsy, Nothing) ->
          Set.fold (insertProcSym sm cm pn rsy) m1 ps
       (Nothing, Just rsy) ->
          Set.fold (insertProcSym sm cm pn rsy) m1 ps
       -- Anything not mapped explicitly is left unchanged
       (Nothing, Nothing) -> m1

directProcMap :: CspRawMap -> Sort_map -> ChanMap -> Token ->
  Set.Set ProcProfile -> Result ProcessMap -> Result ProcessMap
directProcMap rmap sm cm pn ps m =
  let pl = Set.toList ps
      rl = map (lookupProcSymbol rmap pn) pl
      (ms, os) = partition (isJust . fst) $ zip rl pl
  in case ms of
       l@((Just rsy, _) : rs) ->
         foldr (\ (_, p) ->
           insertProcSym sm cm pn
              (ACspSymbol $ toProcSymbol
                (idToSimpleId $ rawId rsy, mapProcProfile sm cm p)) p)
         (foldr (\ (rsy2, p) ->
           insertProcSym sm cm pn (fromJust rsy2) p) m l)
         $ rs ++ os
       _ -> m

lookupProcSymbol :: CspRawMap -> Token -> ProcProfile -> Maybe CspRawSymbol
lookupProcSymbol rmap pn p =
  Map.lookup (ACspSymbol $ toProcSymbol (pn, p)) rmap

insertProcSym :: Sort_map -> ChanMap -> Token -> CspRawSymbol -> ProcProfile
  -> Result ProcessMap -> Result ProcessMap
insertProcSym sm cm pn rsy pf@(ProcProfile _ al) m = do
      m1 <- m
      (p1, al1) <- mappedProcSym sm cm pn pf rsy
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

mappedProcSym :: Sort_map -> ChanMap -> Token -> ProcProfile -> CspRawSymbol
  -> Result (Token, CommAlpha)
mappedProcSym sm cm pn pf@(ProcProfile _ al) rsy =
    let procSym = "process symbol " ++ showDoc (toProcSymbol (pn, pf))
                " is mapped to "
    in case rsy of
      ACspSymbol (CspSymbol ide (ProcAsItemType pf1@(ProcProfile _ al1))) ->
        let pf2 = mapProcProfile sm cm pf
        in if compatibleProcTypes pf1 pf2
           then return (idToSimpleId ide, al1)
           else plain_error (pn, al)
             (procSym ++ "type " ++ showDoc pf1
              " but should be mapped to type " ++
              showDoc pf2 "") $ getRange rsy
      CspKindedSymb k ide | elem k [CaslKind Implicit, ProcessKind] ->
        return (idToSimpleId ide, al)
      _ -> plain_error (pn, al)
               (procSym ++ "symbol of wrong kind: " ++ showDoc rsy "")
               $ getRange rsy

compatibleProcTypes :: ProcProfile -> ProcProfile -> Bool
compatibleProcTypes (ProcProfile l1 a1) (ProcProfile l2 a2) =
  l1 == l2 && (Set.isSubsetOf a1 a2 || Set.isSubsetOf a2 a1)
