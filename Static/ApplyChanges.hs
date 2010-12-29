{- |
Module      :  $Header$
Description :  apply xupdate changes to a development graph
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

adjust development graph according to xupdate information
-}

module Static.ApplyChanges (applyXUpdates) where

import Static.ComputeTheory
import Static.DevGraph
import Static.GTheory
import Static.History
import Static.FromXml

import Logic.Coerce
import Logic.ExtSign
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import Common.AS_Annotation
import Common.DocUtils
import qualified Common.OrderedMap as OMap
import Common.Result
import Common.Utils (readMaybe, atMaybe)
import Common.XUpdate

import Data.Graph.Inductive.Graph as Graph
import qualified Data.Set as Set
import Data.List
import qualified Data.Map as Map

import Control.Monad

import Debug.Trace

lookupNodeByNodeName :: NodeName -> DGraph -> [LNode DGNodeLab]
lookupNodeByNodeName nn = lookupNodeWith ((== nn) . dgn_name . snd)

getNodeByName :: Monad m => String -> NodeName -> DGraph -> m (LNode DGNodeLab)
getNodeByName msg nn dg = let s = showName nn in
  case lookupNodeByNodeName nn dg of
    [] -> fail $ msg ++ "missing node:" ++ s
    [i] -> return i
    _ -> fail $ msg ++ "ambiguous node: " ++ s

applyXUpdates :: Monad m => String -> DGraph -> m DGraph
applyXUpdates xs dg = do
    cs <- anaXUpdates xs
    let acs = foldr (\ c l -> case changeDG c of
          Nothing -> l
          Just s -> s : l) [] cs
    return $ foldr (\ s g -> case applyChange s g of
      Nothing -> g
      Just ng -> ng) dg $ sortBy cmpSelChanges acs

cmpSelChanges :: SelChangeDG -> SelChangeDG -> Ordering
cmpSelChanges (SelChangeDG _ ch1) (SelChangeDG _ ch2) =
  case (ch1, ch2) of
    (RemoveChDG, RemoveChDG) -> EQ
    (RemoveChDG, _) -> LT
    (_, RemoveChDG) -> GT
    _ -> EQ

applyChange :: Monad m => SelChangeDG -> DGraph -> m DGraph
applyChange (SelChangeDG se ch) dg = case ch of
  RemoveChDG -> remove se dg
  UpdateChDG str -> update str se dg
  AddChDG _ ls ->
    foldM (add se) dg ls

add :: Monad m => SelElem -> DGraph -> AddChangeDG -> m DGraph
add se dg ch = case ch of
    SpecEntryDG n _fm ->
      trace ("ignore adding spec entry " ++ show n ++ " to:\n" ++ show se)
      $ return dg
    ViewEntryDG n _fm s t gm ->
      trace ("ignore adding view entry " ++ show n ++ " from " ++ show s
             ++ " to " ++ show t ++ "\n" ++ gm
             ++ "via:\n" ++ show se)
      $ return dg
    NodeDG n _refn _consStatus ds ->
      trace ("ignore adding node " ++ showName n
             ++ " (via:\n" ++ show se ++ ") " ++ show ds)
      $ return dg
    LinkDG e s t _linkTy gm ->
      trace ("ignore adding link " ++ showEdgeId e ++ " from "
             ++ showName s ++ " to " ++ showName t
             ++ "\n" ++ gm
             ++ "\nvia: " ++ show se)
      $ return dg
    StringElem en str -> case en of
      "Symbol" -> addSymbol str se dg
      _ | elem en ["Axiom", "Theorem"] -> addAxOrTh str se dg
      _ -> trace ("ignore adding: " ++ show en ++ "\nat: " ++ show se)
         $ return dg

addSymbol :: Monad m => String -> SelElem -> DGraph -> m DGraph
addSymbol str se dg = let err = "Static.ApplyChanges.addSymbol: " in case se of
  NodeElem nn (Just (DeclSymbol Nothing)) -> do
    (v, lbl) <- getNodeByName err nn dg
    case extendByBasicSpec str (dgn_theory lbl) of
       (Success nGt nSens nSyms _, _) ->
          if nSens == 0 && Set.size nSyms == 1 then let
              newLbl = lbl { dgn_theory = nGt
                           , nodeInfo = case nodeInfo lbl of
                               DGNode (DGBasicSpec _ syms) _ -> newNodeInfo $
                                 DGBasicSpec Nothing $ Set.union nSyms syms
                               i -> i }
              finLbl = newLbl { globalTheory = computeLabelTheory Map.empty dg
                                  (v, newLbl) }
              in return $ changeDGH dg $ SetNodeLab lbl (v, finLbl)
          else fail $ err ++ "just add a single symbol to: " ++ showName nn
       (_, msg) -> fail $ err ++ msg
  _ -> fail $ err ++ "cannot add symbol to: " ++ show se

addAxOrTh :: Monad m => String -> SelElem -> DGraph -> m DGraph
addAxOrTh str se dg = let err = "Static.ApplyChanges.addAxOrTh: " in case se of
  NodeElem nn (Just _) -> do
    (v, lbl) <- getNodeByName err nn dg
    case extendByBasicSpec str (dgn_theory lbl) of
       (Success nGt nSens _ sameSig, msg) -> case nSens of
          1 | sameSig -> let
              newLbl = lbl { dgn_theory = nGt }
              finLbl = newLbl { globalTheory = computeLabelTheory Map.empty dg
                                  (v, newLbl) }
              in return $ changeDGH dg $ SetNodeLab lbl (v, finLbl)
          0 -> fail $ err ++ "missing sentence for: " ++ str
          _ -> fail $ err ++ msg
       (_, msg) -> fail $ err ++ msg
  _ -> fail $ err ++ "cannot add sentence to: " ++ show se

remove :: Monad m => SelElem -> DGraph -> m DGraph
remove se dg = let err = "Static.ApplyChanges.remove: " in case se of
  NodeElem nn m -> do
    i <- getNodeByName err nn dg
    let s = showName nn
    case m of
      Nothing -> return $ changeDGH dg (DeleteNode i)
      Just (DeclSymbol md) -> case md of
        Nothing -> fail $ err ++ "cannot remove all declarations from: " ++ s
        Just (si, b) -> if b then
          trace ("ignore removing symbol attributes from: " ++ s) $ return dg
          else removeNthSymbol si dg i
      Just (Axioms si) -> removeNthAxOrTh True si dg i
      Just (Theorems si) -> removeNthAxOrTh False si dg i
  LinkElem eId src tar m -> let e = showEdgeId eId in case m of
    Nothing ->
      case (lookupNodeByNodeName src dg, lookupNodeByNodeName tar dg) of
      ([s], [t]) -> case filter (\ (_, o, l) -> o == fst t && eId == dgl_id l)
        $ outDG dg (fst s) of
        [le] -> return $ changeDGH dg (DeleteEdge le)
        [] -> fail $ err ++ "edge not found: " ++ e
        _ -> fail $ err ++ "ambiguous edge: " ++ e
      (sl, tl) -> if null sl || null tl
        then trace ("cannot remove link " ++ showEdgeId eId
                    ++ " from " ++ showName src
                    ++ " to " ++ showName tar)
             $ return dg -- assume link is gone
        else fail $ err ++ "non-unique source or target for edge: " ++ e
          ++ "\n" ++ show (map (\ (v, l) -> (v, getDGNodeName l)) $ sl ++ tl)
    Just _ -> fail $ err ++ "cannot remove edge morphisms"
  _ -> fail $ err ++ "unimplemented selection"

update :: Monad m => String -> SelElem -> DGraph -> m DGraph
update str se dg =
  let err = "Static.ApplyChanges.update with: " ++ str ++ "\n"
  in case se of
  NodeElem nn m -> case m of
    Nothing -> let s = showName nn in case lookupNodeByNodeName nn dg of
      [_] -> trace ("update '" ++ str ++ "' is ignored on: " ++ show se)
        $ return dg -- ignore any attribute changes
      [] -> fail $ err ++ "node not found: " ++ s
      _ -> fail $ err ++ "ambiguous node: " ++ s
    Just nse -> fail $ err ++ "cannot remove node symbols\n" ++ show nse
  NextLinkId -> case readMaybe str of
    Just i -> return dg { getNewEdgeId = EdgeId i }
    Nothing -> fail $ err ++ "could not update nextlinkid using: " ++ str
  _ -> fail $ err ++ "unimplemented selection:\n" ++ show se

removeNthSymbol :: Monad m => Int -> DGraph -> LNode DGNodeLab -> m DGraph
removeNthSymbol n dg (v, lbl) = let nn = getDGNodeName lbl in
  case nodeInfo lbl of
  DGRef _ _ -> fail $ "cannot remove symbols from ref-node: " ++ nn
  DGNode orig _ -> case orig of
    DGBasicSpec _ syms -> case atMaybe (Set.toList syms) $ n - 1 of
      Nothing -> fail $ "symbol " ++ show n ++ " not found in node: " ++ nn
        ++ "\n" ++ showDoc syms ""
      Just gs@(G_symbol lid sym) -> case dgn_theory lbl of
        G_theory lid2 sig _ sens _ ->
          let Result ds mr = ext_cogenerated_sign lid2
                (Set.singleton $ coerceSymbol lid lid2 sym) sig
          in case mr of
            Nothing -> fail $ "hiding " ++ showDoc sym " in " ++ nn ++
              " failed:\n" ++ showRelDiags 1 ds
            Just mor -> let
              newLbl = lbl { dgn_theory = G_theory lid2
                               (makeExtSign lid2 $ dom mor) startSigId
                               sens startThId
                           , nodeInfo = newNodeInfo $
                                DGBasicSpec Nothing $ Set.delete gs syms }
              finLbl = newLbl { globalTheory = computeLabelTheory Map.empty dg
                                  (v, newLbl) }
              in return $ changeDGH dg $ SetNodeLab lbl (v, finLbl)
    _ -> fail $ "cannot remove symbol from non-basic-spec node: " ++ nn

removeNthAxOrTh :: Monad m => Bool -> Int -> DGraph -> LNode DGNodeLab
  -> m DGraph
removeNthAxOrTh b n dg (v, lbl) = let nn = getDGNodeName lbl in
  case dgn_theory lbl of
        G_theory lid sig si thsens _ -> let
          sens = toNamedList $ OMap.filter ((if b then id else not) . isAxiom)
                thsens
          in case atMaybe sens $ n - 1 of
          Nothing -> fail $ "sentence " ++ show n ++ " not found in node: "
            ++ nn ++ "\n" ++ intercalate ", " (map senAttr sens)
          Just ns -> let
            newLbl = lbl { dgn_theory = G_theory lid sig si
                           (Map.delete (senAttr ns) thsens) startThId }
            finLbl = newLbl { globalTheory = computeLabelTheory Map.empty dg
                                  (v, newLbl) }
            in return $ changeDGH dg $ SetNodeLab lbl (v, finLbl)
