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

module Static.ApplyChanges where

import Static.DevGraph
import Static.History

import Data.Graph.Inductive.Graph as Graph

import Control.Monad

import Static.FromXml
import Debug.Trace

lookupNodeByNodeName :: NodeName -> DGraph -> [LNode DGNodeLab]
lookupNodeByNodeName nn = lookupNodeWith ((== nn) . dgn_name . snd)

applyChange :: Monad m => SelChangeDG -> DGraph -> m DGraph
applyChange (SelChangeDG se ch) dg = case ch of
  RemoveChDG -> remove se dg
  UpdateChDG str -> update str se dg
  AddChDG _ ls  ->
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
    _ ->
      trace ("ignore adding: " ++ show ch
             ++ "\nat: " ++ show se)
      $ return dg

remove :: Monad m => SelElem -> DGraph -> m DGraph
remove se dg = let err = "Static.ApplyChanges.remove: " in case se of
  NodeElem nn m -> let s = showName nn in case m of
    Nothing -> case lookupNodeByNodeName nn dg of
      [i] -> return $ changeDGH dg (DeleteNode i)
      [] -> trace ("cannot remove: " ++ s) $ return dg -- assume node is gone
      _ -> fail $ err ++ "ambiguous node: " ++ s
    Just nse -> case nse of
       DeclSymbol -> fail $ err ++ "cannot remove node symbols of: " ++ s
       SymbolRangeAttr i ->
          fail $ err ++ "cannot remove symbol range attribute "
            ++ show i ++ " of: " ++ s
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
  _ -> fail $ err ++ "unimplemented selection:\n" ++ show se
