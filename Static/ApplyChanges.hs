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

import Static.FromXml

lookupNodeByNodeName :: NodeName -> DGraph -> [LNode DGNodeLab]
lookupNodeByNodeName nn = lookupNodeWith ((== nn) . dgn_name . snd)

applyChange :: Monad m => SelChangeDG -> DGraph -> m DGraph
applyChange (SelChangeDG se ch) dg = case ch of
  RemoveChDG -> remove se dg
  UpdateChDG str -> update str se dg
  _ -> fail "applyChange.unimplemented ChangeDG"

remove :: Monad m => SelElem -> DGraph -> m DGraph
remove se dg = let err = "Static.ApplyChanges.remove: " in case se of
  NodeElem nn m -> case m of
    Nothing -> let s = showName nn in case lookupNodeByNodeName nn dg of
      [i] -> return $ changeDGH dg (DeleteNode i)
      [] -> return dg -- assume node is gone
      _ -> fail $ err ++ "ambiguous node: " ++ s
    Just _ -> fail $ err ++ "cannot remove node symbols"
  LinkElem eId src tar m -> let e = showEdgeId eId in case m of
    Nothing ->
      case (lookupNodeByNodeName src dg, lookupNodeByNodeName tar dg) of
      ([s], [t]) -> case filter (\ (_, o, l) -> o == fst t && eId == dgl_id l)
        $ outDG dg (fst s) of
        [le] -> return $ changeDGH dg (DeleteEdge le)
        [] -> fail $ err ++ "edge not found: " ++ e
        _ -> fail $ err ++ "ambiguous edge: " ++ e
      (sl, tl) -> if null sl || null tl then return dg -- assume link is gone
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
      [_] -> return dg -- ignore any attribute changes
      [] -> fail $ err ++ "node not found: " ++ s
      _ -> fail $ err ++ "ambiguous node: " ++ s
    Just _ -> fail $ err ++ "cannot remove node symbols"
  _ -> fail $ err ++ "unimplemented selection"
