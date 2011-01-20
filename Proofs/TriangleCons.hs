{- |
Module      :  $Header$
Description :  apply triangle-cons rule for all edges in development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

-}


module Proofs.TriangleCons where


--import Logic.Grothendieck

import Static.DevGraph
import Static.History

import Common.Consistency
import Common.Result
import Common.LibName

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Graph.Inductive.Graph

import Control.Monad

triangleConsRule :: DGRule
triangleConsRule = DGRule "TriangleCons"

triangleCons :: LibName -> LibEnv -> Result LibEnv
triangleCons ln le = do
 let dg = lookupDGraph ln le
 newDg <- foldM triangleConsDG dg $ 
             filter (\ (_, _, l) -> let e = getRealDGLinkType l in
               edgeTypeModInc e == GlobalDef
               && getCons (dgl_type l) == Cons
             )
          $ labEdgesDG dg 
 return $ Map.insert ln
    (groupHistory dg triangleConsRule newDg) le

triangleConsDG :: DGraph -> LEdge DGLinkLab -> Result DGraph
triangleConsDG dg (s,t,l) = do
 let g = dgBody dg
     markCons l1 l2= let
        l' = l{dgl_type = case dgl_type l of
                           ScopedLink a b _ ->
                              ScopedLink a b $
                               ConsStatus 
                                 Cons
                                 Cons
                                 $ Proven triangleConsRule $ 
                                    ProofBasis $ Set.fromList $ 
                                     map dgl_id [l1, l2]
                           dt -> dt}
       in [DeleteEdge (s,t,l), InsertEdge (s,t,l')]
     checkThm eType = 
       case eType of 
         ThmType (GlobalOrLocalThm _ _) _ _ _ -> True
         _ -> False
     oThm  = filter (\ (_, _, ll) -> let e = getRealDGLinkType ll in
               checkThm (edgeTypeModInc e)
             ) $ out g t
 case oThm of 
   [] -> return dg -- no outgoing thm link found
   _ -> do
    let bases = filter (\((s',_,_), _) -> s == s') 
                $ concatMap (\dge@(_, tt, _) -> 
                        map (\x-> (x,dge)) 
                         $ filter (\ (_, _, lx) -> 
                           let e = getRealDGLinkType lx in
                             edgeTypeModInc e == GlobalDef
                             && getCons (dgl_type lx) == Cons
                           ) $ inn g tt)
                  oThm
    case bases of
      [] -> return dg -- no cons link found
      ((_, _, cl), (_, _, tl)):_ -> do
        let changes = markCons cl tl
        return $ changesDGH dg changes
       --error "nyi"    
