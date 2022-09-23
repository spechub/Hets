{- |
Module      :  ./Proofs/QualifyNames.hs
Description :  qualify all names in the nodes of development graphs
Copyright   :  (c) Igor Stassiy, C.Maeder DFKI Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

qualify and disambiguate all names in the nodes of a development graph for
OMDoc output or for writing out multiple theories for Isabelle or VSE.  Note
however that signature will be always be complete, i.e. imported entities
will be repeated.
-}

module Proofs.QualifyNames (qualifyLibEnv) where

import Logic.Coerce
import Logic.Comorphism
import Logic.ExtSign
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import Static.DevGraph
import Static.DgUtils
import Static.GTheory
import Static.History
import Static.ComputeTheory

import Common.DocUtils
import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result

import Data.Graph.Inductive.Graph
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad
import qualified Control.Monad.Fail as Fail

qualifyLibEnv :: LibEnv -> Result LibEnv
qualifyLibEnv libEnv = fmap fst
  $ foldM (\ (le, m) ln -> do
    dg0 <- updateRefNodes (le, m) $ lookupDGraph ln le
    (dg, trm) <- qualifyDGraph ln dg0
    return ( Map.insert ln (computeDGraphTheories le ln dg) le
           , Map.insert ln trm m))
    (libEnv, Map.empty) $ getTopsortedLibs libEnv

type RenameMap = Map.Map Int (GMorphism, GMorphism)

qualifyDGraph :: LibName -> DGraph -> Result (DGraph, RenameMap)
qualifyDGraph ln dg =
  addErrorDiag "qualification failed for" ln
  $ do
  let es = map (\ (_, _, lb) -> dgl_id lb) $ labEdgesDG dg
  unless (Set.size (Set.fromList es) == length es) $
    Fail.fail $ "inkonsistent graph for library " ++ showDoc ln ""
  (dg1, trm) <- foldM (qualifyLabNode ln) (dg, Map.empty) $ topsortedNodes dg
  return (groupHistory dg (DGRule "Qualified-Names") dg1, trm)

{- consider that loops are part of innDG and outDG that should not be handled
   twice -}
properEdge :: LEdge a -> Bool
properEdge (x, y, _) = x /= y

properInEdges :: DGraph -> Node -> [LEdge DGLinkLab]
properInEdges dg n =
  let pes = filter properEdge $ innDG dg n
      (gs, rs) = partition (liftE isGlobalDef) pes
  in gs ++ rs

constructUnion :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
            lid -> morphism -> [morphism] -> morphism
constructUnion lid hd l = case l of
  [] -> hd
  sd : tl -> case maybeResult $ morphism_union lid hd sd of
    Just m -> case maybeResult $ inverse m of
      Just _ -> constructUnion lid m tl
      Nothing -> constructUnion lid sd tl
    Nothing -> constructUnion lid sd tl

updateRefNodes :: (LibEnv, Map.Map LibName RenameMap) -> DGraph
               -> Result DGraph
updateRefNodes (le, trm) dgraph =
  foldM (\ dg (n, lb) ->
     if isDGRef lb then do
     let refLn = dgn_libname lb
         refNode = dgn_node lb
         gp = Map.findWithDefault (error "updateRefNodes2") refNode
           $ Map.findWithDefault (error "updateRefNodes1") refLn trm
         refGr = lookupDGraph refLn le
         gth = dgn_theory $ labDG refGr refNode
         newlb = lb { dgn_theory = createGThWith gth startSigId startThId }
     (ds, is) <- createChanges dg n (properInEdges dg n) gp
     return $ changesDGH dg $ ds ++ SetNodeLab lb (n, newlb) : is
     else return dg) dgraph $ labNodesDG dgraph

createChanges :: DGraph -> Node -> [LEdge DGLinkLab] -> (GMorphism, GMorphism)
              -> Result ([DGChange], [DGChange])
createChanges dg n inss (gm1, grm) = do
  let allOuts = outDG dg n
  nAllouts <- mapM (composeWithMorphism False gm1 grm) allOuts
  let (nouts, nloops) = partition properEdge nAllouts
  nAllinss <- mapM (composeWithMorphism True gm1 grm) $ nloops ++ inss
  return (map DeleteEdge $ allOuts ++ inss, map InsertEdge $ nAllinss ++ nouts)

qualifyLabNode :: LibName -> (DGraph, RenameMap) -> LNode DGNodeLab
               -> Result (DGraph, RenameMap)
qualifyLabNode ln (dg, mormap) (n, lb) =
   if isDGRef lb then return (dg, mormap) else case dgn_theory lb of
    G_theory lid syn (ExtSign sig _) _ sens _ -> do
        let inss = properInEdges dg n
        hins <- foldM (\ l (GMorphism cid _ _ mor _) ->
            if isIdComorphism (Comorphism cid) && language_name lid ==
               language_name (targetLogic cid) then do
                hmor <- coerceMorphism (targetLogic cid) lid
                        "qualifyLabNode" mor
                return $ hmor : l
            else return l) [] $ map (\ (_, _, ld) -> dgl_morphism ld) inss
        let revHins = mapMaybe (maybeResult . inverse) hins
            m = case revHins of
                  [] -> ide sig
                  hd : tl -> constructUnion lid hd tl
        (m1, osens) <- qualify lid (mkSimpleId $ getDGNodeName lb)
                       ln m sig
        rm <- inverse m1
        nThSens <- mapThSensValueM (map_sen lid m1) $ joinSens sens
          $ toThSens osens
        let nlb = lb { dgn_theory = G_theory lid syn
                       (makeExtSign lid (cod m1)) startSigId
                       nThSens startThId }
            gp = ( gEmbed $ G_morphism lid m1 startMorId
                 , gEmbed $ G_morphism lid rm startMorId)
        (ds, is) <- createChanges dg n inss gp
        return ( changesDGH dg $ ds ++ SetNodeLab lb (n, nlb) : is
               , Map.insert n gp mormap)

{- consider that hiding definition links have a reverse morphism
and hiding theorems are also special -}
composeWithMorphism :: Bool -> GMorphism -> GMorphism -> LEdge DGLinkLab
                    -> Result (LEdge DGLinkLab)
composeWithMorphism dir mor rmor (s, t, lb) = do
    let lmor = dgl_morphism lb
        inmor = comp lmor mor
        outmor = comp rmor lmor
    nlb <- addErrorDiag
      ((if dir then "in" else "out") ++ "-edge " ++ show (s, t, dgl_id lb)) ()
      $ case dgl_type lb of
        HidingDefLink -> do
          nmor <- if dir then outmor else inmor
          return lb { dgl_morphism = nmor }
        HidingFreeOrCofreeThm {} ->
          -- adjusting the morphisms here is more tricky and omitted for now
          return lb
        _ -> do
          nmor <- if dir then inmor else outmor
          return lb { dgl_morphism = nmor }
    return (s, t, nlb)
