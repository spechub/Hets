{- |
Module      :  $Header$
Description :  qualify all names in the nodes of development graphs
Copyright   :  (c) Igor Stassiy, C.Maeder DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

qualify and disambiguate all names in the nodes of a development graph for
OMDoc output or for writing out multiple theories for Isabelle or VSE.  Note
however that signature will be always be complete, i.e. imported entities
will be repeated.
-}

module Proofs.QualifyNames where

import Proofs.EdgeUtils

import Logic.Coerce
import Logic.Comorphism
import Logic.ExtSign
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import Static.DevGraph
import Static.GTheory

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

mapWithKeyM :: (Ord k, Monad m) => (k -> a -> m b) -> Map.Map k a
            -> m (Map.Map k b)
mapWithKeyM f = foldM (\ m (k, a) -> do
   b <- f k a
   return $ Map.insert k b m) Map.empty . Map.toList

qualifyLibEnv :: LibEnv -> Result LibEnv
qualifyLibEnv = mapWithKeyM qualifyDGraph

qualifyDGraph :: LIB_NAME -> DGraph -> Result DGraph
qualifyDGraph ln dg =
  addErrorDiag "qualification failed for" (getLIB_ID ln)
  $ do
  let es = map (\ (_, _, lb) -> dgl_id lb) $ labEdgesDG dg
  unless (Set.size (Set.fromList es) == length es) $
    fail $ "inkonsistent graph for library " ++ showDoc ln ""
  dg1 <- foldM (qualifyLabNode ln) dg $ topsortedNodes dg
  return $ groupHistory dg (DGRule "Qualified-Names") dg1

-- consider that loops are part of innDG and outDG that should not be handled
-- twice

constructUnion :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
            lid -> morphism -> [morphism] -> morphism
constructUnion lid hd l = case l of
  [] -> hd
  sd : tl -> case maybeResult $ morphism_union lid hd sd of
    Just m -> constructUnion lid m tl
    Nothing -> constructUnion lid sd tl

qualifyLabNode :: LIB_NAME -> DGraph -> LNode DGNodeLab
               -> Result DGraph
qualifyLabNode ln dg (n, lb) = let
  noLoop (x, y, _) = x /= y
  inss = filter noLoop $ innDG dg n
  allOuts = outDG dg n in
  case dgn_theory lb of
    G_theory lid (ExtSign sig _) _ sens _ -> do
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
                       (getLIB_ID ln) m sig
        rm <- inverse m1
        nThSens <- mapThSensValueM (map_sen lid m1) sens
        let nlb = lb { dgn_theory = G_theory lid
                       (makeExtSign lid (cod m1)) startSigId
                       (joinSens nThSens $ toThSens osens) startThId }
        gm1 <- return $ gEmbed $ G_morphism lid m1 startMorId
        grm <- return $ gEmbed $ G_morphism lid rm startMorId
        nAllouts <- mapM (composeWithMorphism False gm1 grm) allOuts
        let (nouts, nloops) = partition noLoop nAllouts
        nAllinss <- mapM (composeWithMorphism True gm1 grm) $ nloops ++ inss
        return $ changesDGH dg $ map DeleteEdge (allOuts ++ inss)
              ++ SetNodeLab lb (n, nlb) : map InsertEdge (nAllinss ++ nouts)

-- consider that hiding edges have a reverse morphism

composeWithMorphism :: Bool -> GMorphism -> GMorphism -> LEdge DGLinkLab
                    -> Result (LEdge DGLinkLab)
composeWithMorphism dir mor rmor (s, t, lb) = do
    let lmor = dgl_morphism lb
    nmor <- if dir /= isHidingEdge (dgl_type lb)
            then comp lmor mor else comp rmor lmor
    return (s, t, lb { dgl_morphism = nmor})
