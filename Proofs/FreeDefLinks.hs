{- |
Module      :  $Header$
Description :  compute ingoing free definition links for provers
Copyright   :  C. Maeder DFKI GmbH 2010
License     :  GPLv2 or higher
Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(Logic)

compute ingoing free definition links for provers
-}

module Proofs.FreeDefLinks where

import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory

import Proofs.EdgeUtils

import Common.ExtSign
import Common.LibName
import Common.AS_Annotation
import qualified Common.Lib.Graph as Tree

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck
import Logic.Comorphism
import Logic.Coerce

import Data.Graph.Inductive.Basic (elfilter)
import Data.Graph.Inductive.Graph
import Data.Maybe

getCFreeDefLinks :: DGraph -> Node
                        -> ([[LEdge DGLinkLab]], [[LEdge DGLinkLab]])
getCFreeDefLinks dg tgt =
  let isGlobalOrCFreeEdge = liftOr isGlobalEdge $ liftOr isFreeEdge isCofreeEdge
      paths = map reverse $ Tree.getAllPathsTo tgt
        $ elfilter (isGlobalOrCFreeEdge . dgl_type) $ dgBody dg
      myfilter p = filter ( \ ((_, _, lbl) : _) -> p $ dgl_type lbl)
  in (myfilter isFreeEdge paths, myfilter isCofreeEdge paths)

mkFreeDefMor :: [Named sentence] -> morphism -> morphism
                -> FreeDefMorphism sentence morphism
mkFreeDefMor sens m1 m2 = FreeDefMorphism
  { freeDefMorphism = m1
  , pathFromFreeDef = m2
  , freeTheory = sens
  , isCofree = False }

getFreeDefMorphism :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
   lid -> LibEnv -> LibName -> DGraph -> [LEdge DGLinkLab]
   -> Maybe (FreeDefMorphism sentence morphism)
getFreeDefMorphism lid libEnv ln dg path = case path of
  [] -> error "getFreeDefMorphism"
  (s, t, l) : rp -> do
    gmor@(GMorphism cid _ _ fmor _) <- return $ dgl_morphism l
    G_theory lidth (ExtSign _sign _) _ axs _ <-
      computeTheory libEnv ln s
    if isHomogeneous gmor then do
        cfmor <- coerceMorphism (targetLogic cid) lid "getFreeDefMorphism1" fmor
        sens <- coerceSens lidth lid "getFreeDefMorphism4" (toNamedList axs)
        case rp of
          [] -> do
            G_theory lid2 (ExtSign sig _) _ _ _ <-
                     return $ dgn_theory $ labDG dg t
            sig2 <- coercePlainSign lid2 lid "getFreeDefMorphism2" sig
            return $ mkFreeDefMor sens cfmor $ ide sig2
          _ -> do
            pm@(GMorphism cid2 _ _ pmor _) <- calculateMorphismOfPath rp
            if isHomogeneous pm then do
                cpmor <- coerceMorphism (targetLogic cid2) lid
                         "getFreeDefMorphism3" pmor
                return $ mkFreeDefMor sens cfmor cpmor
              else Nothing
      else Nothing

getCFreeDefMorphs :: Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
   lid -> LibEnv -> LibName -> DGraph -> Node
   -> [FreeDefMorphism sentence morphism]
getCFreeDefMorphs lid libEnv ln dg node = let
  (frees, cofrees) = getCFreeDefLinks dg node
  myget = mapMaybe (getFreeDefMorphism lid libEnv ln dg)
  mkCoFree m = m { isCofree = True }
  in myget frees ++ map mkCoFree (myget cofrees)
