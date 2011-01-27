{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
{- |
Module      :  $Header$
Description :  compute ingoing free definition links for provers
Copyright   :  C. Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
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
import Data.Typeable

getCFreeDefLinks :: DGraph -> Node
  -> ([[LEdge DGLinkLab]], [[LEdge DGLinkLab]])
getCFreeDefLinks dg tgt =
  let isGlobalOrCFreeEdge = liftOr isGlobalEdge $ liftOr isFreeEdge isCofreeEdge
      paths = map reverse $ Tree.getAllPathsTo tgt
        $ elfilter (isGlobalOrCFreeEdge . dgl_type) $ dgBody dg
      myfilter p = filter ( \ ~((_, _, lbl) : _) -> p $ dgl_type lbl)
  in (myfilter isFreeEdge paths, myfilter isCofreeEdge paths)

mkFreeDefMor :: [Named sentence] -> morphism -> morphism
  -> FreeDefMorphism sentence morphism
mkFreeDefMor sens m1 m2 = FreeDefMorphism
  { freeDefMorphism = m1
  , pathFromFreeDef = m2
  , freeTheory = sens
  , isCofree = False }

data GFreeDefMorphism =
  forall lid sublogics basic_spec sentence symb_items symb_map_items
    sign morphism symbol raw_symbol proof_tree
  . Logic lid sublogics basic_spec sentence symb_items symb_map_items
      sign morphism symbol raw_symbol proof_tree
  => GFreeDefMorphism lid (FreeDefMorphism sentence morphism)
  deriving Typeable

getFreeDefMorphism :: LibEnv -> LibName -> DGraph -> [LEdge DGLinkLab]
  -> Maybe GFreeDefMorphism
getFreeDefMorphism libEnv ln dg path = case path of
  [] -> error "getFreeDefMorphism"
  (s, t, l) : rp -> do
    gmor@(GMorphism cid _ _ fmor _) <- return $ dgl_morphism l
    let tlid = targetLogic cid
    G_theory lidth (ExtSign _sign _) _ axs _ <-
      computeTheory libEnv ln s
    if isHomogeneous gmor then do
        sens <- coerceSens lidth tlid "getFreeDefMorphism4" (toNamedList axs)
        case rp of
          [] -> do
            G_theory lid2 (ExtSign sig _) _ _ _ <-
                     return $ dgn_theory $ labDG dg t
            sig2 <- coercePlainSign lid2 tlid "getFreeDefMorphism2" sig
            return $ GFreeDefMorphism tlid $ mkFreeDefMor sens fmor $ ide sig2
          _ -> do
            pm@(GMorphism cid2 _ _ pmor _) <- calculateMorphismOfPath rp
            if isHomogeneous pm then do
                cpmor <- coerceMorphism (targetLogic cid2) tlid
                         "getFreeDefMorphism3" pmor
                return $ GFreeDefMorphism tlid $ mkFreeDefMor sens fmor cpmor
              else Nothing
      else Nothing

getCFreeDefMorphs :: LibEnv -> LibName -> DGraph -> Node -> [GFreeDefMorphism]
getCFreeDefMorphs libEnv ln dg node = let
  (frees, cofrees) = getCFreeDefLinks dg node
  myget = mapMaybe (getFreeDefMorphism libEnv ln dg)
  mkCoFree (GFreeDefMorphism lid m) = GFreeDefMorphism lid m { isCofree = True }
  in myget frees ++ map mkCoFree (myget cofrees)
