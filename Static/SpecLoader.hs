{- |
Module      :  $Header$
Description :  For loading of signatures and sentences from file
Copyright   :  (c)  C. Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (import Logic)

For loading of signatures and sentences from file
-}

module Static.SpecLoader where

import Static.AnalysisLibrary
import Static.GTheory
import Static.DevGraph
import Static.ComputeTheory

import Driver.Options

import qualified Common.OrderedMap as OMap
import Common.GlobalAnnotations
import Common.AS_Annotation as Anno
import Common.Result
import Common.ResultT
import Common.LibName
import Common.Id as Id
import Common.ExtSign

import Data.Graph.Inductive.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Logic things
import Logic.Coerce
import Logic.Logic
import Comorphisms.LogicGraph


proceed' :: HetcatsOpts -> FilePath -> ResultT IO (LibName, LibEnv)
proceed' hopts = anaSourceFile logicGraph hopts Set.empty emptyLibEnv emptyDG

data SigSens sign sentence = 
    SigSens
    { sigsensSignature :: sign
    , sigsensNamedSentences :: [Named sentence]
    , sigsensGlobalAnnos :: GlobalAnnos
    , sigsensNode :: Node
    , sigsensNodeLabel :: DGNodeLab
    , sigsensDG :: DGraph
    , sigsensLibname :: LibName
    , sigsensLibenv :: LibEnv }

getSigSensComplete ::
    Logic lid sublogics basic_spec sentence
          symb_items symb_map_items sign
          morphism symbol raw_symbol proof_tree
    => Bool -- complete theory or not
    -> HetcatsOpts -- options
    -> lid -- logicname
    -> String -- filename
    -> String  -- name of spec
    -> IO (SigSens sign sentence)
getSigSensComplete b hopts lid fname sp = do
  Result _ res <- runResultT $ proceed' hopts fname
  case res of
    Just (ln, lenv) -> getSpec b lid ln lenv sp
    Nothing -> error $ "getSigSensComplete: cannot read file" ++ fname


-- read in a hets file and return the basic theory and the sentences
getSigSens ::
    Logic lid sublogics basic_spec sentence
          symb_items symb_map_items sign
          morphism symbol raw_symbol proof_tree
    => HetcatsOpts -- options
    -> lid -- logicname
    -> String -- filename
    -> String  -- name of spec
    -> IO (SigSens sign sentence)
getSigSens = getSigSensComplete False


getSpec ::
    Logic lid sublogics basic_spec sentence
          symb_items symb_map_items sign
          morphism symbol raw_symbol proof_tree
    => Bool -- complete theory or not
    -> lid -- logicname
    -> LibName
    -> LibEnv
    -> String  -- name of spec
    -> IO (SigSens sign sentence)
getSpec b lid ln lenv sp =
    let dg = lookupDGraph ln lenv
        SpecEntry (ExtGenSig _ (NodeSig node _)) =
            case Map.lookup (Id.mkSimpleId sp) $ globalEnv dg of
              Just x -> x
              _ -> error $ "getSpec: Specification " ++ sp ++ " not found"
        f nL gth =
            case gth of
              G_theory { gTheoryLogic = lid2
                       , gTheorySign = gSig
                       , gTheorySens = gSens } ->
                     case (coerceSign lid2 lid "" gSig,
                           coerceThSens lid2 lid "" gSens) of
                       (Just sig, Just sens) ->
                           return SigSens
                                      { sigsensSignature = plainSign sig
                                      , sigsensNamedSentences
                                          = map (\ (x, y) -> y{senAttr = x})
                                            $ OMap.toList sens
                                      , sigsensGlobalAnnos = globalAnnos dg
                                      , sigsensNode = node
                                      , sigsensNodeLabel = nL
                                      , sigsensDG = dg
                                      , sigsensLibname = ln
                                      , sigsensLibenv = lenv }
                       _ -> error $ "getSpec: Not a " ++ show lid ++ " sig"

    in if b then
           case computeTheory lenv ln node of
             Just gth -> f (labDG dg node) gth
             _ -> error "getSpec: computeTheory failed"
       else
           case match node (dgBody dg) of
             (Just ctx, _) ->
                 let nL = lab' ctx in f nL $ dgn_theory nL
             _ -> error $ "getSpec: Node " ++ show node
                  ++ " not in development graph"

