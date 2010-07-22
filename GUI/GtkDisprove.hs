

module GUI.GtkDisprove where

import Common.LibName
import Common.AS_Annotation
import qualified Common.OrderedMap as OMap

import Data.Graph.Inductive.Graph (LNode)

import Logic.Comorphism
import Logic.Logic

import Proofs.AbstractState
import Proofs.ConsistencyCheck

import Static.DevGraph
import Static.GTheory


 -- TODO write error messages with content!
 -- TODO use return value of consistencyCheck and mark node
 -- TODO implement in GtkProverGui

disproveNode :: AnyComorphism -> String -> LNode DGNodeLab
             -> Int -> IO ConsistencyStatus
disproveNode ac selGoal (i, l) timeout =
  case globalTheory l of
    Nothing -> error "GtkDisprove.disproveNode(1)"
    Just (G_theory lid a b sens c) -> 
      let axioms = OMap.filter isAxiom sens
          negSen = case OMap.lookup selGoal sens of
                     Nothing -> error "GtkDisprove.disproveNode(2)"
                     Just sen -> 
                       case negation lid $ sentence sen of
                         Nothing -> error "GtkDisprove.disproveNode(3)"
                         Just sen' -> sen { sentence = sen' }
          sens' = OMap.insert selGoal negSen axioms
          cc = fst $ head $ getConsCheckers [ac]  
      in consistencyCheckAux False cc ac (i, l {globalTheory = 
        Just (G_theory lid a b sens' c) }) timeout
          
