{-# LANGUAGE ScopedTypeVariables #-}

module HetsAPI.InfoCommands (
     getGraphForLibrary
   , getNodesFromDevelopmentGraph
   , getLNodesFromDevelopmentGraph
   , getAllSentences
   , getAllAxioms
   , getAllGoals
   , getProvenGoals
   , getUnprovenGoals
   , prettySentence
   , prettySentenceOfTheory
) where

import Common.LibName (LibName)
import Static.DevGraph (LibEnv, lookupDGraph, labNodesDG, DGraph, DGNodeLab)
import Data.Graph.Inductive (LNode)
import Static.GTheory (G_theory (..), isProvenSenStatus)
import qualified Common.OrderedMap as OMap
import Common.AS_Annotation (sentence, SenAttr (isAxiom))
import Data.Aeson (toJSON, fromJSON, Result(..))
import Logic.Logic(Logic)
import Common.DocUtils (pretty)


import Data.Dynamic

import HetsAPI.DataTypes (SentenceByName, Sentence)

-- | @getDevelopmentGraphByName name env@ returns the development graph for the
--   library @name@ in the environment @env@.
getGraphForLibrary :: LibName -> LibEnv -> DGraph
getGraphForLibrary = lookupDGraph

-- | @getNodesFromDevelopmentGraph graph@ returns the nodes of the development
--   graph @graph@
getNodesFromDevelopmentGraph :: DGraph -> [DGNodeLab]
getNodesFromDevelopmentGraph = fmap snd . labNodesDG


-- | @getNodesFromDevelopmentGraph graph@ returns the nodes of the development
--   graph @graph@
getLNodesFromDevelopmentGraph :: DGraph -> [LNode DGNodeLab]
getLNodesFromDevelopmentGraph = labNodesDG

getAllSentences :: G_theory -> SentenceByName
getAllSentences (G_theory _ _ _ _ sens _) = OMap.map (toJSON . sentence) sens

getAllAxioms :: G_theory -> SentenceByName
getAllAxioms (G_theory _ _ _ _ sens _) = OMap.map (toJSON . sentence)
    $ OMap.filter isAxiom sens

getAllGoals :: G_theory -> SentenceByName
getAllGoals (G_theory _ _ _ _ sens _) = OMap.map (toJSON . sentence)
    $ OMap.filter (not . isAxiom) sens

getProvenGoals :: G_theory -> SentenceByName
getProvenGoals (G_theory _ _ _ _ sens _) = OMap.map (toJSON . sentence)
    $ OMap.filter (\sen -> not (isAxiom sen) && isProvenSenStatus sen) sens

getUnprovenGoals :: G_theory -> SentenceByName
getUnprovenGoals (G_theory _ _ _ _ sens _) = OMap.map (toJSON . sentence)
    $ OMap.filter (\sen -> isAxiom sen && isProvenSenStatus sen) sens

prettySentence' :: Logic lid sublogics basic_spec sentence symb_items symb_map_items sign morphism symbol raw_symbol proof_tree =>
    sentence -> lid -> Sentence -> String
prettySentence' (x::sentence) _ sen = case (fromJSON sen :: Result sentence) of
    Success a -> show . pretty $ a
    Error e -> "Error parsing JSON: " ++ e

prettySentence :: Logic lid sublogics basic_spec sentence symb_items symb_map_items sign morphism symbol raw_symbol proof_tree =>
    lid -> Sentence -> String
prettySentence = prettySentence' (undefined :: sentence)

prettySentenceOfTheory :: G_theory -> Sentence -> String
prettySentenceOfTheory (G_theory lid _ _ _ _ _) = prettySentence lid