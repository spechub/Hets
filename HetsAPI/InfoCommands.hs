module HetsAPI.InfoCommands (
     getGraphForLibrary
   , getNodesFromDevelopmentGraph
   , getLNodesFromDevelopmentGraph
   , getAllSentences
   , getAllAxioms
   , getAllGoals
   , getProvenGoals
   , getUnprovenGoals
) where


import Common.LibName (LibName)
import Static.DevGraph (LibEnv, DGraph (DGraph), DGNodeLab (DGNodeLab), lookupDGraph, labNodesDG)
import Data.Graph.Inductive (LNode)
import Static.GTheory (G_theory (..), isProvenSenStatus)
import HetsAPI.DataTypes (Sentence, SentenceByName)
import qualified Common.OrderedMap as OMap
import ATerm.Conversion (toShATerm')
import ATerm.AbstractSyntax (emptyATermTable)
import Common.AS_Annotation (sentence, SenAttr (isAxiom))
import Common.Json (asJson)
import Logic.Prover (thmStatus)

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
getAllSentences (G_theory _ _ _ _ sens _) = OMap.map (asJson . sentence) sens

getAllAxioms :: G_theory -> SentenceByName
getAllAxioms (G_theory _ _ _ _ sens _) = OMap.map (asJson . sentence)
    $ OMap.filter isAxiom sens

getAllGoals :: G_theory -> SentenceByName
getAllGoals (G_theory _ _ _ _ sens _) = OMap.map (asJson . sentence)
    $ OMap.filter (not . isAxiom) sens

getProvenGoals :: G_theory -> SentenceByName
getProvenGoals (G_theory _ _ _ _ sens _) = OMap.map (asJson . sentence)
    $ OMap.filter (\sen -> not (isAxiom sen) && isProvenSenStatus sen) sens

getUnprovenGoals :: G_theory -> SentenceByName
getUnprovenGoals (G_theory _ _ _ _ sens _) = OMap.map (asJson . sentence)
    $ OMap.filter (\sen -> isAxiom sen && isProvenSenStatus sen) sens