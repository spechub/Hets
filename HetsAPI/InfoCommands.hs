{-# LANGUAGE ScopedTypeVariables #-}
{- |
Description :  Commands providing information about the state of the development graph and selected theories
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}


module HetsAPI.InfoCommands (
     getGraphForLibrary
   , getNodesFromDevelopmentGraph
   , getLNodesFromDevelopmentGraph
   , getEdgesFromDevelopmentGraph
   , getLEdgesFromDevelopmentGraph
   , getAllSentences
   , getAllAxioms
   , getAllGoals
   , getProvenGoals
   , getUnprovenGoals
   , prettySentence
   , prettySentenceOfTheory
   , getDevelopmentGraphNodeType
   , theorySentenceIsAxiom
   , theorySentenceWasTheorem
   , theorySentenceIsDefined
   , theorySentenceGetTheoremStatus
   , theorySentencePriority
   , theorySentenceContent
   , theorySentenceBestProof
   , getLibraryDependencies
) where

import Data.Aeson (encode, eitherDecode, Result(..), ToJSON)
import Data.Dynamic
import Data.Graph.Inductive (LNode, LEdge)

import Common.AS_Annotation (SenAttr (..))
import Common.DocUtils (pretty)
import Common.LibName (LibName)
import qualified Common.Lib.Rel as Rel
import qualified Common.OrderedMap as OMap

import Logic.Logic(Logic)
import Logic.Prover(ThmStatus(..))
import Logic.Comorphism(AnyComorphism(..))

import HetsAPI.DataTypes (TheoryPointer, TheorySentenceByName, TheorySentence, Sentence)

import Static.DevGraph (LibEnv, lookupDGraph, labNodesDG, labEdgesDG, DGraph, DGNodeLab, DGLinkLab, getDGNodeName, getRealDGNodeType, getLibDepRel)
import Static.DgUtils (DGNodeType)
import Static.GTheory (G_theory (..), isProvenSenStatus, BasicProof(..))



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

getLEdgesFromDevelopmentGraph :: DGraph -> [LEdge DGLinkLab]
getLEdgesFromDevelopmentGraph = labEdgesDG

getEdgesFromDevelopmentGraph :: DGraph -> [DGLinkLab]
getEdgesFromDevelopmentGraph = fmap (\(_, _, x) -> x) . labEdgesDG

-- getGlobalAnnotations :: DGraph -> GlobalAnnos

theorySentenceIsAxiom :: SenAttr a (ThmStatus tStatus) -> Bool
theorySentenceIsAxiom = isAxiom

theorySentenceWasTheorem :: SenAttr a (ThmStatus tStatus) -> Bool
theorySentenceWasTheorem = wasTheorem

theorySentenceIsDefined :: SenAttr a (ThmStatus tStatus) -> Bool
theorySentenceIsDefined = isDef

theorySentenceGetTheoremStatus :: SenAttr a (ThmStatus tStatus) -> [tStatus]
theorySentenceGetTheoremStatus = getThmStatus . senAttr

theorySentencePriority :: SenAttr a (ThmStatus tStatus) -> Maybe String
theorySentencePriority = priority

theorySentenceContent :: SenAttr a (ThmStatus tStatus) -> a
theorySentenceContent = sentence

theorySentenceBestProof :: Ord proof => SenAttr a (ThmStatus (c, proof)) -> Maybe proof
theorySentenceBestProof sentence =
    if null ts then Nothing else Just $ maximum $ map snd ts
    where ts = theorySentenceGetTheoremStatus sentence


toTheorySentence :: ToJSON sentence => SenAttr sentence (ThmStatus (AnyComorphism, BasicProof)) -> TheorySentence
toTheorySentence sen = sen { sentence = encode . sentence $ sen }

getAllSentences :: G_theory -> TheorySentenceByName
getAllSentences (G_theory _ _ _ _ sens _) = OMap.map toTheorySentence sens

getAllAxioms :: G_theory -> TheorySentenceByName
getAllAxioms (G_theory _ _ _ _ sens _) = OMap.map toTheorySentence
    $ OMap.filter isAxiom sens

getAllGoals :: G_theory -> TheorySentenceByName
getAllGoals (G_theory _ _ _ _ sens _) = OMap.map toTheorySentence
    $ OMap.filter (not . isAxiom) sens

getProvenGoals :: G_theory -> TheorySentenceByName
getProvenGoals (G_theory _ _ _ _ sens _) = OMap.map toTheorySentence
    $ OMap.filter (\sen -> not (isAxiom sen) && isProvenSenStatus sen) sens

getUnprovenGoals :: G_theory -> TheorySentenceByName
getUnprovenGoals (G_theory _ _ _ _ sens _) = OMap.map toTheorySentence
    $ OMap.filter (\sen -> not (isAxiom sen) && not (isProvenSenStatus sen)) sens

prettySentence' :: Logic lid sublogics basic_spec sentence symb_items symb_map_items sign morphism symbol raw_symbol proof_tree =>
    sentence -> lid -> Sentence -> String
prettySentence' (x::sentence) _ sen = case (eitherDecode sen :: Either String sentence) of
    Left e -> "Error parsing JSON: " ++ e
    Right a -> show . pretty $ a

prettySentence :: Logic lid sublogics basic_spec sentence symb_items symb_map_items sign morphism symbol raw_symbol proof_tree =>
    lid -> Sentence -> String
prettySentence = prettySentence' (undefined :: sentence)

prettySentenceOfTheory :: G_theory -> Sentence -> String
prettySentenceOfTheory (G_theory lid _ _ _ _ _) = prettySentence lid

getDevelopmentGraphNodeType :: DGNodeLab -> DGNodeType
getDevelopmentGraphNodeType = getRealDGNodeType

getLibraryDependencies :: LibEnv -> [(LibName, LibName)]
getLibraryDependencies =
  Rel.toList . Rel.intransKernel . getLibDepRel