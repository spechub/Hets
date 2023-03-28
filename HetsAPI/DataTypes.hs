module HetsAPI.DataTypes (
    Sentence
  , SentenceByName
  , TheoryPointer) where
import qualified Common.OrderedMap as OMap
import Data.Aeson (Value)

import Common.LibName (LibName)
import Static.DevGraph (LibEnv, DGraph, DGNodeLab)

import Data.Graph.Inductive.Graph (LNode)

type Sentence = Value
type SentenceByName = OMap.OMap String Sentence

type TheoryPointer = (LibName, LibEnv, DGraph, LNode DGNodeLab)