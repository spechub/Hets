{- |
Description :  Common Datatypes used by the HETS API
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}
module HetsAPI.DataTypes (
    Sentence
  , SentenceByName
  , TheoryPointer) where
import qualified Common.OrderedMap as OMap
import Data.ByteString.Lazy(ByteString)

import Common.LibName (LibName)
import Static.DevGraph (LibEnv, DGraph, DGNodeLab)

import Data.Graph.Inductive.Graph (LNode)

type Sentence = ByteString
type SentenceByName = OMap.OMap String Sentence

type TheoryPointer = (LibName, LibEnv, DGraph, LNode DGNodeLab)