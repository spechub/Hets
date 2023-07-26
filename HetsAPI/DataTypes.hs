{- |
Description :  Common Datatypes used by the HETS API
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}
module HetsAPI.DataTypes (
    Sentence
  , SentenceByName
  , SignatureJSON
  , SymbolJSON
  , GenericTransportType
  , TheoryPointer) where
import qualified Common.OrderedMap as OMap
import Data.ByteString.Lazy(ByteString)

import Common.LibName (LibName)
import Static.DevGraph (LibEnv, DGraph, DGNodeLab)

import Data.Graph.Inductive.Graph (LNode)

-- | In the API if it is not possible to export the generic type, they are converted to JSON.
type GenericTransportType = ByteString

type Sentence = GenericTransportType
type SentenceByName = OMap.OMap String Sentence

type SignatureJSON = GenericTransportType
type SymbolJSON = GenericTransportType

type TheoryPointer = (LibName, LibEnv, DGraph, LNode DGNodeLab)
