{- |
Description :  Common Datatypes used by the HETS API
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt
-}
module HetsAPI.DataTypes (
    Sentence
  , TheorySentence
  , TheorySentenceByName
  , SignatureJSON
  , SymbolJSON
  , GenericTransportType
  , TheoryPointer) where

import Data.ByteString.Lazy(ByteString)
import Data.Graph.Inductive.Graph (LNode)

import Common.AS_Annotation(SenAttr(..))
import Common.LibName (LibName)
import qualified Common.OrderedMap as OMap

import Logic.Comorphism (AnyComorphism(..))
import Logic.Prover(ThmStatus(..))

import Static.DevGraph (LibEnv, DGraph, DGNodeLab)
import Static.GTheory (BasicProof(..))



-- | In the API if it is not possible to export the generic type, they are converted to JSON.
type GenericTransportType = ByteString


type Sentence = GenericTransportType

type TheorySentence = SenAttr Sentence (ThmStatus (AnyComorphism, BasicProof))
type TheorySentenceByName = OMap.OMap String TheorySentence

type SignatureJSON = GenericTransportType
type SymbolJSON = GenericTransportType

type TheoryPointer = (LibName, LibEnv, DGraph, LNode DGNodeLab)
