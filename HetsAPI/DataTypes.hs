module HetsAPI.DataTypes (
    Sentence (..)
    , SentenceByName(..)) where
import ATerm.AbstractSyntax (ATermTable)
import Logic.Prover (ThSens)
import Static.GTheory (BasicProof)
import Logic.Comorphism (AnyComorphism)
import qualified Common.OrderedMap as OMap
import Common.Json (Json)

type Sentence = Json
type SentenceByName = OMap.OMap String Sentence
