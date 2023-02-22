module HetsAPI.DataTypes (
    Sentence
  , SentenceByName) where
import qualified Common.OrderedMap as OMap
import Data.Aeson (Value)

type Sentence = Value
type SentenceByName = OMap.OMap String Sentence
