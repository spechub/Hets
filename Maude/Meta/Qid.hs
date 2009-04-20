module Maude.Meta.Qid (
    Qid,
    QidList,
    QidSet,
    QidMap,
    qid,
    fromString,
    toString
) where

import Common.ATerm.Conversion
import Common.DocUtils (Pretty)
import qualified Common.Id as Id

import Data.Map (Map)
import Data.Set (Set)
import Data.Typeable (Typeable)
import qualified Data.Char as Char

-- A Quoted Identifier
newtype Qid = Qid { qid :: Id.Id }
    deriving (Show, Eq, Ord, Typeable, Pretty)

-- TODO: Replace dummy implementation for ShATermConvertible Qid.
instance ShATermConvertible Qid where
    toShATermAux table _ = return (table, 0)
    fromShATermAux _ table = (table, fromString "Qid")


type QidList = [Qid]
type QidSet = Set Qid
type QidMap = Map Qid Qid


-- Convert a Qid to a String.
toString :: Qid -> String
--string (Qid q) = q
toString  = show . qid

-- Convert a String to a Qid.
fromString :: String -> Qid
fromString = Qid . Id.stringToId . translate


--- Helper functions for translating a String to a Qid.

-- Quote the identifier by prepending a tick.
-- Don't keep backticks at the beginning of a string.
tick :: String -> String
tick ('`':str) = tick str
tick str = '\'':str

-- Escape a special character by prepending a backtick.
-- Don't place backticks at the end of a string.
backtick :: String -> String
backtick "" = ""
backtick str = '`':str

-- Translate the string to an identifier by masking all special characters.
translate :: String -> String
translate = tick . foldr escape ""

-- Escape a whitespace or special character.
escape :: Char -> String -> String
escape char str
    | isSpecial char = collapse $ backtick (char:str)
    | isSpace char = collapse $ backtick str
    | otherwise = char:str
    where
        isSpecial ch = elem ch "()[]{},"
        isSpace ch = Char.isSpace ch || ch == '`'

-- Sequences of backticks are collapsed into one.
collapse :: String -> String
collapse ('`':'`':str) = '`':str
collapse str = str
