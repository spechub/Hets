{-# OPTIONS -fglasgow-exts #-}
module ModalLogic where

import GMPAS
import Text.ParserCombinators.Parsec

data PPflag = Sqr | Ang | None
    deriving Eq
-------------------------------------------------------------------------------
-- Modal Logic Class
-------------------------------------------------------------------------------
class ModalLogic a b | a -> b, b -> a where
    OrderIns :: (Formula a) -> Bool                 -- order insensitivity flag
    flagML :: (Formula a) -> PPflag              -- primary modal operator flag
    parseIndex :: Parser a                                      -- index parser
    matchRO :: [(MATV a)] -> [b]                                 -- RO matching
    guessClause :: b -> [Clause]                             -- clause guessing
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
