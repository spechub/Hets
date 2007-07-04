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
    flagML :: (Formula a) -> PPflag
    parseIndex :: Parser a
    matchRO :: [(TVandMA a)] -> [b]
    guessClause :: b -> [Clause]
