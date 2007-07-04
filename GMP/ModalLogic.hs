{-# OPTIONS -fglasgow-exts #-}
module ModalLogic where

import GMPAS
import Text.ParserCombinators.Parsec

-------------------------------------------------------------------------------
-- Modal Logic Class
-------------------------------------------------------------------------------
class ModalLogic a b | a -> b, b -> a where
    preprocess :: (Formula a) -> (Formula a)
    parseIndex :: Parser a
    matchRO :: [(TVandMA a)] -> [b]
    guessClause :: b -> [Clause]
