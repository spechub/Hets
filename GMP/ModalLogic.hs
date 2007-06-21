{-# OPTIONS -fglasgow-exts #-}
module ModalLogic where

import GMPAS
import Text.ParserCombinators.Parsec

-------------------------------------------------------------------------------
-- Modal Logic Class
-------------------------------------------------------------------------------
class ModalLogic a b | a -> b where
    parseIndex :: Parser a
    matchRO :: [(TVandMA a)] -> [b]
--    getClause :: ???   -- step 4
