module ModalLogic where

import GMPAS
import Text.ParserCombinators.Parsec

---------------------------------------------------------------------------------
-- Modal Logic Class
---------------------------------------------------------------------------------
class ModalLogic a where
    parseIndex :: Parser a
    matchRO :: [(TVandMA a)] -> [Int]
--    getClause :: ???   -- step 4
