module ModalLogic where

import GMPAS
import Text.ParserCombinators.Parsec

---------------------------------------------------------------------------------
-- Modal Logic Class
---------------------------------------------------------------------------------
class ModalLogic a where
    parseIndex :: Parser a
    matchRO :: (Formula a) -> [(TVandMA a)]
--    getClause :: ???   -- step 4

