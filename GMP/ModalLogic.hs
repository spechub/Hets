module ModalLogic where

import GMPAS
import Text.ParserCombinators.Parsec

---------------------------------------------------------------------------------
-- Modal Logic Class
---------------------------------------------------------------------------------
class ModalLogic a where
    parseIndex :: Parser a
--    matchRo :: ???     -- step 3
--    getClause :: ???   -- step 4

