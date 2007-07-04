{-# OPTIONS -fglasgow-exts #-}
module GenericML where

import GMPAS
import ModalLogic
import Text.ParserCombinators.Parsec

data Grules = Grules ()

instance ModalLogic Kars Grules where
    flagML _ = None
    parseIndex =  do l <- letter
                     ;Kars i <- parseIndex
                     ;return (Kars (l:i))
              <|> do return (Kars [])
    matchRO ro = if (length ro == 0)
                  then []
                  else [Grules ()]
    guessClause r = case r of
                    _ -> []
-------------------------------------------------------------------------------
