{-# OPTIONS -fglasgow-exts #-}
module GenericML where

import GMPAS
import ModalLogic
import Text.ParserCombinators.Parsec

instance ModalLogic Kars Grules where
    parseIndex =  do l <- letter
                     ;Kars i <- parseIndex
                     ;return (Kars (l:i))
              <|> do return (Kars [])
    matchRO ro = if (length ro == 0)
                  then []
                  else [Grules ()]
-------------------------------------------------------------------------------
