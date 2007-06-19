module GenericML where

import GMPAS
import ModalLogic
import Text.ParserCombinators.Parsec

instance ModalLogic Kars where
    parseIndex =  do l <- letter
                     ;Kars i <- parseIndex
                     ;return (Kars (l:i))
              <|> do return (Kars [])

