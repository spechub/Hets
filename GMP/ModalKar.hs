module ModalKar where

import ModalLogic
import GMPAS
--import Lexer
import Text.ParserCombinators.Parsec

instance ModalLogic Kars where 
    parseIndex =  do l <- letter 
                     ;Kars i <- parseIndex 
                     ;return (Kars (l:i))
              <|> do return (Kars [])
