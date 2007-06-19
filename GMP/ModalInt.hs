module ModalInt where

import ModalLogic
import GMPAS
--import Text.ParserCombinators.Parsec
import Lexer

instance ModalLogic Integer where
    parseIndex = natural
