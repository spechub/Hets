module GradedML where

import GMPAS
import ModalLogic
import Lexer

instance ModalLogic Integer where
    parseIndex = natural

