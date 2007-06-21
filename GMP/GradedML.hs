module GradedML where

import GMPAS
import ModalLogic
import Lexer

instance ModalLogic Integer GMLrules where
    parseIndex = natural

-------------------------------------------------------------------------------
