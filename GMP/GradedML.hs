{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

instance ModalLogic Integer GMLrules where
    parseIndex = natural
    matchRO ro = if (length ro == 0)
                  then []
                  else [GMLrules ()]
-------------------------------------------------------------------------------
