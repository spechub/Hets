{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS()
import ModalLogic
import Lexer

data GMLrules = GMLrules ()

instance ModalLogic Integer GMLrules where
    parseIndex = natural
    matchRO ro = if (length ro == 0)
                  then []
                  else [GMLrules ()]
    guessClause r = case r of
                    _ -> []
-------------------------------------------------------------------------------
