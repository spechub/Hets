{-# OPTIONS -fglasgow-exts #-}
module GradedML where

import GMPAS
import ModalLogic
import Lexer

data GMLrules = GMLrules ()

instance ModalLogic Integer GMLrules where
    preprocess f =
        case f of
            T                      -> T
            F                      -> F
            Neg ff                 -> Neg $ preprocess ff
            Junctor f1 j f2        -> Junctor (preprocess f1) j (preprocess f2)
            Mapp (Mop i Square) ff -> Neg $ Mapp (Mop i Angle) (Neg ff)
            _                      -> f
            
    parseIndex = natural
    matchRO ro = if (length ro == 0)
                  then []
                  else [GMLrules ()]
    guessClause r = case r of
                    _ -> []
-------------------------------------------------------------------------------
