{-# OPTIONS -fglasgow-exts #-}
module GMP.GenericML where

import GMP.GMPAS
import GMP.ModalLogic
import Text.ParserCombinators.Parsec

data Grules = Grules ()

instance ModalLogic Kars Grules where
    flagML _ = None
    parseIndex =  do l <- letter
                     ;Kars i <- parseIndex
                     ;return (Kars (l:i))
              <|> do return (Kars [])
    matchR _ = [Grules()]
    guessClause r = case r of
                        _ -> []
-------------------------------------------------------------------------------
