{- | Module     : $Header$
 -  Description : Logic specific function implementation for a "Generic Logic"
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : Similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : non-portable (various -fglasgow-exts extensions)
 -
 -  Stub file. Provides the implementation of the logic specific functions of
 -  the ModalLogic class in the particular case of a Generic Logic -}
{-# OPTIONS -fglasgow-exts #-}
module GMP.GenericML where

import GMP.GMPAS
import GMP.ModalLogic
import Text.ParserCombinators.Parsec

data Grules = Grules ()

instance ModalLogic Kars Grules where
    flagML _ = None
    parseIndex =  do l <- letter
                     Kars i <- parseIndex
                     return (Kars (l:i))
              <|> do return (Kars [])
    matchR _ = [Grules()]
    guessClause r = case r of
                        _ -> []
-------------------------------------------------------------------------------
