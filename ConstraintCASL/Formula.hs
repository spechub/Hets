{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse terms and formulae
-}

module ConstraintCASL.Formula     where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import ConstraintCASL.AS_ConstraintCASL
import Text.ParserCombinators.Parsec
import CASL.AS_Basic_CASL

-- ------------------------------------------------------------------------
-- formula
-- ------------------------------------------------------------------------

cformula :: [String] -> AParser st ConstraintFORMULA
cformula k = return CC

formula :: [String] -> AParser st ConstraintCASLFORMULA
formula k = do x <- cformula k
               return (ExtFORMULA x)

instance AParsable ConstraintFORMULA where
  aparser = cformula []

