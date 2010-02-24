{- |
Module      :  $Header$
Description :  Parser for basic specs
Copyright   :  (c) Dominik Dietrich, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for reduce computer algebra system
-}

module Reduce.Parse_AS_Basic
    where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer

import Propositional.AS_BASIC_Propositional as AS_BASIC
import Text.ParserCombinators.Parsec

