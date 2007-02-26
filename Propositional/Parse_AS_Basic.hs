{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Definition of abstract syntax for propositional logic
-}

{-
  Ref.
  http://en.wikipedia.org/wiki/Propositional_logic
-}

module Propositional.Parse_AS_Basic 
    (
    ) 
    where

import Common.AnnoState as AnnoState
import Common.AS_Annotation as Annotation
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer
import Propositional.AS_BASIC_Propositional as AS_BASIC
import Text.ParserCombinators.Parsec

-- | Parser for implies '=>'
implKey :: AnnoState.AParser st Id.Token
implKey = AnnoState.asKey Keywords.implS

-- | Parser for and '/\'
andKey :: AnnoState.AParser st Id.Token
andKey = AnnoState.asKey Keywords.lAnd

-- | Parser for or '\/'
orKey :: AnnoState.AParser st Id.Token
orKey = AnnoState.asKey Keywords.lOr

-- | Parser for true 
trueKey :: AnnoState.AParser st Id.Token
trueKey = AnnoState.asKey Keywords.trueS

-- | Parser for false
falseKey :: AnnoState.AParser st Id.Token
falseKey = AnnoState.asKey Keywords.falseS

-- | Parser for not
notKey :: AnnoState.AParser st Id.Token
notKey = AnnoState.asKey Keywords.notS

-- | Parser for negation
negKey :: AnnoState.AParser st Id.Token
negKey = AnnoState.asKey Keywords.negS

-- | Parser for equivalence '<=>'
equivKey ::  AnnoState.AParser st Id.Token
equivKey = AnnoState.asKey Keywords.equivS

-- | Parser for atomic formulae
primFormula :: [String] -> AParser st FORMULA
primFormula f = 
    do c <- trueKey
       return (True_atom $ Id.tokPos c)
    <|>
    do c <- falseKey
       return (False_atom $ Id.tokPos c)
    <|>
    do c <- notKey <|> negKey <?> "\"not\""
       k <- primFormula f
       return (Negation k $ Id.tokPos c)
