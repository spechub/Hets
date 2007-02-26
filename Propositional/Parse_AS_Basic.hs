{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for propositional logic
-}

{-
  Ref.
  http://en.wikipedia.org/wiki/Propositional_logic
-}

module Propositional.Parse_AS_Basic 
    (
    ) 
    where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import qualified Common.Id as Id
import qualified Common.Keywords as Keywords
import qualified Common.Lexer as Lexer
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
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

-- | Parser for primitive formulae
primFormula :: [String] -> AnnoState.AParser st AS_BASIC.FORMULA
primFormula f = 
    do c <- trueKey
       return (AS_BASIC.True_atom $ Id.tokPos c)
    <|>
    do c <- falseKey
       return (AS_BASIC.False_atom $ Id.tokPos c)
    <|>
    do c <- notKey <|> negKey <?> "\"not\""
       k <- primFormula f
       return (AS_BASIC.Negation k $ Id.tokPos c)

-- | Parser for formulae containing 'and' and 'or'
andOrFormula :: [String] -> AnnoState.AParser st AS_BASIC.FORMULA
andOrFormula k =
               do f <- primFormula k
                  do c <- andKey
                     (fs, ps) <- primFormula k `Lexer.separatedBy` andKey
                     return (AS_BASIC.Conjunction (f:fs) (Id.catPos (c:ps)))
                    <|>
                    do c <- orKey
                       (fs, ps) <- primFormula k `Lexer.separatedBy` orKey
                       return (AS_BASIC.Disjunction (f:fs) (Id.catPos (c:ps)))
                    <|> return f

-- | Parser for formulae with implications
impFormula :: [String] -> AnnoState.AParser st AS_BASIC.FORMULA
impFormula k =
             do f <- andOrFormula k
                do c <- implKey
                   (fs, ps) <- andOrFormula k `Lexer.separatedBy` implKey
                   return (makeImpl True (f:fs) (Id.catPosAux (c:ps)))
                  <|>
                  do c <- equivKey
                     g <- andOrFormula k
                     return (AS_BASIC.Equivalence f g $ Id.tokPos c)
                  <|> return f
                    where makeImpl b [f,g] p = AS_BASIC.Implication f g b (Id.Range p)
                          makeImpl b (f:r) (c:p) =
                                     AS_BASIC.Implication f (makeImpl b r p) b (Id.Range [c])
                          makeImpl _ _ _ =
                              error "makeImpl got illegal argument"
                          makeIf l p = makeImpl False (reverse l) (reverse p)
