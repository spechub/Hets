{- |
Module      :  $Header$
Description :  Parser for basic specs
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for propositional logic

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>

Acknowledgements:
I'd like to thank Christian Maeder for his help and advice.

-}

module Propositional.Parse_AS_Basic
    (
     basicSpec                      -- Parser for basic specs
    )
    where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import qualified Common.Id as Id
import qualified Common.Keywords as Keywords
import Common.Lexer as Lexer
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Common.AS_Annotation as AS_Anno
import Text.ParserCombinators.Parsec

propKeywords :: [String]
propKeywords = [
                Keywords.propS
               ,Keywords.notS
               ,Keywords.trueS
               ,Keywords.falseS
               ]

-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st AS_BASIC.BASIC_SPEC
basicSpec = (fmap AS_BASIC.Basic_spec $ AnnoState.annosParser $ parseBasicItems)
            <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (AS_BASIC.Basic_spec []))

-- | Parser for basic items
parseBasicItems :: AnnoState.AParser st AS_BASIC.BASIC_ITEMS
parseBasicItems =
   parsePredDecl
   <|>
   parseAxItems

-- | parser for predicate declarations
parsePredDecl :: AnnoState.AParser st AS_BASIC.BASIC_ITEMS
parsePredDecl = fmap AS_BASIC.Pred_decl predItem

-- | parser for Axiom_items
parseAxItems :: AnnoState.AParser st AS_BASIC.BASIC_ITEMS
parseAxItems =
    do d <- AnnoState.dotT
       (fs, ds) <- aFormula `Lexer.separatedBy` AnnoState.dotT
       (_, an) <- AnnoState.optSemi
       let _  = Id.catRange (d:ds)
           ns = init fs ++ [AS_Anno.appendAnno (last fs) an]
       return $ AS_BASIC.Axiom_items ns

-- | Any word to token
propId :: GenParser Char st Id.Token
propId = Lexer.pToken $ Lexer.reserved propKeywords Lexer.scanAnyWords

-- | parser for predicates = propositions
predItem :: AnnoState.AParser st AS_BASIC.PRED_ITEM
predItem =
    do
      v <- AnnoState.asKey (Keywords.propS++Keywords.sS) <|>
           AnnoState.asKey Keywords.propS
      (ps, cs) <- propId `Lexer.separatedBy` AnnoState.anComma
      return $ AS_BASIC.Pred_item ps $ Id.catRange(v : cs)

-- | Parser for implies @=>@
implKey :: AnnoState.AParser st Id.Token
implKey = AnnoState.asKey Keywords.implS

-- | Parser for and @\/\ @
andKey :: AnnoState.AParser st Id.Token
andKey = AnnoState.asKey Keywords.lAnd

-- | Parser for or @\\\/@
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

-- | Parser for equivalence @<=>@
equivKey ::  AnnoState.AParser st Id.Token
equivKey = AnnoState.asKey Keywords.equivS

-- | Parser for primitive formulae
primFormula :: AnnoState.AParser st AS_BASIC.FORMULA
primFormula =
    do c <- trueKey
       return (AS_BASIC.True_atom $ Id.tokPos c)
    <|>
    do c <- falseKey
       return (AS_BASIC.False_atom $ Id.tokPos c)
    <|>
    do c <- notKey <|> negKey <?> "\"not\""
       k <- primFormula
       return (AS_BASIC.Negation k $ Id.tokPos c)
    <|> parenFormula
    <|> fmap AS_BASIC.Predication propId

-- | Parser for formulae containing 'and' and 'or'
andOrFormula :: AnnoState.AParser st AS_BASIC.FORMULA
andOrFormula =
               do f <- primFormula
                  do c <- andKey
                     (fs, ps) <- primFormula `Lexer.separatedBy` andKey
                     return (AS_BASIC.Conjunction (f:fs) (Id.catRange (c:ps)))
                    <|>
                    do c <- orKey
                       (fs, ps) <- primFormula `Lexer.separatedBy` orKey
                       return (AS_BASIC.Disjunction (f:fs) (Id.catRange (c:ps)))
                    <|> return f

-- | Parser for formulae with implications
impFormula :: AnnoState.AParser st AS_BASIC.FORMULA
impFormula  =
             do f <- andOrFormula
                do c <- implKey
                   (fs, ps) <- andOrFormula `Lexer.separatedBy` implKey
                   return (makeImpl      (f:fs) (Id.catPosAux (c:ps)))
                  <|>
                  do c <- equivKey
                     g <- andOrFormula
                     return (AS_BASIC.Equivalence f g $ Id.tokPos c)
                  <|> return f
                    where makeImpl   [f,g] p = AS_BASIC.Implication f g   (Id.Range p)
                          makeImpl   (f:r) (c:p) =
                                     AS_BASIC.Implication f (makeImpl r p)   (Id.Range [c])
                          makeImpl   _ _ =
                              error "makeImpl got illegal argument"

-- | Parser for formulae with parentheses
parenFormula :: AnnoState.AParser st AS_BASIC.FORMULA
parenFormula =
    do Lexer.oParenT << AnnoState.addAnnos
       f <- impFormula << AnnoState.addAnnos
       Lexer.cParenT >> return f

-- | Toplevel parser for formulae
aFormula :: AnnoState.AParser st (AS_Anno.Annoted AS_BASIC.FORMULA)
aFormula = Lexer.bind AS_Anno.appendAnno (AnnoState.annoParser $ impFormula) AnnoState.lineAnnos
