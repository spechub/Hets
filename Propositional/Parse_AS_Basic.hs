{- |
Module      :  ./Propositional/Parse_AS_Basic.hs
Description :  Parser for basic specs
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for propositional logic

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
-}

module Propositional.Parse_AS_Basic
  ( basicSpec                      -- Parser for basic specs
  , symbItems
  , symbMapItems
  , impFormula
  , primFormula
  ) where

import Common.AnnoState
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import Common.Parsec
import Common.GlobalAnnotations (PrefixMap)

import Propositional.AS_BASIC_Propositional as AS_BASIC
import Text.ParserCombinators.Parsec

propKeywords :: [String]
propKeywords = criticalKeywords ++
  [ propS
  , notS
  , trueS
  , falseS ]

-- | Toplevel parser for basic specs
basicSpec :: PrefixMap -> AParser st AS_BASIC.BASIC_SPEC
basicSpec _ =
  fmap AS_BASIC.Basic_spec (annosParser parseBasicItems)
  <|> (oBraceT >> cBraceT >> return (AS_BASIC.Basic_spec []))

-- | Parser for basic items
parseBasicItems :: AParser st AS_BASIC.BASIC_ITEMS
parseBasicItems = parsePredDecl <|> parseAxItems

-- | parser for predicate declarations
parsePredDecl :: AParser st AS_BASIC.BASIC_ITEMS
parsePredDecl = fmap AS_BASIC.Pred_decl predItem

-- | parser for Axiom_items
parseAxItems :: AParser st AS_BASIC.BASIC_ITEMS
parseAxItems = do
       d <- dotT
       (fs, ds) <- aFormula `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       return $ AS_BASIC.Axiom_items ns

-- | Any word to token
propId :: GenParser Char st Token
propId = pToken $ reserved propKeywords scanAnyWords

-- | parser for predicates = propositions
predItem :: AParser st AS_BASIC.PRED_ITEM
predItem = do
      v <- asKey (propS ++ sS) <|>
           asKey propS
      (ps, cs) <- propId `separatedBy` anComma
      return $ AS_BASIC.Pred_item ps $ catRange $ v : cs

-- | Parser for implies @=>@
implKey :: AParser st Token
implKey = asKey implS

-- | Parser for and @\/\ @
andKey :: AParser st Token
andKey = asKey lAnd

-- | Parser for or @\\\/@
orKey :: AParser st Token
orKey = asKey lOr

-- | Parser for true
trueKey :: AParser st Token
trueKey = asKey trueS

-- | Parser for false
falseKey :: AParser st Token
falseKey = asKey falseS

-- | Parser for not
notKey :: AParser st Token
notKey = asKey notS

-- | Parser for negation
negKey :: AParser st Token
negKey = asKey negS

-- | Parser for equivalence @<=>@
equivKey :: AParser st Token
equivKey = asKey equivS

-- | Parser for primitive formulae
primFormula :: AParser st AS_BASIC.FORMULA
primFormula =
    do c <- trueKey
       return (AS_BASIC.True_atom $ tokPos c)
    <|>
    do c <- falseKey
       return (AS_BASIC.False_atom $ tokPos c)
    <|>
    do c <- notKey <|> negKey <?> "\"not\""
       k <- primFormula
       return (AS_BASIC.Negation k $ tokPos c)
    <|> parenFormula
    <|> fmap AS_BASIC.Predication propId

-- | Parser for formulae containing 'and' and 'or'
andOrFormula :: AParser st AS_BASIC.FORMULA
andOrFormula = do
  f <- primFormula
  do c <- andKey
     (fs, ps) <- primFormula `separatedBy` andKey
     return . AS_BASIC.Conjunction (f : fs) . catRange $ c : ps
   <|> do
     c <- orKey
     (fs, ps) <- primFormula `separatedBy` orKey
     return . AS_BASIC.Disjunction (f : fs) . catRange $ c : ps
   <|> return f

-- | Parser for formulae with implications
impFormula :: AParser st AS_BASIC.FORMULA
impFormula = do
  f <- andOrFormula
  do c <- implKey
     (fs, ps) <- andOrFormula `separatedBy` implKey
     return . makeImpl (f : fs) . catPosAux $ c : ps
   <|> do
     c <- equivKey
     g <- andOrFormula
     return . AS_BASIC.Equivalence f g $ tokPos c
   <|> return f
  where
  makeImpl [f, g] p = AS_BASIC.Implication f g (Range p)
  makeImpl (f : r) (c : p) = AS_BASIC.Implication f (makeImpl r p) (Range [c])
  makeImpl _ _ = error "makeImpl got illegal argument"

-- | Parser for formulae with parentheses
parenFormula :: AParser st AS_BASIC.FORMULA
parenFormula = do
       oParenT << addAnnos
       f <- impFormula << addAnnos
       cParenT >> return f

-- | Toplevel parser for formulae
aFormula :: AParser st (Annoted AS_BASIC.FORMULA)
aFormula = allAnnoParser impFormula

-- | parsing a prop symbol
symb :: GenParser Char st SYMB
symb = fmap Symb_id propId

-- | parsing one symbol or a mapping of one to a second symbol
symbMap :: GenParser Char st SYMB_OR_MAP
symbMap = do
  s <- symb
  do f <- pToken $ toKey mapsTo
     t <- symb
     return (Symb_map s t $ tokPos f)
    <|> return (Symb s)

-- | Parse a list of comma separated symbols.
symbItems :: GenParser Char st SYMB_ITEMS
symbItems = do
  (is, ps) <- symbs
  return (Symb_items is $ catRange ps)

-- | parse a comma separated list of symbols
symbs :: GenParser Char st ([SYMB], [Token])
symbs = do
       s <- symb
       do c <- commaT `followedWith` symb
          (is, ps) <- symbs
          return (s : is, c : ps)
         <|> return ([s], [])

-- | parse a list of symbol mappings
symbMapItems :: GenParser Char st SYMB_MAP_ITEMS
symbMapItems = do
  (is, ps) <- symbMaps
  return (Symb_map_items is $ catRange ps)

-- | parse a comma separated list of symbol mappings
symbMaps :: GenParser Char st ([SYMB_OR_MAP], [Token])
symbMaps = do
  s <- symbMap
  do c <- commaT `followedWith` symb
     (is, ps) <- symbMaps
     return (s : is, c : ps)
    <|> return ([s], [])
