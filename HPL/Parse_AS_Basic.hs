{- |
Module      :  ./HPL/Parse_AS_Basic.hs
Description :  Parser for basic specs
Copyright   :  (c) Mihai Codescu, IMAR, 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for hybrid propositional logic

-}

module HPL.Parse_AS_Basic
  ( basicSpec                      -- Parser for basic specs
  , symbItems
  , symbMapItems
  , impFormula
  ) where

import Common.AnnoState
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import Common.Parsec
import Common.GlobalAnnotations (PrefixMap)
import Common.Doc(prettyAt)

import Debug.Trace

import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified HPL.AS_BASIC_HPL as HBasic
import Text.ParserCombinators.Parsec

propKeywords :: [String]
propKeywords = criticalKeywords ++
  [ propS
  , notS
  , trueS
  , falseS
  , nomS
  , boxS
  , diamondS
  ]

-- | Toplevel parser for basic specs
basicSpec :: PrefixMap -> AParser st HBasic.BASIC_SPEC
basicSpec _ =
  fmap HBasic.Basic_spec (annosParser parseBasicItems)
  <|> (oBraceT >> cBraceT >> return (HBasic.Basic_spec []))

-- | Parser for basic items
parseBasicItems :: AParser st HBasic.BASIC_ITEMS
parseBasicItems = parsePredDecl <|> parseNomDecl <|> parseAxItems

-- | parser for predicate declarations
parsePredDecl :: AParser st HBasic.BASIC_ITEMS
parsePredDecl = fmap HBasic.Pred_decl predItem

-- | parser for nominal declarations
parseNomDecl :: AParser st HBasic.BASIC_ITEMS
parseNomDecl = fmap HBasic.Nom_decl nomItem

-- | parser for Axiom_items
parseAxItems :: AParser st HBasic.BASIC_ITEMS
parseAxItems = do
       d <- dotT
       (fs, ds) <- aFormula `separatedBy` dotT
       (_, an) <- optSemi
       let _ = catRange (d : ds)
           ns = init fs ++ [appendAnno (last fs) an]
       trace (concatMap (\x -> show x ++ "\n" ) ns) $ 
        return $ HBasic.Axiom_items ns

-- | Any word to token
propId :: GenParser Char st Token
propId = pToken $ reserved propKeywords scanAnyWords

-- | parser for predicates = propositions
predItem :: AParser st PBasic.PRED_ITEM
predItem = do
      v <- asKey (propS ++ sS) <|>
           asKey propS
      (ps, cs) <- propId `separatedBy` anComma
      return $ PBasic.Pred_item ps $ catRange $ v : cs

-- | parser for nominals
nomItem :: AParser st HBasic.NOM_ITEM
nomItem = do
      v <- asKey (nomS ++ sS) <|>
           asKey nomS
      (ps, cs) <- propId `separatedBy` anComma
      return $ HBasic.Nom_item ps $ catRange $ v : cs


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

-- | Parser for box @[]@
boxKey :: AParser st Token
boxKey = asKey boxS

-- | Parser for diamond @<>@
diamondKey :: AParser st Token
diamondKey = asKey diamondS

-- | Parser for at 
atKey :: AParser st Token
atKey = asKey asP

-- | Parser for primitive formulae
primFormula :: AParser st HBasic.FORMULA
primFormula =
    do c <- trueKey
       return (HBasic.Prop_formula $ PBasic.True_atom $ tokPos c)
    <|>
    do c <- falseKey
       return (HBasic.Prop_formula $ PBasic.False_atom $ tokPos c)
    <|>
    do c <- notKey <|> negKey <?> "\"not\""
       k <- primFormula
       return (HBasic.Negation k $ tokPos c)
    <|> parenFormula
    <|> 
     do c <- diamondKey
        k <- impFormula
        return (HBasic.DiamondFormula k $ tokPos c)
    <|> 
     do c <- boxKey
        k <- impFormula
        return $ HBasic.BoxFormula k $ tokPos c
    <|> 
     do c <- atKey
        n <- propId
        _ <- colonT
        k <- impFormula
        return $ HBasic.AtState n k $ tokPos c
    <|> fmap (HBasic.Prop_formula . PBasic.Predication) propId
         -- NOTE!!!: we parse nominal sentences as predications
         -- in the static analysis, we must correct this! 

-- | Parser for formulae containing 'and' and 'or'
andOrFormula :: AParser st HBasic.FORMULA
andOrFormula = do
  f <- primFormula
  do c <- andKey
     (fs, ps) <- primFormula `separatedBy` andKey
     return $  
       HBasic.Conjunction 
           (f : fs)  $ catRange $ c : ps
   <|> do
     c <- orKey
     (fs, ps) <- primFormula `separatedBy` orKey
     return $  
       HBasic.Disjunction (f : fs) $ catRange $ c : ps
   <|> return f

-- | Parser for formulae with implications
impFormula :: AParser st HBasic.FORMULA
impFormula = do
  f <- andOrFormula
  do c <- implKey
     (fs, ps) <- andOrFormula `separatedBy` implKey
     return . makeImpl (f : fs) . catPosAux $ c : ps
   <|> do
     c <- equivKey
     g <- andOrFormula
     return . HBasic.Equivalence f g $ tokPos c
   <|> return f
  where
  makeImpl [f, g] p = HBasic.Implication f g (Range p)
  makeImpl (f : r) (c : p) = HBasic.Implication f (makeImpl r p) (Range [c])
  makeImpl _ _ = error "makeImpl got illegal argument"

-- | Parser for formulae with parentheses
parenFormula :: AParser st HBasic.FORMULA
parenFormula = do
       oParenT << addAnnos
       f <- impFormula << addAnnos
       cParenT >> return f

-- | Toplevel parser for formulae
aFormula :: AParser st (Annoted HBasic.FORMULA)
aFormula = allAnnoParser impFormula

-- TODO: some functions below are duplicated with Propositional. Keep them once

-- | parsing a prop symbol
symb :: GenParser Char st PBasic.SYMB
symb = fmap PBasic.Symb_id propId

-- | parsing one symbol or a mapping of one to a second symbol
symbMap :: GenParser Char st PBasic.SYMB_OR_MAP
symbMap = do
  s <- symb
  do f <- pToken $ toKey mapsTo
     t <- symb
     return (PBasic.Symb_map s t $ tokPos f)
    <|> return (PBasic.Symb s)

-- | Parse a list of comma separated symbols.
symbItems :: GenParser Char st PBasic.SYMB_ITEMS
symbItems = do
  (is, ps) <- symbs
  return (PBasic.Symb_items is $ catRange ps)

-- | parse a comma separated list of symbols
symbs :: GenParser Char st ([PBasic.SYMB], [Token])
symbs = do
       s <- symb
       do c <- commaT `followedWith` symb
          (is, ps) <- symbs
          return (s : is, c : ps)
         <|> return ([s], [])

-- | parse a list of symbol mappings
symbMapItems :: GenParser Char st PBasic.SYMB_MAP_ITEMS
symbMapItems = do
  (is, ps) <- symbMaps
  return (PBasic.Symb_map_items is $ catRange ps)

-- | parse a comma separated list of symbol mappings
symbMaps :: GenParser Char st ([PBasic.SYMB_OR_MAP], [Token])
symbMaps = do
  s <- symbMap
  do c <- commaT `followedWith` symb
     (is, ps) <- symbMaps
     return (s : is, c : ps)
    <|> return ([s], [])

