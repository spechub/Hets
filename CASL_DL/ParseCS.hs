{- |
Module      :  $Header$
Description :  abstract syntax for CASL_DL logic extension of CASL
Copyright   :  Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser for the CASL_DL Concrete Syntax
-}

module CASL_DL.ParseCS where

import Common.AnnoState
import Common.Id
import Common.Lexer
import Common.Token

import CASL_DL.AS_CASL_DL

import Text.ParserCombinators.Parsec

pCSConcept :: GenParser Char (AnnoState st) CSConcept
pCSConcept = do
  chainr1 orConcept (asKey "xor" >> return CSXor)

orConcept :: GenParser Char (AnnoState st) CSConcept
orConcept = do 
  chainr1 andConcept (asKey "or" >> return CSOr)

andConcept :: GenParser Char (AnnoState st) CSConcept 
andConcept = do
  chainr1 notConcept (asKey "and" >> return CSAnd)

notConcept :: GenParser Char (AnnoState st) CSConcept
notConcept = do
  asKey "not"
  i <- infixCps
  return $ CSNot i
 <|> infixCps

infixCps :: GenParser Char (AnnoState st) CSConcept
infixCps = do
   i <- relationP
   case i of
     CSThat _ _ -> restCps i
     _ -> option i (restCps i)

relationP :: GenParser Char (AnnoState st) CSConcept
relationP = do
   p <- primC 
   option p $ do 
       asKey "that"
       p2 <- primC
       return (CSThat p p2)

primC :: GenParser Char (AnnoState st) CSConcept
primC = do
   fmap CSClassId (parseId [])
  <|> do
   between oParenT cParenT pCSConcept
  <|> do
   oBraceT
   is <- sepBy1 (many1 $ noneOf " ,}") spaces 
   cBraceT
   return $ CSOneOf $ map (mkId . (: []) . mkSimpleId) is

restCps :: CSConcept -> GenParser Char (AnnoState st) CSConcept
restCps i = do
   asKey "some"
   p <- relationP
   return $ CSSome i p 
  <|>  do
    asKey "only"
    p <- relationP
    return $ CSOnly i p 
  <|> do
    asKey "min"
    p <- fmap read $ many1 digit
    return $ CSMin i p 
  <|> do
    asKey "max"
    p <- fmap read $ many1 digit
    return $ CSMin i p 
  <|> do
    asKey "exactly"
    p <- fmap read $ many1 digit
    return $ CSMin i p
  <|> do
    asKey "value"
    p <- parseId[]
    return $ CSValue i p
  <|> do
    asKey "onlysome"
    oBracketT
    is <- sepBy1 pCSConcept commaT
    cBracketT
    return $ CSOnlysome i is

cscpParser :: GenParser Char (AnnoState st) CSClassProperty
cscpParser = 
    do 
      try $ string "SubClassof:" 
      spaces
      s <- pCSConcept
      return $ CSSubClassof s
    <|>
    do
      try $ string "EquivalentTo:" 
      spaces
      s <- pCSConcept
      return $ CSEquivalentTo s
    <|>
    do
      try $ string "DisjointWith:" 
      spaces
      s <- pCSConcept
      return $ CSDisjointWith s

-- ^ The CASL_DL Syntax Parser for basic items
csbiParse :: GenParser Char (AnnoState st) CSBasicItem
csbiParse = 
    do 
      try $ string "Class:"
      spaces
      cId   <- parseId []
      props <- many cscpParser
      return $ CSClass cId props
    <|> 
    do
      try $ string "ValuePartition:"
      spaces
      cId   <- parseId []
      oBracketT
      is <- sepBy1 (many1 $ noneOf " ,}]") spaces 
      cBracketT
      return $ CSValPart cId $ map (mkId . (: []) . mkSimpleId) is
    <|> 
    do
      try $ string "ObjectProperty:"
      spaces
      cId   <- parseId []
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRel
      return $ CSObjectProperty cId dom ran probRel

csDomain :: GenParser Char st (Maybe Id)
csDomain = 
    do 
      try $ string "Domain:"
      spaces
      dID <- parseId []
      return $ Just dID
    <|>
    do
      return Nothing

csRange :: GenParser Char st (Maybe Id)
csRange = 
    do 
      try $ string "Range:"
      spaces
      dID <- parseId []
      return $ Just dID
    <|>
    do
      return Nothing
      
csPropsRel :: GenParser Char st CSPropsRel
csPropsRel =
    do
      try $ string "SubPropertyOf:"
      spaces
      is <- sepBy1 (many1 $ noneOf " ,}") spaces 
      return $ CSSubProperty $ map (mkId . (: []) . mkSimpleId) is
    <|>
    do
      try $ string "Inverses:"
      spaces
      is <- sepBy1 (many1 $ noneOf " ,}") spaces 
      return $ CSInverses $ map (mkId . (: []) . mkSimpleId) is

-- ^ the toplevel parser for CASL_DL Syntax
csbsParse :: GenParser Char (AnnoState st) CSBasic
csbsParse = 
    do 
      biS <- many csbiParse
      return $ CSBasic biS

instance AParsable CSBasicItem where
    aparser = csbiParse

instance AParsable CSBasic where
    aparser = csbsParse

instance AParsable CSClassProperty where
    aparser = cscpParser

instance AParsable CSConcept where
    aparser = pCSConcept
