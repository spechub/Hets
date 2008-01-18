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

casl_dl_keywords :: [String]
casl_dl_keywords = ["Class:", "xor", "or", "and", "not", "that", "some",
                    "only", "min", "max", "exactly", "value",
                    "onlysome", "SubclassOf:","EquivalentTo:",
                    "DisjointWith:","Domain:","Range:","ValuePartition",
                    "ObjectProperty"]

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
   fmap (\x -> CSClassId $ mkId (x:[])) (varId casl_dl_keywords)
  <|> do
   between oParenT cParenT pCSConcept
  <|> do
   oBraceT
   is <- sepBy1 (varId casl_dl_keywords) commaT
   cBraceT
   return $ CSOneOf $ map (mkId . (: [])) is

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
    p <- varId casl_dl_keywords
    return $ CSValue i (simpleIdToId p)
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
      cId   <- varId casl_dl_keywords
      props <- many cscpParser
      return $ CSClass (simpleIdToId cId) props
    <|> 
    do
      try $ string "ValuePartition:"
      spaces
      cId   <- varId casl_dl_keywords
      oBracketT
      is <- sepBy1 (varId casl_dl_keywords) commaT
      cBracketT
      return $ CSValPart (simpleIdToId cId) $ map (mkId . (: [])) is
    <|> 
    do
      try $ string "ObjectProperty:"
      spaces
      cId   <- varId casl_dl_keywords
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRel
      return $ CSObjectProperty (simpleIdToId cId) dom ran probRel
    <|>
    do
      try $ string "Individual:"
      spaces
      iId <- varId casl_dl_keywords
      ty  <- parseType
      facts <- parseFacts
      indrel <- csIndRels
      return $ CSIndividual (simpleIdToId iId) ty facts indrel

csDomain :: GenParser Char st (Maybe Id)
csDomain = 
    do 
      try $ string "Domain:"
      spaces
      dID <- varId casl_dl_keywords
      return $ Just (simpleIdToId dID)
    <|>
    do
      return Nothing

csRange :: GenParser Char st (Maybe Id)
csRange = 
    do 
      try $ string "Range:"
      spaces
      dID <- varId casl_dl_keywords
      return $ Just (simpleIdToId dID)
    <|>
    do
      return Nothing
      
csPropsRel :: GenParser Char st CSPropsRel
csPropsRel =
    do
      try $ string "SubPropertyOf:"
      spaces
      is <- sepBy1 (varId casl_dl_keywords) commaT
      return $ CSSubProperty $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Inverses:"
      spaces
      is <- sepBy1 (varId casl_dl_keywords) commaT
      return $ CSInverses $ map (mkId . (: [])) is

parseType :: GenParser Char st (Maybe CSType)
parseType =
    do
      try $ string "Types:"
      spaces
      ty <- sepBy1 (varId casl_dl_keywords) commaT 
      return $ Just (CSType $ map (mkId . (: [])) ty)
    <|> return Nothing

parseFacts :: GenParser Char st [(Id, Id)]
parseFacts = 
    do 
      try $ string "Facts:"
      spaces
      facts <-  sepBy1 parseFact commaT
      return facts
    <|>
    do
      return []

parseFact :: GenParser Char st (Id, Id)
parseFact = 
    do 
      is <- varId casl_dl_keywords
      spaces
      os <- varId casl_dl_keywords
      return $ (\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os)

csIndRels :: GenParser Char st [CSIndRel]
csIndRels =
    do
      is <- many csIndRel
      return is

csIndRel :: GenParser Char st CSIndRel
csIndRel = 
    do
      try $ string "DifferentFrom:"
      spaces
      is <- sepBy1 (varId casl_dl_keywords) commaT
      return $ CSDifferentFrom $ map (mkId . (: [])) is

-- ^ the toplevel parser for CASL_DL Syntax
csbsParse :: GenParser Char (AnnoState st) CSBasic
csbsParse = 
    do 
      biS <- many csbiParse
      return $ CSBasic biS

testParse :: [Char] -> Either ParseError CSBasic
testParse st = runParser csbsParse (emptyAnnos ()) "" st

hellishTest :: Either ParseError CSBasic
hellishTest = testParse "ObjectProperty: Hell\nDomain: Limbo\nRange: Purgatory\nInverses: Heaven\nClass: Heaven\nIndividual:Satan\nTypes:Demon,FallenAngel\nFacts: hasEvil Satan\nIndividual:Parsons\n\n\nTypes:Stupid,Doubleplusgoodduckspeaker,Goodthinker\nFacts:goingto Hell"

instance AParsable CSBasicItem where
    aparser = csbiParse

instance AParsable CSBasic where
    aparser = csbsParse

instance AParsable CSClassProperty where
    aparser = cscpParser

instance AParsable CSConcept where
    aparser = pCSConcept
