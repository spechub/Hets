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

import CASL_DL.AS_CASL_DL

import Text.ParserCombinators.Parsec

casl_dl_keywords :: [String]
casl_dl_keywords = ["Class:", "xor", "or", "and", "not", "that", "some",
                    "only", "min", "max", "exactly", "value", "has", 
                    "onlysome", "SubclassOf:","EquivalentTo:",
                    "DisjointWith:","Domain:","Range:","ValuePartition:",
                    "ObjectProperty:","Characteristics:","InverseFunctional",
                    "SameAs:","Equivalent:","Symmetric","Transitive","DataPropertry"]

-- | parse a simple word not in 'casl_dl_keywords'
csvarId :: [String] -> GenParser Char st Token
csvarId ks = pToken (reserved (ks++casl_dl_keywords) scanAnyWords)

-- | parser for Concepts
pCSConcept :: GenParser Char (AnnoState st) CSConcept
pCSConcept = do
  chainr1 orConcept (asKey "xor" >> return CSXor)
    where
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
               fmap (\x -> CSClassId $ mkId (x:[])) (csvarId casl_dl_keywords)
             <|> 
             do
               between oParenT cParenT pCSConcept
             <|> 
             do
               oBraceT
               is <- sepBy1 (csvarId casl_dl_keywords) commaT
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
             <|>  do
               asKey "has"
               p <- relationP
               return $ CSHas i p 
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
               p <- csvarId casl_dl_keywords
               return $ CSValue i (simpleIdToId p)
             <|> do
               asKey "onlysome"
               oBracketT
               is <- sepBy1 pCSConcept commaT
               cBracketT
               return $ CSOnlysome i is

-- | Auxiliary parser for classes
cscpParser :: GenParser Char (AnnoState st) CSClassProperty
cscpParser = 
    do 
      try $ string "SubclassOf:" 
      spaces
      s <- sepBy pCSConcept commaT
      return $ CSSubClassof s
    <|>
    do
      try $ string "EquivalentTo:" 
      spaces
      s <- sepBy pCSConcept commaT
      return $ CSEquivalentTo s
    <|>
    do
      try $ string "DisjointWith:" 
      spaces
      s <- sepBy pCSConcept commaT
      return $ CSDisjointWith s

-- ^ The CASL_DL Syntax Parser for basic items
csbiParse :: GenParser Char (AnnoState st) CSBasicItem
csbiParse = 
    do 
      try $ string "Class:"
      spaces
      cId   <- csvarId casl_dl_keywords
      props <- many cscpParser
      return $ CSClass (simpleIdToId cId) props
    <|> 
    do
      try $ string "ValuePartition:"
      spaces
      cId   <- csvarId casl_dl_keywords
      oBracketT
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      cBracketT
      return $ CSValPart (simpleIdToId cId) $ map (mkId . (: [])) is
    <|> 
    do
      try $ string "ObjectProperty:"
      spaces
      cId   <- csvarId casl_dl_keywords
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRel
      csChars <- parseCSChars
      return $ CSObjectProperty (simpleIdToId cId) dom ran probRel csChars
    <|> 
    do
      try $ string "DataProperty:"
      spaces
      cId   <- csvarId casl_dl_keywords
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRel
      csChars <- parseCSChars
      return $ CSObjectProperty (simpleIdToId cId) dom ran probRel csChars
    <|>
    do
      try $ string "Individual:"
      spaces
      iId <- csvarId casl_dl_keywords
      ty  <- parseType
      facts <- parseFacts
      indrel <- csIndRels
      return $ CSIndividual (simpleIdToId iId) ty facts indrel

-- | Parser for lists of characteristics
parseCSChars :: GenParser Char st [CSChars]
parseCSChars = 
    do 
      try $ string "Characteristics:"
      spaces
      chars <- sepBy csChar commaT
      return chars
    <|>
    do
      return []
    where
      csChar :: GenParser Char st CSChars
      csChar =
          do
            try $ string "Functional"
            spaces 
            return CSFunctional
          <|>
          do
            try $ string "InverseFunctional"
            spaces
            return CSInvFuntional
          <|>
          do
            try $ string "Symmetric"
            spaces
            return CSInvFuntional
          <|>
          do
            try $ string "Transitive"
            spaces
            return CSInvFuntional

-- | Parser for domain
csDomain :: GenParser Char st (Maybe Id)
csDomain = 
    do 
      try $ string "Domain:"
      spaces
      dID <- csvarId casl_dl_keywords
      return $ Just (simpleIdToId dID)
    <|>
    do
      return Nothing

-- | Parser for range
csRange :: GenParser Char st (Maybe Id)
csRange = 
    do 
      try $ string "Range:"
      spaces
      dID <- csvarId casl_dl_keywords
      return $ Just (simpleIdToId dID)
    <|>
    do
      return Nothing
      
-- | Parser for property relations
csPropsRel :: GenParser Char st CSPropsRel
csPropsRel =
    do
      try $ string "SubPropertyOf:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ CSSubProperty $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Inverses:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ CSInverses $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Equivalent:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ CSEquivalent $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Disjoint:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ CSDisjoint $ map (mkId . (: [])) is

-- | Parser for types
parseType :: GenParser Char st (Maybe CSType)
parseType =
    do
      try $ string "Types:"
      spaces
      ty <- sepBy1 (csvarId casl_dl_keywords) commaT 
      return $ Just (CSType $ map (mkId . (: [])) ty)
    <|> return Nothing

-- | Parser for facts
parseFacts :: GenParser Char st [CSFacts]
parseFacts = 
    do 
      try $ string "Facts:"
      spaces
      facts <-  sepBy1 parseFact commaT
      return facts
    <|>
    do
      return []
    where
      parseFact :: GenParser Char st CSFacts
      parseFact = 
          do 
            is <- csvarId casl_dl_keywords
            spaces
            os <- csvarId casl_dl_keywords
            return $ CSPosFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os))
          <|>
          do
            try $ string "not"
            spaces
            is <- csvarId casl_dl_keywords
            spaces
            os <- csvarId casl_dl_keywords
            return $ CSNegFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os))

-- | Parser for relations between individuals
csIndRels :: GenParser Char st [CSIndRel]
csIndRels =
    do
      is <- many csIndRel
      return is
    where
      csIndRel :: GenParser Char st CSIndRel
      csIndRel = 
          do
            try $ string "DifferentFrom:"
            spaces
            is <- sepBy1 (csvarId casl_dl_keywords) commaT
            return $ CSDifferentFrom $ map (mkId . (: [])) is
          <|>
          do
            try $ string "SameAs:"
            spaces
            is <- sepBy1 (csvarId casl_dl_keywords) commaT
            return $ CSDifferentFrom $ map (mkId . (: [])) is    

-- ^ the toplevel parser for CASL_DL Syntax
csbsParse :: GenParser Char (AnnoState st) CSBasic
csbsParse = 
    do 
      biS <- many csbiParse
      return $ CSBasic biS

testParse :: [Char] -> Either ParseError CSBasic
testParse st = runParser csbsParse (emptyAnnos ()) "" st

longTest :: IO (Either ParseError CSBasic)
longTest = do x <- (readFile "CASL_DL/test/Pizza.het"); return $ testParse x

instance AParsable CSBasicItem where
    aparser = csbiParse

instance AParsable CSBasic where
    aparser = csbsParse

instance AParsable CSClassProperty where
    aparser = cscpParser

instance AParsable CSConcept where
    aparser = pCSConcept
