{- |
Module      :  $Header$
Description :  Parser for DL logic
Copyright   :  Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser for the DL Concrete Syntax
-}

module DL.ParseDL where

import Common.AnnoState
import Common.Id
import Common.Lexer

import DL.AS

import Text.ParserCombinators.Parsec

casl_dl_keywords :: [String]
casl_dl_keywords = ["Class:", "xor", "or", "and", "not", "that", "some",
                    "only", "min", "max", "exactly", "value", "has", 
                    "onlysome", "SubclassOf:","EquivalentTo:",
                    "DisjointWith:","Domain:","Range:","ValuePartition:",
                    "ObjectProperty:","Characteristics:","InverseFunctional",
                    "SameAs:","Equivalent:","Symmetric","Transitive","DataPropertry",
                    "Paraphrase:"]

-- | parse a simple word not in 'casl_dl_keywords'
csvarId :: [String] -> GenParser Char st Token
csvarId ks = pToken (reserved (ks++casl_dl_keywords) scanAnyWords)

stringLit :: GenParser Char st [Char]
stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'

-- | parser for Concepts
pDLConcept :: GenParser Char (AnnoState st) DLConcept
pDLConcept = do
  chainr1 orConcept (asKey "xor" >> return DLXor)
    where
      orConcept :: GenParser Char (AnnoState st) DLConcept
      orConcept = do 
               chainr1 andConcept (asKey "or" >> return DLOr)
                       
      andConcept :: GenParser Char (AnnoState st) DLConcept 
      andConcept = do
               chainr1 notConcept (asKey "and" >> return DLAnd)

      notConcept :: GenParser Char (AnnoState st) DLConcept
      notConcept = do
               asKey "not"
               i <- infixCps
               return $ DLNot i
             <|> infixCps

      infixCps :: GenParser Char (AnnoState st) DLConcept
      infixCps = do
               i <- relationP
               case i of
                 DLThat _ _ -> restCps i
                 _ -> option i (restCps i)

      relationP :: GenParser Char (AnnoState st) DLConcept
      relationP = do
               p <- primC 
               option p $ do 
                    asKey "that"
                    p2 <- primC
                    return (DLThat p p2)

      primC :: GenParser Char (AnnoState st) DLConcept
      primC = do
               fmap (\x -> DLClassId $ mkId (x:[])) (csvarId casl_dl_keywords)
             <|> 
             do
               between oParenT cParenT pDLConcept
             <|> 
             do
               oBraceT
               is <- sepBy1 (csvarId casl_dl_keywords) commaT
               cBraceT
               return $ DLOneOf $ map (mkId . (: [])) is

      restCps :: DLConcept -> GenParser Char (AnnoState st) DLConcept
      restCps i = do
               asKey "some"
               p <- relationP
               return $ DLSome i p                  
             <|>  do
               asKey "only"
               p <- relationP
               return $ DLOnly i p 
             <|>  do
               asKey "has"
               p <- relationP
               return $ DLHas i p 
             <|> do
               asKey "min"
               p <- fmap read $ many1 digit
               return $ DLMin i p 
             <|> do
               asKey "max"
               p <- fmap read $ many1 digit
               return $ DLMin i p 
             <|> do
               asKey "exactly"
               p <- fmap read $ many1 digit
               return $ DLMin i p
             <|> do
               asKey "value"
               p <- csvarId casl_dl_keywords
               return $ DLValue i (simpleIdToId p)
             <|> do
               asKey "onlysome"
               oBracketT
               is <- sepBy1 pDLConcept commaT
               cBracketT
               return $ DLOnlysome i is

-- | Auxiliary parser for classes
cscpParser :: GenParser Char (AnnoState st) DLClassProperty
cscpParser = 
    do 
      try $ string "SubclassOf:" 
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLSubClassof s
    <|>
    do
      try $ string "EquivalentTo:" 
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLEquivalentTo s
    <|>
    do
      try $ string "DisjointWith:" 
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLDisjointWith s

-- ^ The CASL_DL Syntax Parser for basic items
csbiParse :: GenParser Char (AnnoState st) DLBasicItem
csbiParse = 
    do 
      try $ string "Class:"
      spaces
      cId   <- csvarId casl_dl_keywords
      props <- many cscpParser
      para <- parsePara
      return $ DLClass (simpleIdToId cId) props para
    <|> 
    do
      try $ string "ValuePartition:"
      spaces
      cId   <- csvarId casl_dl_keywords
      oBracketT
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      cBracketT
      para <- parsePara
      return $ DLValPart (simpleIdToId cId) (map (mkId . (: [])) is) para
    <|> 
    do
      try $ string "ObjectProperty:"
      spaces
      cId   <- csvarId casl_dl_keywords
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRel
      csChars <- parseDLChars
      para <- parsePara
      return $ DLObjectProperty (simpleIdToId cId) dom ran probRel csChars para
    <|> 
    do
      try $ string "DataProperty:"
      spaces
      cId   <- csvarId casl_dl_keywords
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRelD
      csCharsD <- parseDLCharsD
      para <- parsePara
      return $ DLDataProperty (simpleIdToId cId) dom ran probRel csCharsD para
    <|>
    do
      try $ string "Individual:"
      spaces
      iId <- csvarId casl_dl_keywords
      ty  <- parseType
      facts <- parseFacts
      indrel <- csIndRels
      para <- parsePara
      return $ DLIndividual (simpleIdToId iId) ty facts indrel para

-- | Parser for characteristics for data props
-- | Parser for lists of characteristics
parseDLCharsD :: GenParser Char st (Maybe DLChars)
parseDLCharsD = 
    do 
      try $ string "Characteristics:"
      spaces
      chars <- csCharD
      return (Just $ chars)
    <|>
    do
      return Nothing
    where
      csCharD :: GenParser Char st DLChars
      csCharD =
          do
            try $ string "Functional"
            spaces 
            return DLFunctional

-- | Parser for lists of characteristics
parseDLChars :: GenParser Char st [DLChars]
parseDLChars = 
    do 
      try $ string "Characteristics:"
      spaces
      chars <- sepBy csChar commaT
      return chars
    <|>
    do
      return []
    where
      csChar :: GenParser Char st DLChars
      csChar =
          do
            try $ string "Functional"
            spaces 
            return DLFunctional
          <|>
          do
            try $ string "InverseFunctional"
            spaces
            return DLInvFuntional
          <|>
          do
            try $ string "Symmetric"
            spaces
            return DLInvFuntional
          <|>
          do
            try $ string "Transitive"
            spaces
            return DLInvFuntional

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
csPropsRel :: GenParser Char st DLPropsRel
csPropsRel =
    do
      try $ string "SubPropertyOf:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLSubProperty $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Inverses:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLInverses $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Equivalent:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLEquivalent $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Disjoint:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLDisjoint $ map (mkId . (: [])) is

-- | Parser for property relations
csPropsRelD :: GenParser Char st DLPropsRel
csPropsRelD =
    do
      try $ string "SubPropertyOf:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLSubProperty $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Equivalent:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLEquivalent $ map (mkId . (: [])) is
    <|>
    do
      try $ string "Disjoint:"
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLDisjoint $ map (mkId . (: [])) is

-- | Parser for types
parseType :: GenParser Char st (Maybe DLType)
parseType =
    do
      try $ string "Types:"
      spaces
      ty <- sepBy1 (csvarId casl_dl_keywords) commaT 
      return $ Just (DLType $ map (mkId . (: [])) ty)
    <|> return Nothing

-- | Parser for facts
parseFacts :: GenParser Char st [DLFacts]
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
      parseFact :: GenParser Char st DLFacts
      parseFact = 
          do 
            is <- csvarId casl_dl_keywords
            spaces
            os <- csvarId casl_dl_keywords
            return $ DLPosFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os))
          <|>
          do
            try $ string "not"
            spaces
            is <- csvarId casl_dl_keywords
            spaces
            os <- csvarId casl_dl_keywords
            return $ DLNegFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os))

-- | Parser for relations between individuals
csIndRels :: GenParser Char st [DLIndRel]
csIndRels =
    do
      is <- many csIndRel
      return is
    where
      csIndRel :: GenParser Char st DLIndRel
      csIndRel = 
          do
            try $ string "DifferentFrom:"
            spaces
            is <- sepBy1 (csvarId casl_dl_keywords) commaT
            return $ DLDifferentFrom $ map (mkId . (: [])) is
          <|>
          do
            try $ string "SameAs:"
            spaces
            is <- sepBy1 (csvarId casl_dl_keywords) commaT
            return $ DLDifferentFrom $ map (mkId . (: [])) is    

-- ^ the toplevel parser for CASL_DL Syntax
csbsParse :: GenParser Char (AnnoState st) DLBasic
csbsParse = 
    do 
      biS <- many csbiParse
      return $ DLBasic biS

testParse :: [Char] -> Either ParseError DLBasic
testParse st = runParser csbsParse (emptyAnnos ()) "" st

longTest :: IO (Either ParseError DLBasic)
longTest = do x <- (readFile "DL/test/Pizza.het"); return $ testParse x

-- ^ Parser for Paraphrases
parsePara :: GenParser Char st (Maybe DLPara)
parsePara = 
	do
		try $ string "Paraphrase:"
		spaces
		paras <- many1 $ parseMultiPara
		return $ Just $ DLPara paras
	<|> do
		return Nothing	
	where
	parseMultiPara :: GenParser Char st (ISOLangCode, [Char])
	parseMultiPara = 
		do
			pp <- stringLit
			spaces 
			lg <- parseLang
			return (lg, pp)

	parseLang ::  GenParser Char st ISOLangCode
	parseLang = 
		do
			try $ oBracketT
			string "lang:"
			spaces
			lg1 <- letter
			lg2 <- letter
			spaces
			cBracketT	
			return ([lg1] ++ [lg2])
		<|> return "en"

instance AParsable DLBasicItem where
    aparser = csbiParse

instance AParsable DLBasic where
    aparser = csbsParse

instance AParsable DLClassProperty where
    aparser = cscpParser

instance AParsable DLConcept where
    aparser = pDLConcept
