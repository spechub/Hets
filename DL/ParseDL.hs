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
import DL.DLKeywords
import Common.AS_Annotation
import Control.Monad

import DL.AS

import Text.ParserCombinators.Parsec

-- | parse a simple word not in 'casl_dl_keywords'
csvarId :: [String] -> AParser st Token
csvarId ks =
     do
        tk <- pToken (reserved (ks++casl_dl_keywords) (scanAnyWords <++> option "" (string ":")))
        addAnnos
        return tk

stringLit :: AParser st [Char]
stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'

-- | parser for Concepts
pDLConcept :: AParser st DLConcept
pDLConcept = do
  chainr1 orConcept (asKey dlxor >> return (\x y -> DLXor x y nullRange))

orConcept :: AParser st DLConcept
orConcept = do
           chainr1 andConcept (asKey dlor >> return (\x y -> DLOr x y nullRange))

andConcept :: AParser st DLConcept
andConcept = do
           chainr1 notConcept ((asKey dland <|> asKey dlthat) >> return (\x y -> DLAnd x y nullRange))

notConcept :: AParser st DLConcept
notConcept = do
           asKey dlnot
           i <- infixCps
           return $ DLNot i nullRange
         <|> infixCps

infixCps :: AParser st DLConcept
infixCps = 
          try (do
           i <- relationP
           restCps i)
         <|> primC

relationP :: AParser st Id
relationP = do
        fmap (\x -> mkId (x:[])) (csvarId [])
        

primC :: AParser st DLConcept
primC = do
           fmap (\x -> DLClassId (mkId (x:[])) nullRange) (csvarId [])
         <|>
         do
           between oParenT cParenT pDLConcept
         <|>
         do
           oBraceT
           is <- sepBy1 (csvarId casl_dl_keywords) commaT
           cBraceT
           return $ DLOneOf (map (mkId . (: [])) is) nullRange

restCps :: Id -> AParser st DLConcept
restCps i = do
           asKey dlsome
           p <- primC
           return $ DLSome i p nullRange
         <|>  do
           asKey dlonly
           p <- primC
           return $ DLOnly i p nullRange
         <|>  do
           asKey dlhas
           p <- primC
           return $ DLHas i p nullRange
         <|> do
           asKey dlmin
           p <- fmap read $ many1 digit
           spaces
           return $ DLMin i p Nothing nullRange
         <|> do
           asKey dlmax
           p <- fmap read $ many1 digit
           spaces
           cp <- maybe_primC
           return $ DLMax i p cp nullRange
         <|> do
           asKey dlexact
           p <- fmap read $ many1 digit
           spaces
           return $ DLExactly i p Nothing nullRange
         <|> do
           asKey dlvalue
           p <- csvarId []
           return $ DLValue i (simpleIdToId p) nullRange
         <|> do
           asKey dlonlysome
           oBracketT
           is <- sepBy1 pDLConcept commaT
           cBracketT
           return $ DLOnlysome i is nullRange

maybe_primC :: AParser st (Maybe DLConcept)
maybe_primC = 
    do
        pc <- primC
        return (Just pc)
  <|>
    return Nothing
    
-- | Auxiliary parser for classes
cscpParser :: AParser st DLClassProperty
cscpParser =
    do
      try $ string dlSub
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLSubClassof s nullRange
    <|>
    do
      try $ string dlEquivTo
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLEquivalentTo s nullRange
    <|>
    do
      try $ string dlDisjoint
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLDisjointWith s nullRange

makeAnnoted :: [Annotation] -> [Annotation] -> a -> Annoted a
makeAnnoted l r sen = Annoted
                          {
                            item = sen
                          , l_annos = l
                          , r_annos = r
                          , opt_pos = nullRange
                          }


-- ^ The CASL_DL Syntax Parser for basic items
csbiParse :: AParser st (Annoted DLBasicItem)
csbiParse =
    do
      try $ string dlclass
      spaces
      lano <- getAnnos
      cId   <- csvarId [dlThing, dlNothing]
      props <- many cscpParser
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLClass (simpleIdToId cId) props para nullRange
    <|>
    do
      try $ string dlObjProp
      spaces
      lano <- getAnnos
      cId   <- csvarId casl_dl_keywords
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRel
      csChars <- parseDLChars
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLObjectProperty (simpleIdToId cId) dom ran probRel csChars para nullRange
    <|>
    do
      lano <- getAnnos
      try $ string dlDataProp
      spaces
      cId   <- csvarId casl_dl_keywords
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRelD
      csCharsD <- parseDLCharsD
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLDataProperty (simpleIdToId cId) dom ran probRel csCharsD para nullRange
    <|>
    do
      try $ string dlIndi
      spaces
      lano <- getAnnos
      iId <- csvarId casl_dl_keywords
      ty  <- parseType
      facts <- parseFacts
      indrel <- csIndRels
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLIndividual (simpleIdToId iId) ty facts indrel para nullRange
    <|>
    do
      try $ string dlMultiIndi
      spaces
      lano <- getAnnos
      iIds <- sepBy1 (csvarId []) commaT
      ty <- parseType
      facts <- parseFacts
      dlEq <- parseDLEquality
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLMultiIndi (map simpleIdToId iIds) ty facts dlEq para nullRange

parseDLEquality :: AParser st (Maybe DLEquality)
parseDLEquality =
    do
        try $ string dlEquality
        spaces
        do
            try $ string dlEqualI
            spaces
            return $ Just DLSame
        <|>
        do
            try $ string dlDiffI
            spaces
            return $ Just DLDifferent
    <|>
        return Nothing

-- | Parser for characteristics for data props
-- | Parser for lists of characteristics
parseDLCharsD :: AParser st (Maybe DLChars)
parseDLCharsD =
    do
      try $ string dlChar
      spaces
      chars <- csCharD
      return (Just $ chars)
    <|>
    do
      return Nothing
    where
      csCharD :: AParser st DLChars
      csCharD =
          do
            try $ string dlFunc
            spaces
            return DLFunctional

-- | Parser for lists of characteristics
parseDLChars :: AParser st [DLChars]
parseDLChars =
    do
      try $ string dlChar
      spaces
      chars <- sepBy csChar commaT
      return chars
    <|>
    do
      return []
    where
      csChar :: AParser st DLChars
      csChar =
          do
            try $ string dlFunc
            spaces
            return DLFunctional
          <|>
          do
            try $ string dlInvFunc
            spaces
            return DLInvFuntional
          <|>
          do
            try $ string dlSym
            spaces
            return DLSymmetric
          <|>
          do
            try $ string dlTrans
            spaces
            return DLTransitive

-- | Parser for domain
csDomain :: AParser st (Maybe DLConcept)
csDomain =
    do
      try $ string dlDomain
      spaces
      dID <- pDLConcept
      return $ Just dID
    <|>
    do
      return Nothing

-- | Parser for range
csRange :: AParser st (Maybe DLConcept)
csRange =
    do
      try $ string dlRange
      spaces
      dID <- pDLConcept
      return $ Just dID
    <|>
    do
      return Nothing

-- | Parser for property relations
csPropsRel :: AParser st DLPropsRel
csPropsRel =
    do
      try $ string dlSubProp
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLSubProperty ( map (mkId . (: [])) is) nullRange
    <|>
    do
      try $ string dlInv
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLInverses (map (mkId . (: [])) is) nullRange
    <|>
     do
      try $ string dlInvOf
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLInverses (map (mkId . (: [])) is) nullRange
    <|>
    do
      try $ string dlEquiv
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLEquivalent (map (mkId . (: [])) is) nullRange
    <|>
    do
      try $ string dlDis
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLDisjoint (map (mkId . (: [])) is) nullRange

-- | Parser for property relations
csPropsRelD :: AParser st DLPropsRel
csPropsRelD =
    do
      try $ string dlSubProp
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLSubProperty ( map (mkId . (: [])) is) nullRange
    <|>
    do
      try $ string dlEquiv
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLEquivalent (map (mkId . (: [])) is) nullRange
    <|>
    do
      try $ string dlDis
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLDisjoint (map (mkId . (: [])) is) nullRange

-- | Parser for types
parseType :: AParser st (Maybe DLType)
parseType =
    do
      (try $ string dlTypes) <|> (try $ string dlType)
      spaces
      ty <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ Just (DLType (map (mkId . (: [])) ty) nullRange)
    <|> return Nothing

-- | Parser for facts
parseFacts :: AParser st [DLFacts]
parseFacts =
    do
      try $ string dlFacts
      spaces
      facts <-  sepBy1 parseFact commaT
      return facts
    <|>
    do
      return []
    where
      parseFact :: AParser st DLFacts
      parseFact =
          do
            is <- csvarId []
            spaces
            os <- csvarId [] <|> fmap mkSimpleId (option "" 
                (choice $ map (string . (: [])) "+-") <++> getNumber <++> option ""
                 (char '.' <:> getNumber))  
            return $ DLPosFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os)) nullRange
          <|>
          do
            try $ string dlnot
            spaces
            is <- csvarId []
            spaces
            os <- csvarId [] <|> fmap mkSimpleId getNumber
            return $ DLNegFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os)) nullRange

-- | Parser for relations between individuals
csIndRels :: AParser st [DLIndRel]
csIndRels =
    do
      is <- many csIndRel
      return is
    where
      csIndRel :: AParser st DLIndRel
      csIndRel =
          do
            try $ string dlDiff
            spaces
            is <- sepBy1 (csvarId casl_dl_keywords) commaT
            return $ DLDifferentFrom (map (mkId . (: [])) is) nullRange
          <|>
          do
            try $ string dlSame
            spaces
            is <- sepBy1 (csvarId casl_dl_keywords) commaT
            return $ DLDifferentFrom (map (mkId . (: [])) is) nullRange

-- ^ the toplevel parser for DL Syntax
csbsParse :: AParser st DLBasic
csbsParse =
    do
      biS <- many csbiParse
      return $ DLBasic biS

testParse :: [Char] -> Either ParseError DLBasic
testParse st = runParser csbsParse (emptyAnnos ()) "" st

longTest :: IO (Either ParseError DLBasic)
longTest = do x <- (readFile "DL/test/Pizza.het"); return $ testParse x

-- ^ Parser for Paraphrases
parsePara :: AParser st (Maybe DLPara)
parsePara =
	do
		try $ string dlPara
		spaces
		paras <- many1 $ parseMultiPara
		return $ Just $ DLPara paras nullRange
	<|> do
		return Nothing	
	where
	parseMultiPara :: AParser st (ISOLangCode, [Char])
	parseMultiPara =
		do
			pp <- stringLit
			spaces
			lg <- parseLang
			return (lg, pp)

	parseLang ::  AParser st ISOLangCode
	parseLang =
		do
			try $ oBracketT
			string dlLang
			spaces
			lg1 <- letter
			lg2 <- letter
			spaces
			cBracketT	
			return ([lg1] ++ [lg2])
		<|> return "en"

instance AParsable (Annoted DLBasicItem) where
    aparser = csbiParse

instance AParsable DLBasic where
    aparser = csbsParse

instance AParsable DLClassProperty where
    aparser = cscpParser

instance AParsable DLConcept where
    aparser = pDLConcept
