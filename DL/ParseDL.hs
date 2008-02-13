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

import DL.AS

import Text.ParserCombinators.Parsec

-- | parse a simple word not in 'casl_dl_keywords'
csvarId :: [String] -> AParser st Token
csvarId ks =
     do
        tk <- pToken (reserved (ks++casl_dl_keywords) scanAnyWords)
        addAnnos
        return tk

stringLit :: AParser st [Char]
stringLit = enclosedBy (flat $ many $ single (noneOf "\\\"")
                        <|> char '\\' <:> single anyChar) $ char '\"'

-- | parser for Concepts
pDLConcept :: AParser st DLConcept
pDLConcept = do
  chainr1 orConcept (asKey dlxor >> return DLXor)
    where
      orConcept :: AParser st DLConcept
      orConcept = do
               chainr1 andConcept (asKey dlor >> return DLOr)

      andConcept :: AParser st DLConcept
      andConcept = do
               chainr1 notConcept (asKey dland >> return DLAnd)

      notConcept :: AParser st DLConcept
      notConcept = do
               asKey dlnot
               i <- infixCps
               return $ DLNot i
             <|> infixCps

      infixCps :: AParser st DLConcept
      infixCps = do
               i <- relationP
               case i of
                 DLThat _ _ -> restCps i
                 _ -> option i (restCps i)

      relationP :: AParser st DLConcept
      relationP = do
               p <- primC
               option p $ do
                    asKey dlthat
                    p2 <- primC
                    return (DLThat p p2)

      primC :: AParser st DLConcept
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

      restCps :: DLConcept -> AParser st DLConcept
      restCps i = do
               asKey dlsome
               p <- relationP
               return $ DLSome i p
             <|>  do
               asKey dlonly
               p <- relationP
               return $ DLOnly i p
             <|>  do
               asKey dlhas
               p <- relationP
               return $ DLHas i p
             <|> do
               asKey dlmin
               p <- fmap read $ many1 digit
               return $ DLMin i p
             <|> do
               asKey dlmax
               p <- fmap read $ many1 digit
               return $ DLMin i p
             <|> do
               asKey dlexact
               p <- fmap read $ many1 digit
               return $ DLMin i p
             <|> do
               asKey dlvalue
               p <- csvarId casl_dl_keywords
               return $ DLValue i (simpleIdToId p)
             <|> do
               asKey dlonlysome
               oBracketT
               is <- sepBy1 pDLConcept commaT
               cBracketT
               return $ DLOnlysome i is

-- | Auxiliary parser for classes
cscpParser :: AParser st DLClassProperty
cscpParser =
    do
      try $ string dlSub
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLSubClassof s
    <|>
    do
      try $ string dlEquivTo
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLEquivalentTo s
    <|>
    do
      try $ string dlDisjoint
      spaces
      s <- sepBy pDLConcept commaT
      return $ DLDisjointWith s

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
      return $ makeAnnoted lano rano $ DLClass (simpleIdToId cId) props para
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
      return $ makeAnnoted lano rano $ DLObjectProperty (simpleIdToId cId) dom ran probRel csChars para
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
      return $ makeAnnoted lano rano $ DLDataProperty (simpleIdToId cId) dom ran probRel csCharsD para
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
      return $ makeAnnoted lano rano $ DLIndividual (simpleIdToId iId) ty facts indrel para
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
      return $ makeAnnoted lano rano $ DLMultiIndi (map simpleIdToId iIds) ty facts dlEq para

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
      return $ DLSubProperty $ map (mkId . (: [])) is
    <|>
    do
      try $ string dlInv
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLInverses $ map (mkId . (: [])) is
    <|>
     do
      try $ string dlInvOf
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLInverses $ map (mkId . (: [])) is
    <|>
    do
      try $ string dlEquiv
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLEquivalent $ map (mkId . (: [])) is
    <|>
    do
      try $ string dlDis
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLDisjoint $ map (mkId . (: [])) is

-- | Parser for property relations
csPropsRelD :: AParser st DLPropsRel
csPropsRelD =
    do
      try $ string dlSubProp
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLSubProperty $ map (mkId . (: [])) is
    <|>
    do
      try $ string dlEquiv
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLEquivalent $ map (mkId . (: [])) is
    <|>
    do
      try $ string dlDis
      spaces
      is <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ DLDisjoint $ map (mkId . (: [])) is

-- | Parser for types
parseType :: AParser st (Maybe DLType)
parseType =
    do
      try $ string dlTypes
      spaces
      ty <- sepBy1 (csvarId casl_dl_keywords) commaT
      return $ Just (DLType $ map (mkId . (: [])) ty)
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
            is <- csvarId casl_dl_keywords
            spaces
            os <- csvarId casl_dl_keywords
            return $ DLPosFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os))
          <|>
          do
            try $ string dlnot
            spaces
            is <- csvarId casl_dl_keywords
            spaces
            os <- csvarId casl_dl_keywords
            return $ DLNegFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os))

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
            return $ DLDifferentFrom $ map (mkId . (: [])) is
          <|>
          do
            try $ string dlSame
            spaces
            is <- sepBy1 (csvarId casl_dl_keywords) commaT
            return $ DLDifferentFrom $ map (mkId . (: [])) is

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
		return $ Just $ DLPara paras
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
