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

module DL.ParseDL
    (
      csbsParse
    , longTest
    )
    where

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

-- | string Parse
parseDLString :: String -> AParser st String
parseDLString iS =
    do
        st <- string iS
        spaces
        return st

-- | parser for Concepts
pDLConcept :: AParser st DLConcept
pDLConcept = do
  chainr1 orConcept (
    do
        p <- asKey dlxor
        return (\x y -> DLXor x y (tokPos p))
        )

orConcept :: AParser st DLConcept
orConcept = do
       chainr1 andConcept (
        do
            p <- asKey dlor
            return (\x y -> DLOr x y (tokPos p))
            )

andConcept :: AParser st DLConcept
andConcept = do
           chainr1 notConcept (
            do
                p <- (asKey dland <|> asKey dlthat)
                return (\x y -> DLAnd x y (tokPos p))
                )

notConcept :: AParser st DLConcept
notConcept = do
           nt <- asKey dlnot
           i <- infixCps
           return $ DLNot i $ tokPos nt
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
           fmap (\x -> DLClassId (mkId (x:[])) $ tokPos x) (csvarId [])
         <|>
         do
           between oParenT cParenT pDLConcept
         <|>
         do
           oBt <- oBraceT
           is <- sepBy1 (csvarId []) commaT
           cBraceT
           return $ DLOneOf (map (mkId . (: [])) is) $ tokPos oBt

selfParser :: AParser st DLConcept
selfParser =
    do
        k <- asKey dlSelf
        return $ DLSelf $ tokPos k

restCps :: Id -> AParser st DLConcept
restCps i = do
           k <- asKey dlsome
           p <- primC <|> selfParser
           return $ DLSome i p $ tokPos k
         <|>  do
           k <- asKey dlonly
           p <- primC <|> selfParser
           return $ DLOnly i p $ tokPos k
         <|>  do
           k <- asKey dlhas
           p <- csvarId []
           return $ DLHas i (simpleIdToId p) $ tokPos k
         <|> do
           k <- asKey dlmin
           p <- fmap read $ many1 digit
           spaces
           return $ DLMin i p Nothing $ tokPos k
         <|> do
           k <- asKey dlmax
           p <- fmap read $ many1 digit
           spaces
           cp <- maybe_primC
           return $ DLMax i p cp $ tokPos k
         <|> do
           k <- asKey dlexact
           p <- fmap read $ many1 digit
           spaces
           return $ DLExactly i p Nothing $ tokPos k
         <|> do
           k <- asKey dlvalue
           p <- csvarId []
           return $ DLValue i (simpleIdToId p) $ tokPos k
         <|> do
           k <- asKey dlonlysome
           oBracketT
           is <- sepBy1 pDLConcept commaT
           cBracketT
           return $ DLOnlysome i is $ tokPos k

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
      return $ makeAnnoted lano rano $ DLClass (simpleIdToId cId) props para $ tokPos cId
    <|>
    do
      try $ string dlObjProp
      spaces
      lano <- getAnnos
      cId   <- csvarId [dlUniversal]
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRel
      csChars <- parseDLChars
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLObjectProperty (simpleIdToId cId) dom ran probRel csChars para $ tokPos cId
    <|>
    do
      lano <- getAnnos
      try $ string dlDataProp
      spaces
      cId   <- csvarId [dlUniversal]
      dom   <- csDomain
      ran   <- csRange
      probRel <- many csPropsRelD
      csCharsD <- parseDLCharsD
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLDataProperty (simpleIdToId cId) dom ran probRel csCharsD para $ tokPos cId
    <|>
    do
      try $ string dlIndi
      spaces
      lano <- getAnnos
      iId <- csvarId []
      ty  <- parseType
      facts <- parseFacts
      indrel <- csIndRels
      para <- parsePara
      rano <- getAnnos
      return $ makeAnnoted lano rano $ DLIndividual (simpleIdToId iId) ty facts indrel para $ tokPos iId
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
      return $ makeAnnoted lano rano $ DLMultiIndi (map simpleIdToId iIds) ty facts dlEq para $ tokPos $ head iIds

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
            try $ parseDLString dlFunc
            return DLFunctional
          <|>
          do
            try $ parseDLString dlInvFunc
            return DLInvFuntional
          <|>
          do
            try $ parseDLString dlSym
            return DLSymmetric
          <|>
          do
            try $ parseDLString dlTrans
            return DLTransitive
          <|>
          do
            try $ parseDLString dlRefl
            return DLReflexive
          <|>
          do
            try $ parseDLString dlIrr
            return DLIrreflexive

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
      is <- sepBy1 (csvarId []) commaT
      return $ DLSubProperty ( map (mkId . (: [])) is) $ tokPos $ head is
    <|>
    do
      try $ string dlInv
      spaces
      is <- sepBy1 (csvarId []) commaT
      return $ DLInverses (map (mkId . (: [])) is) $ tokPos $ head is
    <|>
     do
      try $ string dlInvOf
      spaces
      is <- sepBy1 (csvarId []) commaT
      return $ DLInverses (map (mkId . (: [])) is) $ tokPos $ head is
    <|>
    do
      try $ string dlEquiv
      spaces
      is <- sepBy1 (csvarId []) commaT
      return $ DLEquivalent (map (mkId . (: [])) is) $ tokPos $ head is
    <|>
    do
      try $ string dlDis
      spaces
      is <- sepBy1 (csvarId []) commaT
      return $ DLDisjoint (map (mkId . (: [])) is) $ tokPos $ head is
    <|>
     do
        parseDLString dlSuperProp
        is <- sepBy1 (sepBy1 (csvarId []) semiT) commaT
        iis <- mapM (\x -> return $ DLPropertyComp (map simpleIdToId x)) is
        return $ DLSuperProperty iis (tokPos $ head $ head is)

-- | Parser for property relations
csPropsRelD :: AParser st DLPropsRel
csPropsRelD =
    do
      try $ string dlSubProp
      spaces
      is <- sepBy1 (csvarId []) commaT
      return $ DLSubProperty ( map (mkId . (: [])) is) $ tokPos $ head is
    <|>
    do
      try $ string dlEquiv
      spaces
      is <- sepBy1 (csvarId []) commaT
      return $ DLEquivalent (map (mkId . (: [])) is) $ tokPos $ head is
    <|>
    do
      try $ string dlDis
      spaces
      is <- sepBy1 (csvarId []) commaT
      return $ DLDisjoint (map (mkId . (: [])) is) $ tokPos $ head is

-- | Parser for types
parseType :: AParser st (Maybe DLType)
parseType =
    do
      (try $ string dlTypes) <|> (try $ string dlType)
      spaces
      ty <- sepBy1 (csvarId []) commaT
      return $ Just (DLType (map (mkId . (: [])) ty) $ tokPos $ head ty)
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
            return $ DLPosFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os)) $ tokPos is
          <|>
          do
            try $ string dlnot
            spaces
            is <- csvarId []
            spaces
            os <- csvarId [] <|> fmap mkSimpleId getNumber
            return $ DLNegFact ((\(x,y) -> (simpleIdToId x, simpleIdToId y)) (is,os)) $ tokPos is

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
            is <- sepBy1 (csvarId []) commaT
            return $ DLDifferentFrom (map (mkId . (: [])) is) $ tokPos $ head is
          <|>
          do
            try $ string dlSame
            spaces
            is <- sepBy1 (csvarId []) commaT
            return $ DLDifferentFrom (map (mkId . (: [])) is) $ tokPos $ head is

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
                        return (lg, reverse $ tail $ reverse $ tail $ pp)

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
