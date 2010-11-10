{- |
Module      :  $Header$
Description :  parsing of interspersed annotations
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parsing of interspersed annotations

- a parser state to collect annotations

- parsing annoted keywords

- parsing an annoted item list
-}

module Common.AnnoState where

import Common.Parsec
import Common.Lexer
import Common.Token
import Common.Id
import Common.Keywords
import Common.AS_Annotation
import Common.AnnoParser

import Text.ParserCombinators.Parsec

import Data.List
import Control.Monad

-- | parsers that can collect annotations via side effects
type AParser st = GenParser Char (AnnoState st)

class AParsable a where
  aparser :: AParser st a

-- used for CASL extensions. If there is no extension, just fail
instance AParsable () where
  aparser = pzero

-- | just the list of currently collected annotations
data AnnoState st = AnnoState { toAnnos :: [Annotation], _userState :: st }

-- | no annotations
emptyAnnos :: st -> AnnoState st
emptyAnnos = AnnoState []

-- | add further annotations to the input state
parseAnnos :: AnnoState a -> GenParser Char st (AnnoState a)
parseAnnos (AnnoState as b) =
    do a <- skip >> annotations
       return $ AnnoState (as ++ a) b

-- | add only annotations on consecutive lines to the input state
parseLineAnnos :: AnnoState a -> GenParser Char st (AnnoState a)
parseLineAnnos (AnnoState as b) =
    do l <- mLineAnnos
       return $ AnnoState (as ++ l) b

-- | add annotations to the internal state
addAnnos :: AParser st ()
addAnnos = getState >>= parseAnnos >>= setState

-- | add only annotations on consecutive lines to the internal state
addLineAnnos :: AParser st ()
addLineAnnos = getState >>= parseLineAnnos >>= setState

-- | extract all annotation from the internal state,
-- resets the internal state to 'emptyAnnos'
getAnnos :: AParser st [Annotation]
getAnnos = do
  aSt <- getState
  setState aSt { toAnnos = [] }
  return $ toAnnos aSt

-- | annotations on consecutive lines
mLineAnnos :: GenParser Char st [Annotation]
mLineAnnos = optionL $ do
    a <- annotationL
    skipSmart
    fmap (a :) $ optionL mLineAnnos

-- | explicitly parse annotations, reset internal state
annos :: AParser st [Annotation]
annos = addAnnos >> getAnnos

-- | explicitly parse annotations on consecutive lines. reset internal state
lineAnnos :: AParser st [Annotation]
lineAnnos = addLineAnnos >> getAnnos

-- | optional semicolon followed by annotations on consecutive lines
optSemi :: AParser st ([Token], [Annotation])
optSemi = do
    (a1, s) <- try $ pair annos semiT
    a2 <- lineAnnos
    return ([s], a1 ++ a2)
  <|> do
    a <- lineAnnos
    return ([], a)

-- | succeeds if the previous item is finished
tryItemEnd :: [String] -> AParser st ()
tryItemEnd l = try $ do
  c <- lookAhead $ annos >>
    (single (oneOf "\"([{") <|> placeS <|> scanAnySigns
     <|> many (scanLPD <|> char '_' <?> "") <?> "")
  unless (null c || elem c l) pzero

-- | keywords that indicate a new item for 'tryItemEnd'.
-- the quantifier exists does not start a new item.
startKeyword :: [String]
startKeyword = dotS : cDot : delete existsS casl_reserved_words

-- | parse preceding annotations and the following item
annoParser :: AParser st a -> AParser st (Annoted a)
annoParser = liftM2 addLeftAnno annos

allAnnoParser :: AParser st a -> AParser st (Annoted a)
allAnnoParser p = liftM2 appendAnno (annoParser p) lineAnnos

{- | parse preceding and consecutive trailing annotations of an item in
     between.  Unlike 'annosParser' do not treat all trailing annotations as
     preceding annotations of the next item. -}
trailingAnnosParser :: AParser st a -> AParser st [Annoted a]
trailingAnnosParser p = do
  l <- many1 $ allAnnoParser p
  a <- annos -- append remaining annos to last item
  return $ init l ++ [appendAnno (last l) a]

-- | parse an item list preceded and followed by annotations
annosParser :: AParser st a -> AParser st [Annoted a]
annosParser parser =
    do a <- annos
       l <- many1 $ pair parser annos
       let ps = map fst l
           as = map snd l
           is = zipWith addLeftAnno (a : init as) ps
       return (init is ++ [appendAnno (last is) (last as)])

-- | parse an item list preceded by a singular or plural keyword,
-- interspersed with semicolons and an optional semicolon at the end
itemList :: [String] -> String -> ([String] -> AParser st b)
               -> ([Annoted b] -> Range -> a) -> AParser st a
itemList ks kw ip constr =
    do p <- pluralKeyword kw
       auxItemList (ks ++ startKeyword) [p] (ip ks) constr

-- | generalized version of 'itemList'
-- for an other keyword list for 'tryItemEnd' and without 'pluralKeyword'
auxItemList :: [String] -> [Token] -> AParser st b
            -> ([Annoted b] -> Range -> a) -> AParser st a
auxItemList startKeywords ps parser constr = do
       (vs, ts, ans) <- itemAux startKeywords (annoParser parser)
       let r = zipWith appendAnno vs ans in
           return (constr r (catRange (ps ++ ts)))

-- | parse an item list without a starting keyword
itemAux :: [String] -> AParser st a
        -> AParser st ([a], [Token], [[Annotation]])
itemAux startKeywords itemParser =
    do a <- itemParser
       (m, an) <- optSemi
       let r = return ([a], [], [an])
       if null m then r else (tryItemEnd startKeywords >> r) <|>
          do (ergs, ts, ans) <- itemAux startKeywords itemParser
             return (a : ergs, m ++ ts, an : ans)

-- | collect preceding and trailing annotations
wrapAnnos :: AParser st a -> AParser st a
wrapAnnos p = try (addAnnos >> p) << addAnnos

-- | parse an annoted keyword
asKey :: String -> AParser st Token
asKey = wrapAnnos . pToken . toKey

-- * annoted keywords
anComma :: AParser st Token
anComma = wrapAnnos Common.Lexer.commaT

anSemi :: AParser st Token
anSemi = wrapAnnos Common.Lexer.semiT

equalT :: AParser st Token
equalT = wrapAnnos $ pToken $ reserved [exEqual]
         (choice (map (keySign . string) [exEqual, equalS]) <?> show equalS)

colonT :: AParser st Token
colonT = asKey colonS

lessT :: AParser st Token
lessT = asKey lessS

dotT :: AParser st Token
dotT = asKey dotS <|> asKey cDot <?> show dotS

asT :: AParser st Token
asT = asKey asS

barT :: AParser st Token
barT = asKey barS

forallT :: AParser st Token
forallT = asKey forallS
