{- |
Module      :  $Header$
Description :  parsing of interspersed annotations
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parsing of interspersed annotations

- a parser state to collect annotations

- parsing annoted keywords

- parsing an annoted item list
-}

module Common.AnnoState where

import Common.Lexer
import Common.Token
import Common.Id
import Common.Keywords
import Common.AS_Annotation
import Common.Anno_Parser
import Text.ParserCombinators.Parsec
import Data.List(delete)

-- | parsers that can collect annotations via side effects
type AParser st a = GenParser Char (AnnoState st) a

class AParsable a where
  aparser :: AParser st a

-- used for CASL extensions. If there is no extension, just fail
instance AParsable () where
  aparser = pzero

-- | just the list of currently collected annotations
data AnnoState st = AnnoState { toAnnos :: [Annotation]
                              , userState :: st }

-- | no annotations
emptyAnnos :: st -> AnnoState st
emptyAnnos st = AnnoState [] st

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

getUserState :: AParser st st
getUserState = fmap userState getState

setUserState :: st -> AParser st ()
setUserState st = getState >>= \ s -> setState s { userState = st }

-- | extract all annotation from the internal state,
-- resets the internal state to 'emptyAnnos'
getAnnos :: AParser st [Annotation]
getAnnos = do aSt <- getState
              setState aSt { toAnnos = [] }
              return $ toAnnos aSt

-- | annotations on consecutive lines
mLineAnnos :: GenParser Char st [Annotation]
mLineAnnos =
       do a <- annotationL
          skipSmart
          do  l <- mLineAnnos
              return (a:l)
            <|> return [a]
         <|> return []

-- | explicitly parse annotations, reset internal state
annos :: AParser st [Annotation]
annos = addAnnos >> getAnnos

-- | explicitly parse annotations on consecutive lines. reset internal state
lineAnnos :: AParser st [Annotation]
lineAnnos = addLineAnnos >> getAnnos

-- | optional semicolon followed by annotations on consecutive lines
optSemi :: AParser st ([Token], [Annotation])
optSemi = do (a1, s) <- try $ bind (,) annos semiT
             a2 <- lineAnnos
             return ([s], a1 ++ a2)
          <|> do a <- lineAnnos
                 return ([], a)

-- | succeeds if the previous item is finished
tryItemEnd :: [String] -> AParser st ()
tryItemEnd l = try $ do
  c <- lookAhead $ annos >>
    (single (oneOf "\"([{") <|> placeS <|> scanAnySigns
     <|> many (scanLPD <|> char '_' <?> "") <?> "")
  if null c || c `elem` l then return () else pzero

-- | keywords that indicate a new item for 'tryItemEnd'.
-- the quantifier exists does not start a new item.
startKeyword :: [String]
startKeyword = dotS:cDot:
                   (delete existsS casl_reserved_words)

-- | parse preceding annotations and the following item
annoParser :: AParser st a
           -> AParser st (Annoted a)
annoParser parser = bind addLeftAnno annos parser

-- | parse an item list preceded and followed by annotations
annosParser :: AParser st a
            -> AParser st [Annoted a]
annosParser parser =
    do a <- annos
       l <- many1 $ bind (,) parser annos
       let ps = map fst l
           as = map snd l
           is = zipWith addLeftAnno (a: init as) ps
       return (init is ++ [appendAnno (last is) (last as)])

-- | parse an item list preceded by a singular or plural keyword,
-- interspersed with semicolons and an optional semicolon at the end
itemList :: [String] -> String -> ([String] -> AParser st b)
               -> ([Annoted b] -> Range -> a) -> AParser st a
itemList ks kw ip constr =
    do p <- pluralKeyword kw
       auxItemList (ks++startKeyword) [p] (ip ks) constr

-- | generalized version of 'itemList'
-- for an other keyword list for 'tryItemEnd' and without 'pluralKeyword'
auxItemList :: [String] -> [Token] -> AParser st b
            -> ([Annoted b] -> Range -> a) -> AParser st a
auxItemList startKeywords ps parser constr = do
       (vs, ts, ans) <- itemAux startKeywords (annoParser parser)
       let r = zipWith appendAnno vs ans in
           return (constr r (catRange (ps++ts)))

-- | parse an item list without a starting keyword
itemAux :: [String] -> AParser st a
        -> AParser st ([a], [Token], [[Annotation]])
itemAux startKeywords itemParser =
    do a <- itemParser
       (m, an) <- optSemi
       let r = return ([a], [], [an])
       if null m then r else (tryItemEnd startKeywords >> r) <|>
          do (ergs, ts, ans) <- itemAux startKeywords itemParser
             return (a:ergs, m++ts, an:ans)

-- | collect preceding and trailing annotations
wrapAnnos :: AParser st a -> AParser st a
wrapAnnos p = try (addAnnos >> p) << addAnnos

-- | parse an annoted keyword
asKey :: String -> AParser st Token
asKey s = wrapAnnos $ pToken $ toKey s

-- * annoted keywords
anComma, anSemi :: AParser st Token
anComma = wrapAnnos Common.Lexer.commaT
anSemi = wrapAnnos Common.Lexer.semiT

equalT, colonT, lessT, dotT :: AParser st Token
equalT = wrapAnnos $ pToken $
         (((lookAhead $ keySign $ string exEqual)
                          >> unexpected exEqual)
         <|> keySign (string equalS))

colonT = asKey colonS
lessT = asKey lessS
dotT = asKey dotS <|> asKey cDot <?> "dot"

asT, barT, forallT :: AParser st Token
asT = asKey asS
barT = asKey barS
forallT = asKey forallS
