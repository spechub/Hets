
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
parsing of interspersed annotations

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
import Common.Lib.Parsec
import Data.List(delete)


-- | parsers that can collect annotations via side effects
type AParser a = GenParser Char AnnoState a

class AParsable a where
  aparser :: AParser a

-- used for CASL extensions. If there is no extension, just fail
instance AParsable () where
  aparser = pzero

-- | just the list of currently collected annotations
data AnnoState = AnnoState { toAnnos :: [Annotation] }

-- | no annotations
emptyAnnos :: AnnoState
emptyAnnos = AnnoState []

-- | add further annotations to the input state
parseAnnos :: AnnoState -> GenParser Char st AnnoState 
parseAnnos (AnnoState as) = 
    do a <- skip >> annotations
       return $ AnnoState (as ++ a) 

-- | add only annotations on consecutive lines to the input state 
parseLineAnnos :: AnnoState -> GenParser Char st AnnoState 
parseLineAnnos (AnnoState as) = 
    do l <- mLineAnnos
       return $ AnnoState (as ++ l) 

-- | add annotations to the internal state
addAnnos :: AParser ()
addAnnos = getState >>= parseAnnos >>= setState

-- | add only annotations on consecutive lines to the internal state 
addLineAnnos :: AParser ()
addLineAnnos = getState >>= parseLineAnnos >>= setState

-- | extract all annotation from the internal state,
-- resets the internal state to 'emptyAnnos'
getAnnos :: AParser [Annotation]
getAnnos = do AnnoState a <- getState 
	      setState emptyAnnos 
	      return a

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
annos :: AParser [Annotation]
annos = addAnnos >> getAnnos

-- | explicitly parse annotations on consecutive lines. reset internal state
lineAnnos :: AParser [Annotation]
lineAnnos = addLineAnnos >> getAnnos

-- | optional semicolon followed by annotations on consecutive lines
optSemi :: AParser (Maybe Token, [Annotation])
optSemi = do (a1, s) <- try $ bind (,) annos Common.Lexer.semiT
             a2 <- lineAnnos                         
             return (Just s, a1 ++ a2)
          <|> do a <- lineAnnos
                 return (Nothing, a)

-- | succeeds if the previous item is finished 
tryItemEnd :: [String] -> AParser ()
tryItemEnd l = 
    try (do c <- lookAhead (annos >>
			      (single (oneOf "\"([{")
			       <|> placeS
			       <|> scanAnySigns
			       <|> many scanLPD))
	    if null c || c `elem` l then return () else unexpected c)



-- | keywords that indicate a new item for 'tryItemEnd'.
-- the quantifier exists does not start a new item.
startKeyword :: [String]
startKeyword = dotS:cDot:
		   (delete existsS casl_reserved_words)

-- | parse preceding annotations and the following item
annoParser :: AParser a 
	   -> AParser (Annoted a)
annoParser parser = bind addLeftAnno annos parser

-- | parse an item list preceded and followed by annotations
annosParser :: AParser a 
	    -> AParser [Annoted a]
annosParser parser = 
    do a <- annos 
       l <- many1 $ bind (,) parser annos
       let ps = map fst l 
	   as = map snd l
           is = zipWith addLeftAnno (a: init as) ps  
       return (init is ++ [appendAnno (last is) (last as)])

-- | parse an item list preceded by a singular or plural keyword,
-- interspersed with semicolons and an optional semicolon at the end
itemList :: [String] -> String -> ([String] -> AParser b)
               -> ([Annoted b] -> [Pos] -> a) -> AParser a
itemList ks kw ip constr = 
    do p <- pluralKeyword kw
       auxItemList (ks++startKeyword) [p] (ip ks) constr	      

-- | generalized version of 'itemList' 
-- for an other keyword list for 'tryItemEnd' and without 'pluralKeyword'
auxItemList :: [String] -> [Token] -> AParser b
            -> ([Annoted b] -> [Pos] -> a) -> AParser a
auxItemList startKeywords ps parser constr = do
       (vs, ts, ans) <- itemAux startKeywords (annoParser parser)
       let r = zipWith appendAnno vs ans in 
	   return (constr r (map tokPos (ps++ts)))

-- | parse an item list without a starting keyword
itemAux :: [String] -> AParser a 
	-> AParser ([a], [Token], [[Annotation]])
itemAux startKeywords itemParser = 
    do a <- itemParser
       (m, an) <- optSemi
       case m of Nothing -> return ([a], [], [an])
                 Just t -> do tryItemEnd startKeywords
			      return ([a], [t], [an])
	                   <|> 
	                   do (as, ts, ans) <- itemAux startKeywords itemParser
			      return (a:as, t:ts, an:ans)


-- | collect preceding and trailing annotations
wrapAnnos :: AParser a -> AParser a
wrapAnnos p = try (addAnnos >> p) << addAnnos

-- | parse an annoted keyword
asKey :: String -> AParser Token
asKey s = wrapAnnos $ pToken $ toKey s

-- * annoted keywords
anComma, commaT, anSemi, semiT :: AParser Token
anComma = wrapAnnos Common.Lexer.commaT
commaT = anComma
anSemi = wrapAnnos Common.Lexer.semiT
semiT = anSemi

equalT, colonT, lessT, dotT :: AParser Token
equalT = wrapAnnos $ pToken $ 
	 (((lookAhead $ keySign $ string exEqual) 
			  >> unexpected exEqual)
	 <|> keySign (string equalS))

colonT = asKey colonS
lessT = asKey lessS
dotT = try(asKey dotS <|> asKey cDot) <?> "dot"

asT, barT, forallT :: AParser Token
asT = asKey asS
barT = asKey barS
forallT = asKey forallS

