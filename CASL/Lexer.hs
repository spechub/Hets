
{- HetCATS/CASL/Lexer.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002

   scanner for CASL tokens and extensions to parsec
   
   http://www.cs.uu.nl/~daan/parsec.html)
   -- extended with "consumeNothing" 
   
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001
   C.4 Lexical Syntax

-}

module Lexer ( bind, (<<), (<:>), (<++>), 
	     , begDoEnd, flat, single, separatedBy, caslLetters
	     , checkWith, scanAnySigns, scanAnyWords, scanDotWords 
	     , scanDigit, scanFloat, scanQuotedChar, scanString
	     , reserved, placeS, placeT, pToken, asKey
	     , oBraceT, cBraceT, oBracketT, cBracketT, oParenT, cParenT
	     , commaT, semiT, pluralKeyword
	     , annos, lineAnnos, optSemi, tryItemEnd
	     ) where

import Char (digitToInt)
import Id (Token(..), place)
import Monad (MonadPlus (mplus), liftM2)
import ParsecPrim ((<?>), (<|>), many, try, skipMany, getPosition
		  , unexpected, consumeNothing, GenParser)
import ParsecCombinator (count, option, lookAhead, many1, notFollowedBy)
import ParsecChar (char, digit, hexDigit, octDigit
		  , oneOf, noneOf, satisfy, string)
import ParsecPos (SourcePos, sourceLine, sourceColumn) -- for setTokPos

import AS_Annotation
import Anno_Parser (comment, annote)

-- ----------------------------------------------
-- no-bracket-signs
-- ----------------------------------------------
signChars = "!#$&*+-./:<=>?@\\^|~" ++ "°¢£ß©¨∞±≤≥µ∂∑πø◊˜"

-- "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"
-- \172 neg \183 middle dot \215 times 

scanAnySigns = many1 (oneOf signChars <?> "casl sign") <?> "signs"

-- ----------------------------------------------
-- casl letters
-- ----------------------------------------------
caslLetters = ['A'..'Z'] ++ ['a'..'z'] ++ 
	      "¿¡¬√ƒ≈∆«»… ÀÃÕŒœ—“”‘’÷ÿŸ⁄€‹›ﬂ‡·‚„‰ÂÊÁËÈÍÎÏÌÓÔÒÚÛÙıˆ¯˘˙˚¸˝ˇ"

-- see http://www.htmlhelp.com/reference/charset/ starting from \192
-- \208 ETH \215 times \222 THORN \240 eth \247 divide \254 thorn

caslLetter :: GenParser Char st Char
caslLetter = oneOf caslLetters <?> "casl letter"

prime = char '\'' -- also used for quoted chars

scanLPD :: GenParser Char st Char
scanLPD = caslLetter <|> digit <|> prime <?> "casl char"

-- ----------------------------------------------
-- Monad/Functor extensions
-- ----------------------------------------------

bind :: (Monad m) => (a -> b -> c) -> m a -> m b -> m c
bind f p q = do { x <- p; y <- q; return (f x y) }

infixl <<

(<<) :: (Monad m) => m a -> m b -> m a
(<<) = bind const

infixr 5 <:>

(<:>) :: (Monad m) => m a -> m [a] -> m [a]
(<:>) = liftM2 (:)

infixr 5 <++>

(<++>) :: (Monad m, MonadPlus p) => m (p a) -> m (p a) -> m (p a)
(<++>) = liftM2 mplus

-- Functor extension
single :: (Functor f, Monad m) => f a -> f (m a)
single = fmap return

flat :: (Functor f) => f [[a]] -> f [a]
flat = fmap concat

-- ----------------------------------------------
-- ParsecCombinator extension
-- ----------------------------------------------

followedWith :: GenParser tok st a -> GenParser tok st b -> GenParser tok st a
p `followedWith` q = try (p << lookAhead q)

begDoEnd :: (Monad f, Functor f) => f a -> f [a] -> f a -> f [a]
begDoEnd open p close = open <:> p <++> single close  

enclosedBy :: (Monad f, Functor f) => f [a] -> f a -> f [a]
p `enclosedBy` q = begDoEnd q p q

checkWith :: (Show a) => GenParser tok st a -> (a -> Bool) 
	  -> GenParser tok st a
p `checkWith` f = do { x <- p
		     ; if f x then return x else 
		       consumeNothing >> unexpected (show x)
		     }

separatedBy :: GenParser tok st a -> GenParser tok st b 
	    -> GenParser tok st ([a], [b])
p `separatedBy`  s = do { r <- p
			; option ([r], []) 
			  (do { t <- s
                              ; (es, ts) <- separatedBy p s
                              ; return (r:es, t:ts)
                              })
			}

-- ----------------------------------------------
-- casl words
-- ----------------------------------------------

scanLetterWord = caslLetter <:> many scanLPD <?> "letter word"

singleUnderline = char '_' `followedWith` scanLPD

scanUnderlineWord = singleUnderline <:> many1 scanLPD <?> "underline word"

scanAnyWords :: GenParser Char st String
scanAnyWords = flat (scanLetterWord <:> many scanUnderlineWord) <?> "words"

scanDot = char '.' `followedWith` caslLetter

scanDotWords = scanDot <:> scanAnyWords <?> "dot-words"

-- ----------------------------------------------
-- casl escape chars for quoted chars and literal strings
-- ----------------------------------------------

-- see ParsecToken.number
value :: Int -> String -> Int
value base s = foldl (\x d -> base*x + (digitToInt d)) 0 s

simpleEscape = single (oneOf "'\"\\ntrvbfa?")

decEscape = count 3 digit `checkWith` \s -> value 10 s <= 255

hexEscape = char 'x' <:> count 2 hexDigit -- cannot be too big

octEscape = char 'o' <:> 
	    count 3 octDigit `checkWith` \s -> value 8 s <= 255

escapeChar = char '\\' <:> 
	     (simpleEscape <|> decEscape <|> hexEscape <|> octEscape)

-- ----------------------------------------------
-- chars for quoted chars and literal strings
-- ----------------------------------------------

printable = single (satisfy (\c -> (c /= '\'')  && (c /= '"') 
			      && (c /= '\\') && (c > '\026')))

caslChar = escapeChar <|> printable

scanQuotedChar = (caslChar <|> string "\"") `enclosedBy` prime <?> "quoted char"

scanString = flat (many (caslChar <|> string "'")) `enclosedBy` char '"'
	     <?> "literal string"

-- ----------------------------------------------
-- digit, number, fraction, float
-- ----------------------------------------------

getNumber = many1 digit

scanFloat = getNumber <++> option "" 
	     (char '.' <:> getNumber
	      <++> option "" 
	      (char 'E' <:> option "" (single (oneOf "+-"))
	       <++> getNumber))

scanDigit :: GenParser Char st String
scanDigit = single digit

-- ----------------------------------------------
-- nested comment outs
-- ----------------------------------------------

notEndText c = try (char c << notFollowedBy (char '%'))

nestCommentOut = try (string "%[") >> 
		 many (noneOf "]%" 
		       <|> notEndText ']'
			  <|> nestCommentOut 
			  <|> char '%')
		 >> char ']' >> char '%'

-- ----------------------------------------------
-- skip whitespaces and nested comment out
-- ----------------------------------------------

newlineChars = "\n\r"
blankChars = "\t\v\f \160" -- non breaking space

skip :: GenParser Char st ()
skip = skipMany(oneOf (newlineChars ++ blankChars) 
		       <|> nestCommentOut <?> "") >> return () 

-- only skip to an annotation if it's on the same line
skipSmart = do {p <- getPosition
	       ; try (do { skip
			 ; q <- getPosition
			 ; if sourceLine q == sourceLine p then return ()
			   else notFollowedBy (char '%') >> return ()
			 })
		<|> return ()
	       }


-- ----------------------------------------------
-- annotations
-- ----------------------------------------------

anno :: GenParser Char st Annotation
anno = 	comment <|> annote  --  (imported) position not included yet

-- skip to leading annotation and read many
annos :: GenParser Char st [Annotation]
annos = skip >> many (anno << skip)

-- annotations on one line
lineAnnos :: GenParser Char st [Annotation]
lineAnnos = do { p <- getPosition
	       ; do { a <- anno  
		    ; skip
		    ; q <- getPosition
		    ; if sourceLine q == sourceLine p then
		      do { l <- lineAnnos
			 ; return (a:l)
			 }
		      else return [a]
		    }
		 <|> return []
	       }

-- ----------------------------------------------
-- keywords WORDS or NO-BRACKET-SIGNS 
-- ----------------------------------------------

keyWord :: GenParser Char st a -> GenParser Char st a
keyWord p = try(p << notFollowedBy scanLPD)
keySign :: GenParser Char st a -> GenParser Char st a
keySign p = try(p << notFollowedBy (oneOf signChars))

reserved :: [String] -> GenParser Char st String -> GenParser Char st String
-- "try" to avoid reading keywords 
reserved l p = try (p `checkWith` \r -> r `notElem` l)

-- ----------------------------------------------
-- lexical tokens with position
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token s (sourceLine p, sourceColumn p)

pToken :: GenParser Char st String -> GenParser Char st Token
pToken parser = bind setTokPos getPosition (parser << skipSmart)

pluralKeyword :: String -> GenParser Char st Token
pluralKeyword s = pToken (keyWord (string s <++> option "" (string "s")))

-- check for keywords (depending on lexem class)
toKey s = let p = string s in 
	      if last s `elem` "[]{}(),;" then p 
		 else if last s `elem` signChars then keySign p 
		      else keyWord p

asKey :: String -> GenParser Char st Token
asKey = pToken . toKey

commaT = asKey ","
semiT = asKey ";"

oBracketT = asKey "["
cBracketT = asKey "]"
oBraceT = asKey "{" 
cBraceT = asKey "}"
oParenT = asKey "("
cParenT = asKey ")"

placeS = string place
placeT = pToken (try (placeS) <?> place)

-- optional semicolon followed by annotations on the same line
optSemi :: GenParser Char st (Maybe Token, [Annotation])
optSemi = bind (,) (option Nothing (fmap Just semiT)) lineAnnos

-- succeeds if an item is not continued after a semicolon
tryItemEnd :: [String] -> GenParser Char st ()
tryItemEnd l = 
    try (do { c <- lookAhead (annos >> 
			      (single (oneOf "\"([{")
			       <|> placeS
			       <|> scanAnySigns
			       <|> many scanLPD))
	    ; if null c || c `elem` l then return () else unexpected c
	    })
