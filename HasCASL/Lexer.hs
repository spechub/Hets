module Lexer where

import Char
import Id
import Monad
import ParsecPos
import ParsecPrim
import ParsecCombinator
import ParsecChar

-- ----------------------------------------------
-- no-bracket-signs
-- ----------------------------------------------
signChars = "!#$&*+-./:<=>?@\\^|~" ++ "°¢£ß©¨∞±≤≥µ∂∑πø◊˜"

-- "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"
-- \172 neg \183 middle dot \215 times 

scanAnySigns = many1 (oneOf signChars) <?> "signs"

scanPlace = try (string place) <?> "place"

-- ----------------------------------------------
-- casl letters
-- ----------------------------------------------
caslLetters = ['A'..'Z'] ++ ['a'..'z'] ++ 
	      "¿¡¬√ƒ≈∆«»… ÀÃÕŒœ—“”‘’÷ÿŸ⁄€‹›ﬂ‡·‚„‰ÂÊÁËÈÍÎÏÌÓÔÒÚÛÙıˆ¯˘˙˚¸˝ˇ"

-- see http://www.htmlhelp.com/reference/charset/ starting from \192
-- \208 ETH \215 times \222 THORN \240 eth \247 divide \254 thorn

caslLetter :: Parser Char
caslLetter = oneOf caslLetters <?> "casl letter"

prime = char '\'' -- also used for quoted chars

scanLPD :: Parser Char
scanLPD = caslLetter <|> digit <|> prime

-- ----------------------------------------------
-- Monad/Functor extensions
-- ----------------------------------------------

ignore :: (Monad m) => m a -> m b -> m a
p `ignore` q = do { x <- p; q; return x }

bind :: (Monad m) => (a -> b -> c) -> m a -> m b -> m c
bind f p q = do { x <- p; y <- q; return (f x y) }

infixr 1 <:>

(<:>) :: (Monad m) => m a -> m [a] -> m [a]
(<:>) = liftM2 (:)

infixr 1 <++>

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

notFollowedWith :: (Show b) => GenParser tok st a 
		-> GenParser tok st b -> GenParser tok st a
p `notFollowedWith` q = do { x <- p 
			   ; try ((q >>= unexpected . show) <|> return x)
			   }

followedBy :: GenParser tok st a -> GenParser tok st b -> GenParser tok st a
p `followedBy` q = try (do { x <- p
			   ; lookAhead q
			   ; return x
			   })

begDoEnd :: (Monad f, Functor f) => f a -> f [a] -> f a -> f [a]
begDoEnd open p close = (open <:> p) <++> single close  

enclosedBy :: (Monad f, Functor f) => f [a] -> f a -> f [a]
p `enclosedBy` q = begDoEnd q p q

checkWith :: (Show a) => GenParser tok st a -> (a -> Bool) -> GenParser tok st a
p `checkWith` f = do { x <- p
		     ; if f x then return x else unexpected (show x)
		     }

-- ----------------------------------------------
-- casl words
-- ----------------------------------------------

scanLetterWord = caslLetter <:> many scanLPD <?> "letter word"

singleUnderline = (char '_') `followedBy` scanLPD

scanUnderlineWord = singleUnderline <:> many1 scanLPD <?> "underline word"

scanAnyWords :: Parser String
scanAnyWords = flat (scanLetterWord <:> many scanUnderlineWord <?> "words")

scanDot = (char '.') `followedBy` caslLetter

scanDotWords = scanDot <:> scanAnyWords <?> "dot-words"

-- ----------------------------------------------
-- casl escape chars for quoted chars and literal strings
-- ----------------------------------------------

-- see ParsecToken.number
value :: Int -> String -> Int
value base s = foldl (\x d -> base*x + (digitToInt d)) 0 s

simpleEscape = single (oneOf "'\"\\ntrvbfa?")

decEscape = (count 3 digit) `checkWith` (\s -> value 10 s <= 255)

hexEscape = char 'x' <:> count 2 hexDigit -- cannot be too big

octEscape = char 'o' <:> 
	    ((count 3 octDigit) `checkWith`(\s -> value 8 s <= 255))

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

scanFloat = (getNumber <++> option "" 
	     ((char '.' <:> getNumber)
	      <++> option "" 
	      ((char 'E' <:> option "" (single (oneOf "+-")))
	       <++> getNumber))) `checkWith` (\n -> length n > 1)

scanDigit = getNumber `checkWith` (\n -> length n == 1)

-- ----------------------------------------------
-- skip whitespaces and comment out
-- ----------------------------------------------

blankChars = "\t\v\f \160" -- non breaking space

skip p = p `ignore` 
	 skipMany(single (oneOf (newlineChars ++ blankChars)) 
		  <|> commentOut <?> "")

-- ----------------------------------------------
-- comments and label
-- ----------------------------------------------

newlineChars = "\n\r"

eol = (eof >> return '\n') <|> oneOf newlineChars

textLine = many (noneOf newlineChars) `ignore` eol

commentLine = try (string "%%") <++> textLine

notEndText c = try (char c) `notFollowedWith` char '%' <?> ""

middleText c = many ((satisfy (/=c)) <|> notEndText c) 

comment o c = try (string ("%" ++ [o])) <++> middleText c <++> string (c : "%")

commentOut = comment '[' ']' 
commentGroup = comment '{' '}'
labelAnn = comment '(' ')'


-- ----------------------------------------------
-- annotations starting with %word
-- ----------------------------------------------

annote = try(char '%' <:> scanAnyWords) <++>
	 (((try(char '(') <:> middleText ')') <++> string ")%")
	  <|> textLine)

-- annotations between items
ann = many (skip (annote <|> labelAnn <|> commentGroup <|> commentLine))
      <?> "annotation"

-- ----------------------------------------------
-- lexical tokens with position
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token(s, (sourceLine p, sourceColumn p))

makeToken parser = skip(bind setTokPos getPosition parser)
