module Lexer where

import Char
import Id
import ParsecPos
import ParsecPrim
import ParsecCombinator
import ParsecChar

-- ----------------------------------------------
-- no-bracket-signs
-- ----------------------------------------------
signChars = "!#$&*+-./:<=>?@\\^|~" ++ "°¢£ß©¨∞±≤≥µ∂∑πø◊˜"

-- "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

--    \172 neg
--    \183 middle dot
--    \215 times 

scanAnySigns = many1 (oneOf signChars) <?> "signs"

scanPlace = try (string place) <?> "place"

-- ----------------------------------------------
-- casl letters
-- ----------------------------------------------
caslLetters = ['A'..'Z'] ++ ['a'..'z'] ++ 
	      "¿¡¬√ƒ≈∆«»… ÀÃÕŒœ—“”‘’÷ÿŸ⁄€‹›ﬂ‡·‚„‰ÂÊÁËÈÍÎÏÌÓÔÒÚÛÙıˆ¯˘˙˚¸˝ˇ"

{- see http://www.htmlhelp.com/reference/charset/
              ['\192' .. '\207'] ++ -- \208 ETH 
              ['\209' .. '\214'] ++ -- \215 times
              ['\216' .. '\221'] ++ -- \222 THORN
              ['\223' .. '\239'] ++ -- \240 eth
              ['\241' .. '\246'] ++ -- \247 divide
              ['\248' .. '\253'] ++ -- \254 thorn
              ['\255'] 
-}

caslLetter :: Parser Char
caslLetter = oneOf caslLetters <?> "casl letter"

prime = char '\'' -- also used for quoted chars

scanLPD :: Parser Char
scanLPD = caslLetter <|> digit <|> prime <?> "word"

-- ----------------------------------------------
-- parsec/Monad extension
infixr 1 <:>

-- (<:>) :: GenParser tok st a -> GenParser tok st [a] -> GenParser tok st [a]
(<:>) :: (Monad m) => m a -> m [a] -> m [a]
(<:>) p1 p2 = do { e <- p1; l <- p2; return (e:l) } 

-- ----------------------------------------------
-- casl words
-- ----------------------------------------------

scanLetterWord = caslLetter <:> many scanLPD

singleUnderline = try (do { c <- char '_'
			  ; lookAhead scanLPD
			  ; return c
			  }) 

scanUnderlineWord = singleUnderline <:> many1 scanLPD <?> "word"

scanAnyWords :: Parser String
scanAnyWords = do { ws <- scanLetterWord <:> many scanUnderlineWord <?> "words"
		  ; return (concat ws)
		  } 

scanDot = try (do { d <- char '.'
		  ; lookAhead caslLetter
		  ; return d
		  })

scanDotWords = scanDot <:> scanAnyWords <?> "dot-words"

-- ----------------------------------------------
-- parsec/Functor extension
single :: (Functor f) => f a -> f [a]
single p = fmap (:[]) p 

-- see ParsecToken.number
value :: Int -> String -> Int
value base s = foldl (\x d -> base*x + (digitToInt d)) 0 s

-- ----------------------------------------------
-- casl escape chars for quoted chars and literal strings
-- ----------------------------------------------

simpleEscape = single (oneOf "'\"\\ntrvbfa?")

decEscape = do { s <- count 3 digit;
		 if value 10 s <= 255 then return s
	         else unexpected "decimal escape code (> 255)"
	       }
hexEscape = char 'x' <:> count 2 hexDigit -- cannot be too big

octEscape = do { c <- char 'o';
		 s <- count 3 octDigit;
		 if value 8 s <= 255 then return (c:s)
	         else unexpected "octal escape code (> o377)"
	       }

escapeChar = char '\\' <:> 
	     (simpleEscape <|> decEscape <|> hexEscape <|> octEscape)

-- ----------------------------------------------
-- chars for quoted chars and literal strings
-- ----------------------------------------------

printable = single (satisfy (\c -> (c /= '\'')  && (c /= '"') 
			      && (c /= '\\') && (c > '\026')))

caslChar = escapeChar <|> printable


scanQuotedChar = do { s <- between prime prime (caslChar <|> string "\"");
		      return ("'" ++ s ++ "'") 
                    } <?> "quoted char"

dblquote = char '"'

scanString = do { s <- between dblquote dblquote (caslChar <|> string "'");
		  return ("\"" ++ s ++ "\"")
		} <?> "literal string"

-- ----------------------------------------------
-- digit, number, fraction, float
-- ----------------------------------------------

getNumber = many1 digit

scanFloat = do { n1 <- getNumber <?> "number, fraction or float";
		 n3 <- option n1 
		 (do { d <- char '.';
		       n2 <- getNumber;
		       return (n1 ++ d:n2)
		     });
		 n5 <- option n3
		 (do { e <- char 'E';
		       o <- option [e] 
		       (do { s <- oneOf "+-";
			     return (e:[s])
			   });
		       n4 <- getNumber;
		       return (n3 ++ o ++ n4)
		     });
		 if length n5 == 1 then unexpected "single digit"
		 else return n5
	       }

scanDigit = do { n <- getNumber;
                 if length n > 1 then unexpected "multiple digits"
		 else return n
	       }


-- ----------------------------------------------
-- comments and label
-- ----------------------------------------------

newlineChars = "\n\r"

textLine = many (noneOf newlineChars)
eol = (eof >> return '\n') <|> oneOf newlineChars

commentLine = between (try (string "%%")) eol textLine
              >>= return . ("%%" ++)

notEndText c = try (do { char c;
			notFollowedBy (char '%');
			return c;
		      }) <?> ""

middleText c = many ((satisfy (/=c)) <|> notEndText c) 

comment o c = let op = "%" ++ [o]
		  cl = c : "%"
	      in do { t <- between (try (string op)) (string cl) 
		          (middleText c);
		      return (op ++ t ++ cl)
		    }

commentOut = comment '[' ']' 
commentGroup = comment '{' '}'
labelAnn = comment '(' ')'

-- ----------------------------------------------
-- skip whitespaces and comment out
-- ----------------------------------------------

blankChars = "\t\v\f \160" -- non breaking space

skip p = do {t <- p ; 
	     skipMany(single (oneOf (newlineChars ++ blankChars)) 
		      <|> commentOut <?> "");
	     return t} 

-- ----------------------------------------------
-- annotations starting with %word
-- ----------------------------------------------

-- starting with %word
annote = 
    do { w <- try ((char '%') >> scanAnyWords);
         (do { try(char '(');
		   t <- middleText ')';
	       string ")%";
	       return ("%" ++ w ++ "(" ++ t ++ ")%")
	     })  
	 <|> (do { t <- textLine;
                   eol; 
		   return ("%" ++ w ++ t)
		 })
       }

-- annotations between items
ann = many (skip (annote <|> labelAnn <|> commentGroup <|> commentLine))
      <?> "annotation"

-- ----------------------------------------------
-- lexical tokens with position
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token(s, (sourceLine p, sourceColumn p))

makeToken parser = skip(do { p <- getPosition;
		             s <- parser;
			     return (setTokPos p s)
			   })

