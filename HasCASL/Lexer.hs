module Lexer where

import Char
import Id
-- import Parsec

import ParsecPos
import ParsecPrim
import ParsecCombinator
import ParsecChar


-- ----------------------------------------------
-- casl letters
-- ----------------------------------------------
caslLetters = ['A'..'Z'] ++ ['a'..'z'] ++ 
	      "¿¡¬√ƒ≈∆«»… ÀÃÕŒœ—“”‘’÷ÿŸ⁄€‹›ﬂ‡·‚„‰ÂÊÁËÈÍÎÏÌÓÔÒÚÛÙıˆ¯˘˙˚¸˝ˇ"
{-
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

-- excluded or "casl-builtin" ids in terms and formulae
casl_reserved_words = 
    "and arch as assoc axiom axioms closed comm end " ++
    "exists fit forall free from generated get given " ++
    "hide idem in lambda library local op ops pred preds " ++
    "result reveal sort sorts spec then to type types " ++
    "unit units var vars version view with within"

reserved :: [String] -> Parser String -> Parser String
reserved l p = do { r <- p 
		  ; if r `elem` l 
		    then unexpected ("reserved keyword: " ++ r)
		    else return r
		  }

scanAnyWords :: Parser String
scanAnyWords = do { ws <- scanLetterWord <:> many scanUnderlineWord <?> "words"
		  ; return (concat ws)
		  } 

scanWords = reserved (words casl_reserved_words) scanAnyWords

scanDot = try (do { d <- char '.'
		  ; lookAhead caslLetter
		  ; return d
		  })

scanDotWords = scanDot <:> scanAnyWords <?> "dot-words"

-- ----------------------------------------------
-- no-bracket-signs
-- ----------------------------------------------
signChars = "!#$&*+-./:<=>?@\\^|~" ++ "°¢£ß©¨∞±≤≥µ∂∑πø◊˜"

-- "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

-- see http://www.htmlhelp.com/reference/charset/
--    \172 neg
--    \183 middle dot
--    \215 times 

casl_reserved_ops = [":",":?","::=",".","\183","|","|->","->","->?"]

scanAnySigns = many1 (oneOf signChars) <?> "signs"
scanSigns = reserved casl_reserved_ops scanAnySigns

-- ----------------------------------------------
-- parsec/Functor extension
single :: (Functor f) => f a -> f [a]
single p = fmap (:[]) p 

-- see ParsecToken.number
value base s = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 s

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
    do { w <- try ((char '%') >> scanWords);
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
-- no-bracket-token, literal or place (for terms)
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token(s, (sourceLine p, sourceColumn p))

makeToken parser = skip(do { p <- getPosition;
		             s <- parser;
			     return (setTokPos p s)
			   })

scanPlace = try (string place) <?> "place"

scToken = scanWords <|> scanDigit <|> scanQuotedChar <|>
	       scanDotWords

scanMixLeaf = makeToken(try scanFloat <|> scanString <|> scToken 
			<|> try (string "=e=") <|> scanSigns <|> scanPlace)



-- ----------------------------------------------
-- balanced brackets
-- ----------------------------------------------

balanced = many (noneOf brackets
		 <|>
		 between (char '[')(char ']') balanced
                 <|>			    
		 between (char '{')(char '}') balanced) >> return ' ' 

isBalanced ts = let s = concat (map show ts) in
		    case parse (balanced >> eof) "" s of 
						      Right _ -> True 
						      _ -> False



-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------

brackets = "{}[]"

-- bracket signs must not be separated by spaces
anyBracketSigns = fmap concat (many1 (scanAnySigns 
				   <|> single (oneOf brackets) 
				   <?> "bracket signs"))

bracketSigns = reserved casl_reserved_ops anyBracketSigns 

bracketToken = makeToken (scToken <|> bracketSigns <?> "id")

comps = between (skip (char '[')) (skip (char ']')) 
	(sepBy1 parseId (skip (char ','))) <?> "[<id>,...,<id>]"

placeToken = makeToken scanPlace

-- several tokens between places are not allowed
-- the last token may have a compound list (for the whole mixfix id) 

mixId l = do {  b <- many placeToken <?> "id"
	     ;  (if isBalanced l then
		 ((lookAhead ( char ']') <?> "") >> return (l ++ b))
		else fail "")
                <|> continue (l ++ b)
	     }

continue l = do { t <- bracketToken
		; let s = l ++ [t] in
	              (do { p <- many1 placeToken
			  ; option (s ++ p) (mixId (s ++ p))
			  })
	              <|> return s
		}

compEnd p = do { c <- comps
	       ; l <- many placeToken
	       ; return (Id (p ++ l) c)
	       }

parseId = do { l <- mixId [];
	       if isBalanced l then
	       if null l then unexpected "empty id"
	       else if isPlace (last l) then
	               if all isPlace l then unexpected "places only"
	               else return (Id l [])
	             else option (Id l []) (compEnd l)
	       else unexpected ("unbalanced brackets id: " ++ (show (Id l [])))
	     }


		





