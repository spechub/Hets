module Lexer where

import Char
import Id
import Parsec

{-
import ParsecPos
import ParsecPrim
import ParsecCombinator
import ParsecChar
-}

-- special = "\"%(),;[]_{}"

newlineChars = "\n\r"

caslLetters = ['A'..'Z'] ++ ['a'..'z'] ++ 
              ['\192' .. '\207'] ++ -- \208 ETH 
              ['\209' .. '\214'] ++ -- \215 times
              ['\216' .. '\221'] ++ -- \222 THORN
              ['\223' .. '\239'] ++ -- \240 eth
              ['\241' .. '\246'] ++ -- \247 divide
              ['\248' .. '\253'] ++ -- \245 thorn
              ['\255'] 

blankChars = "\t\v\f \160" -- non breaking space

signChars = "!#$&*+-./:<=>?@\\^|~\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

-- see http://www.htmlhelp.com/reference/charset/
--    \172 neg
--    \183 middle dot
--    \215 times 

isWhitespace t = t `elem` (newlineChars ++ blankChars)
isSign brackets t = t `elem` (brackets ++ signChars)

getDot = oneOf ".\183"
getUnderline = char '_'

prime, caslLetter :: Parser Char
prime = char '\''
caslLetter = oneOf caslLetters

scanLPD :: Parser Char
scanLPD = caslLetter <|> digit <|> prime

scanWord :: Parser String
scanWord = many1 scanLPD
getNumber = many1 digit

scanLetterWord = do { t <- caslLetter; 
		      ts <- many scanLPD;
                      return (t:ts)
		    }

scanUnderlineWord = try(do { u <- getUnderline;
			     t <- scanWord <?> "word";
			     return (u:t)
			   })
casl_reserved_words = 
    "and arch as assoc axiom axioms closed comm end " ++
    "exists fit forall free from generated get given " ++
    "hide idem in lambda library local op ops pred preds " ++
    "result reveal sort sorts spec then to type types " ++
    "unit units var vars version view with within"


scanWords :: Parser String
scanWords = do { t <- scanLetterWord;
                 ts <- (many scanUnderlineWord);
		 let r = concat (t : ts) in
		 if r `elem` (words casl_reserved_words)
		 then unexpected "casl keyword"
                 else return r
	       } <?> "words"


scanDotWords = do { d <- char '.';
                    ws <- scanWords;
		    return (d:ws)
	       } <?> "dot-words"


casl_reserved_ops = ": :? ::= . · | |-> -> ->? "

scanSigns = do { r <- many1 (oneOf signChars);
		 if r `elem` (words casl_reserved_ops)
		 then unexpected "casl symbol"
		 else return r
	       } <?> "signs"

scanDigit = do { d <- digit;
		 return [d]
	       } 

scanSndPrime p = prime <?> "matching prime for prime at " ++ show p

scanQuotedChar = do { s <- between prime prime (caslChar <|> string "\"");
		      return ("'" ++ s ++ "'") 
                    } <?> "quoted char"

caslChar = escapeChar <|> printable
escapeChar = do { char '\\';
		  s <- simpleEscape <|> decEscape <|> hexEscape <|> octEscape;
		  return ('\\':s)
		}

simpleEscape = fmap (\x->[x]) (oneOf "'\"\\ntrvbfa?")

value base s = foldl (\x d -> base*x + toInteger (digitToInt d)) 0 s

decEscape = do { s <- count 3 digit;
		 if value 10 s <= 255 then return s
	         else unexpected "decimal escape code (> 255)"
	       }
hexEscape = do { char 'x';
		 s <- count 2 hexDigit; -- cannot be too big
		 return ('x':s)
	       }

octEscape = do { char 'o';
		 s <- count 3 octDigit;
		 if value 8 s <= 255 then return ('o':s)
	         else unexpected "octal escape code (> o377)"
	       }

printable = fmap (\x->[x]) (satisfy (\c -> (c /= '\'')  && (c /= '"') 
			      && (c /= '\\') && (c > '\026')))

dblquote = char '"'

scanString = do { s <- between dblquote dblquote (caslChar <|> string "'");
		  return ("\"" ++ s ++ "\"")
		} <?> "literal string"

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

scanEEqual = string "=e="

skip p = do {t <- p ; skipMany(satisfy isWhitespace); return t}

scToken = scanWords <|> scanDigit <|> scanQuotedChar <|>
	       try scanDotWords <|> try scanEEqual <|> scanSigns

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token(s, (sourceLine p, sourceColumn p))

makeToken parser = skip(do { p <- getPosition;
		             s <- parser;
			     return (setTokPos p s)
			   })

noBracketToken = makeToken scToken

scanPlace = makeToken((string "__") <?> "place")

scanMixLeaf = makeToken(try scanFloat <|> scanString <|> scToken)

-- tokens and Ids with brackets

bracketToken = makeToken (scToken <|> fmap (\x->[x]) (oneOf "{}[]"))

placeTokenId = do { p <- fmap TokId scanPlace;
                    option [p] 
		    (do { t <- compId;
			  return [p,t]
			});
		  }

placeTokenIds = fmap concat (many1 placeTokenId)

comps  = between (skip (char '[')) (skip (char ']')) 
	 (sepBy1 mixId (skip (char ',')))

compId = do { b <- fmap TokId bracketToken;
	      option b (do {cs <- comps; return (CompId b cs)})
	    }
		  
mixId = (do { l <- option [] (fmap (\x->[x]) compId);
	      ls <- option [] placeTokenIds;
	      let cs = l ++ ls in
              if length cs == 0 then unexpected "missing id"
	      else if length cs == 1 then return (head cs)
	      else return (MixId cs)
	    })
	     
scanSortToken = string "sort" >> option (' ') (char 's')
		
isSigStartKeyword s = s `elem` (words "sort sorts op ops pred preds type types var vars axiom axioms forall free generated .") 

-- comments and annotations

textLine = many (noneOf newlineChars)
eol = (eof >> return '\n') <|> oneOf newlineChars

commentLine = between (try (string "%%")) eol textLine

notEndText c = try(do { char c;
			notFollowedBy (char '%');
			return c;
		      }) <?> ""

middleText c = many ((satisfy (/=c)) <|> notEndText c) 

comment o c = between (try (string ("%" ++ [o]))) (string (c : "%")) 
	     (middleText c)

commentOut = comment '[' ']'
commentGroup = comment '{' '}'
label = comment '(' ')'

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






