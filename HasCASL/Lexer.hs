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

-- ----------------------------------------------
-- casl letters
-- ----------------------------------------------
caslLetters = ['A'..'Z'] ++ ['a'..'z'] ++ 
              ['\192' .. '\207'] ++ -- \208 ETH 
              ['\209' .. '\214'] ++ -- \215 times
              ['\216' .. '\221'] ++ -- \222 THORN
              ['\223' .. '\239'] ++ -- \240 eth
              ['\241' .. '\246'] ++ -- \247 divide
              ['\248' .. '\253'] ++ -- \245 thorn
              ['\255'] 

caslLetter :: Parser Char
caslLetter = oneOf caslLetters <?> "casl letter"

prime = char '\'' -- also used for quoted chars

scanLPD :: Parser Char
scanLPD = caslLetter <|> digit <|> prime

-- ----------------------------------------------
-- parsec/Monad extension
infixr 1 <:>

-- (<:>) :: GenParser tok st a -> GenParser tok st [a] -> GenParser tok st [a]
(<:>) :: (Monad m) => m a -> m [a] -> m [a]
(<:>) p1 p2 = do { e <- p1; l <- p2; return (e:l) } 

-- ----------------------------------------------
-- casl words
-- ----------------------------------------------

scanLetterWord = try caslLetter <:> many scanLPD

scanUnderlineWord = try(char '_') <:> many1 scanLPD

-- excluded or "casl-builtin" ids in terms and formulae
casl_reserved_words = 
    "and arch as assoc axiom axioms closed comm end " ++
    "exists fit forall free from generated get given " ++
    "hide idem in lambda library local op ops pred preds " ++
    "result reveal sort sorts spec then to type types " ++
    "unit units var vars version view with within"

scanWords :: Parser String
scanWords = do { ws <- scanLetterWord <:> many scanUnderlineWord;
		 let r = concat ws in
		 if r `elem` (words casl_reserved_words)
		 then unexpected "casl keyword"
                 else return r
	       } <?> "words"

scanDotWords = try (char '.') <:> scanWords <?> "dot-words"

-- ----------------------------------------------
-- no-bracket-signs
-- ----------------------------------------------
signChars = "!#$&*+-./:<=>?@\\^|~\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

-- see http://www.htmlhelp.com/reference/charset/
--    \172 neg
--    \183 middle dot
--    \215 times 

casl_reserved_ops = ": :? ::= . · | |-> -> ->? "

scanSigns = try (string "=e=") <|>
	    do { r <- many1 (oneOf signChars);
		 if r `elem` (words casl_reserved_ops)
		 then unexpected "casl symbol"
		 else return r
	       } <?> "signs"

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

scanDigit = single digit


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
		      <|> commentOut);
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

-- ----------------------------------------------
-- no-bracket-token, literal or place (for terms)
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token(s, (sourceLine p, sourceColumn p))

makeToken parser = skip(do { p <- getPosition;
		             s <- parser;
			     return (setTokPos p s)
			   })

scanPlace = (string "__") <?> "place"

scToken = scanWords <|> scanDigit <|> scanQuotedChar <|>
	       scanDotWords

scanMixLeaf = makeToken(try scanFloat <|> scanString 
			<|> scToken <|> scanSigns <|> scanPlace)

-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------

placeToken = fmap TokId (makeToken scanPlace)

brackets = "{}[]"

-- bracket signs must not be separated by spaces
bracketSigns = fmap concat (many1 (scanSigns 
				   <|> single (oneOf brackets) 
				   <?> "bracket signs"))

bracketToken = fmap TokId (makeToken (scToken <|> bracketSigns))

-- several tokens between places are currently not allowed
placeTokenId = do { p <- placeToken;
                    option [p] 
		    (do { t <- compId;
			  return [p,t]
			});
		  }

placeTokenIds = fmap concat (many1 placeTokenId)

comps  = between (skip (char '[')) (skip (char ']')) 
	 (sepBy1 mixId (skip (char ','))) <?> "[<id>,...,<id>]"

compId = do { b <- bracketToken;
	      option b (do {cs <- comps; return (CompId b cs)})
	    }
		  
-- balanced brackets
balanced = many (noneOf brackets
		 <|>
		 between (char '[')(char ']') balanced
                 <|>			    
		 between (char '{')(char '}') balanced) >> return ' ' 

isBalanced t = case parse (balanced >> eof) "" t of {Right _ -> True; _ -> False}

mixId = (do { l <- option [] (single compId);
	      ls <- option [] placeTokenIds;
	      let cs = l ++ ls in
	      if isBalanced (show (MixId cs)) then
	      (if length cs == 0 then unexpected "missing id"
	       else if length cs == 1 then return (head cs)
	       else return (MixId cs))
	      else unexpected "unbalanced brackets id" 
	    })

-- a compound list after the last place is still missing

		





