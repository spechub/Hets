module Lexer where

import Char
import Id
import ParsecPos
import ParsecPrim
import ParsecCombinator
import ParsecChar

-- phase 1

special :: Parser String
special = fmap (\c -> [c]) (oneOf "_()[]{};,'\"%");

newlineChars = "\n\r"
newlines = many1 (oneOf newlineChars)

casl_letter = ['a'..'z'] ++ ['A'..'Z'] ++
              [toEnum(192) .. toEnum(207)] ++
              [toEnum(209) .. toEnum(214)] ++
              [toEnum(216) .. toEnum(221)] ++
              [toEnum(223) .. toEnum(239)] ++ -- icelandic eth
              [toEnum(241) .. toEnum(246)] ++
              [toEnum(248) .. toEnum(253)] ++ -- icelandic thorn
              [toEnum(255)] 

letters :: Parser String
letters =  many1 (oneOf casl_letter)
digits = many1 digit
blankChars = " \t\f\v\xA0"
blanks = many1 (oneOf blankChars)
signChars = ".·+-*/|\\&=,`<>!?:$@#^~¡¿×÷£©±¶§¹²³¢º¬µ"
signs = many1 (oneOf signChars)
others = many1 anyChar

--    [\192-\207\209-\214\216-\221]             -> Letter  
--    [\223-\239\241-\246\248-\253\255]         -> Letter
--    [\161-\163\167\169\172\176-\179]          -> No-Bracket-Sign
--    [\181-\183\185\191\215\247]               -> No-Bracket-Sign

tokenize :: Parser String
tokenize = special <|> newlines <|> blanks <|> digits 
	   <|> letters <|> signs <|> others

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token(s, (sourceLine p, sourceColumn p))

-- test
scanToken :: Parser Token
scanToken = do {p <- getPosition; 
                fmap (setTokPos p) tokenize; 
	       }

preScan :: String -> [Token]
preScan s = case parse (many scanToken) "" s of {Right ts -> ts} 
-- end test

-- phase 2
type TokScanner = GenParser Token () Token

getToken :: (Token -> Bool) -> TokScanner
getToken f = token showTok getPos (\x->if f(x) then Just x else Nothing)
    where getPos (Token(_, (l,c))) = newPos "" l c 

fc :: Token -> Char
fc (Token (c : _, _)) = c
isLetter :: Token -> Bool 
isLetter t = (fc t) `elem` casl_letter  
isNumber = isDigit . fc 

isWhitespace t = (fc t) `elem` (newlineChars ++ blankChars)
isSign brackets t = (fc t) `elem` (brackets ++ signChars)

getLetters :: TokScanner
getLetters = getToken isLetter

getStrToken s =  getToken (\t -> showTok t == s) 
getStrOrStrToken s1 s2 = getToken (\t -> let s = showTok t in s == s1 || s == s2) 

getNumber = getToken isNumber
getPrime = getStrToken "'"
getDot = getStrOrStrToken "." "·"
getUnderline = getStrToken "_"

scanLPD :: TokScanner
scanLPD = getLetters <|>  getNumber <|> getPrime

tak :: Token->Token->Token
tak(Token(s,p))(Token(t,_))=Token(s++t,p)

takToks :: [Token] -> Token
takToks ts = foldl1 tak ts

scanWord :: TokScanner
scanWord = fmap takToks (many1 scanLPD)

scanLetterWord = do { t <- getLetters; 
		      ts <- many scanLPD;
                      return (takToks (t:ts))
		    }

scanUnderlineWord = try(do { u <- getUnderline;
			     t <- scanWord <?> "word";
			     return (tak u t)
			   })
casl_reserved_words = 
    "and arch as assoc axiom axioms closed comm end " ++
    "exists fit forall free from generated get given " ++
    "hide idem in lambda library local op ops pred preds " ++
    "result reveal sort sorts spec then to type types " ++
    "unit units var vars version view with within"

scanWords = do { t <- scanLetterWord;
                 ts <- (many scanUnderlineWord);
		 let r = takToks (t:ts) in
		 if (showTok r) `elem` (words casl_reserved_words)
		 then unexpected "casl keyword"
                 else return r
	       } <?> "words"

scanDotWords = do { d <- getDot;
                    ws <- scanWords;
		    return (tak d ws)
	       } <?> "dot-words"

scanPlace = do { u1 <- getUnderline;
		 u2 <- getUnderline <?> "place";
-- comment out next line, if 4 underlines are two places
                 notFollowedBy getUnderline;
		 return (tak u1 u2)
	       }

casl_reserved_ops = ": :? ::= . · | |-> -> ->? "

scanSigns bs = do { r <- many1 (getToken (isSign bs));
		    let t = takToks (r) in 
		    if (showTok t) `elem` (words casl_reserved_ops)
			  then unexpected "casl symbol"
			  else return t
		  } <?> "signs"

scanDigit = do { t <- getNumber;
		 if (length (showTok t) == 1) then return t
		 else unexpected "digits"
	       } <?> "single digit"


scanSndPrime p = getPrime <?> "matching prime for prime at " ++ show p

scanQuotedChar = do { p <- getPosition;
		      t <- getPrime <?> "quoted char";
		      ts <- manyTill anyToken (scanSndPrime p);
		      let toks = takToks (t:ts) 
		          ptoks = tak toks t in 
		      if (showTok toks == "'\\") -- prime ++ escaped prime
		      then (scanSndPrime p) >> (return (tak ptoks t)) 
		      else return ptoks 
		    } 

scanFloat = do { n1 <- getNumber <?> "number, fraction or float";
		 n3 <- option n1 
		 (do { d <- getStrToken ".";
		       n2 <- getNumber;
		       return (takToks [n1,d,n2])
		     });
		 option n3
		 (do { e <- getStrToken "E";
		       o <- option e 
		       (do { s <- getStrOrStrToken "+" "-";
			     return (tak e s)
			   });
		       n4 <- getNumber;
		       return (takToks [n3,o,n4])
		     });
	       }

scanEEqual = do { e1 <-  getStrToken "=";
	      e2 <-  getStrToken "e";
	      e3 <-  getStrToken "=";
	      return (takToks [e1,e2,e3])
	    }

skipWhites p = do {t <- p ; skipMany(getToken isWhitespace); return t}

scToken bs = scanWords <|> scanDigit <|> scanQuotedChar <|>
	       (try scanDotWords) <|> (try scanEEqual) <|> (scanSigns bs)

noBracketToken = scToken ""
bracketToken = scToken "{}[]"

mixToken = many1 (skipWhites(scanPlace <|> bracketToken) )

opSquare = skipWhites (getToken (\t -> showTok t == "[") )
clSquare = skipWhites (getToken (\t -> showTok t == "]") )
comma = skipWhites (getToken (\t -> showTok t == ",") )

compToken = do { ts <- mixToken;
		 option (Id(ts, [])) 
		 (do { opSquare;
		       cs <- sepBy1 compToken comma;
		       clSquare;
		       return (Id(ts, cs))
		     } )
		}


		 




scanSortToken = getStrOrStrToken "sort" "sorts"

		
isSigStartKeyword s = s `elem` (words "sort sorts op ops pred preds type types var vars axiom axioms forall free generated .") 

-- parseSortItems = do {scanSortToken;
--                     s <- scanSort
                         
		        

-- test scanPlace
-- scan2 :: [Token] -> [Token]
-- scanPlace <|> anyToken