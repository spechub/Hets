module Lexer where

import Char

import Id
import ParsecPos
import ParsecPrim
import ParsecCombinator
import ParsecChar

-- phase 1

type Scanner = Parser Token

special :: Scanner
special = fmap (\c -> Token([c], nullPos)) (oneOf "_.'()[]{};,`\"%·");

manyChar :: Parser Char -> Scanner
manyChar parser = fmap (\s -> Token(s, nullPos)) (many1 parser)

letters :: Scanner
letters =  manyChar letter
digits = manyChar digit
whitespace = manyChar space
signs = manyChar sign
others = manyChar anyChar

-- dot not included (see special)
sign :: Parser Char
sign = oneOf "+-*/|\\&=,`<>!?:$@#^~¡¿×÷£©±¶§¹²³¢º¬µ"


--    [\192-\207\209-\214\216-\221]             -> Letter  
--    [\223-\239\241-\246\248-\253\255]         -> Letter
--    [\161-\163\167\169\172\176-\179]          -> No-Bracket-Sign
--    [\181-\183\185\191\215\247]               -> No-Bracket-Sign



tokenize :: Scanner
tokenize = special <|> whitespace <|> digits <|> letters 
			<|> signs <|> others

setTokPos :: SourcePos -> Scanner -> Scanner
setTokPos p = fmap (\t-> setPos(t, (sourceLine p, sourceColumn p)))

fc :: Token -> Char
fc (Token (c : _, _)) = c
isLetter :: Token -> Bool 
isLetter  = isAlpha . fc  
isNumber  = isDigit . fc 
isPrime t = fc(t) == '\''
isDot t =  fc(t) == '.' || fc(t) == '·'
isUnderline t = showTok t == "_"

-- test
scanToken :: Scanner
scanToken = do {p <- getPosition; 
                setTokPos p tokenize; 
	       }

scan :: String -> [Token]
scan s = case parse (many scanToken) "" s of {Right ts -> ts} 
-- end test

-- phase 2
type TokScanner = GenParser Token () Token

getToken :: (Token -> Bool) -> TokScanner
getToken f = token showTok getPos (\x->if f(x) then Just x else Nothing)
    where getPos (Token(_, (l,c))) = newPos "" l c 

getLetters :: TokScanner
getLetters = getToken isLetter


scanLPD :: TokScanner
scanLPD = getLetters <|> (getToken isNumber) <|> (getToken isPrime)

tak :: Token->Token->Token
tak(Token(s,p))(Token(t,_))=Token(s++t,p)

takToks :: [Token] -> Token
takToks ts = foldl1 tak ts

scanWord :: TokScanner
scanWord = fmap takToks (many1 scanLPD)

scanLetterWord = do { t <- getLetters;
                      ts <- (many scanLPD);
                      return (takToks (t:ts))
		    }

getUnderline = getToken isUnderline

scanUnderlineWord = do { u <- getUnderline;
			 t <- scanWord <?> "word";
			 return (tak u t)
		       }
scanWords = do { t <- scanLetterWord;
                 ts <- (many scanUnderlineWord);
                 return (takToks (t:ts))
	       }
singleUnderline = do { u <- getUnderline;
                       notFollowedBy getUnderline;
		       return u
		     }


scanPlace = do { u1 <- getUnderline;
		 u2 <- getUnderline;
                 notFollowedBy getUnderline;
		 return (tak u1 u2)
	       }
-- test scanPlace
-- scan2 :: [Token] -> [Token]
-- scanPlace <|> anyToken