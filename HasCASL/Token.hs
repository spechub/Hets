module Token ( scanTermWords, scanTermSigns, otherToken, makeToken
	     , skipChar, obr, cbr, ocb, ccb, uu, parseId
	     ) where

import Lexer
import Id (Id(Id), Token(Token), place, isPlace)
import ParsecPos (SourcePos, sourceLine, sourceColumn) -- for setTokPos
import ParsecPrim (Parser, (<?>), (<|>), getPosition, many, try)
import ParsecCombinator (many1, option, sepBy1)
import ParsecChar (char, string)

-- ----------------------------------------------
-- casl keyword handling
-- ----------------------------------------------

reserved :: [String] -> Parser String -> Parser String
reserved l p = p `checkWith` \r -> r `notElem` l 

-- sign keywords
casl_reserved_ops = [":", ":?","::=",".","\183","|","|->","->","->?"]

-- these signs are legal in terms, but illegal in declarations
formula_ops = ["=", "=>","<=>","\\/","/\\","\172"] 

scanTermSigns = reserved casl_reserved_ops scanAnySigns

scanSigns = reserved formula_ops scanTermSigns

-- letter keywords
casl_reserved_words = words( 
    "and arch as assoc axiom axioms closed comm end " ++
    "exists fit forall free from generated get given " ++
    "hide idem in lambda library local op ops pred preds " ++
    "result reveal sort sorts spec then to type types " ++
    "unit units var vars version view with within")

-- these words are legal in terms, but illegal in declarations
poly_words = ["def","else","when"]
mono_words = ["false","not","true"]

scanTermWords = reserved casl_reserved_words scanAnyWords 

scanWords = reserved (poly_words 
		      ++ mono_words
		     ) scanTermWords

otherToken = scanDigit <|> scanQuotedChar <|> scanDotWords

-- ----------------------------------------------
-- lexical tokens with position
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token(s, (sourceLine p, sourceColumn p))

makeToken parser = skip(bind setTokPos getPosition parser)

skipChar = makeToken . single . char

-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------

obr = skipChar '['
cbr = skipChar ']'
ocb = skipChar '{'
ccb = skipChar '}'
uu = makeToken (try (string place) <?> "place")

-- simple id
sid = makeToken (otherToken <|> scanSigns <|> scanWords)

singleId = single (sid `notFollowedWith` sid) 

curly =  begDoEnd ocb iList ccb
noComp = begDoEnd obr iList cbr 

iList =  flat (many (many1 uu
	             <|> singleId 
                     <|> curly
	             <|> noComp)) <?> "mix-id-tokens" 

afterPlace =  (curly <|> noComp <|> singleId <?> "token") <++>
		 flat (many (curly <|> singleId <?> "mix-id-token"))

middle = many1 uu <++> option [] afterPlace  

tokStart = afterPlace <++> flat (many middle)

start = tokStart <|> uu <:> (tokStart <|> many1 uu <++> option [] tokStart)
        <?> "mix-id"

comps = obr >> (parseId `sepBy1` skip (char ',')) << cbr 
	<?> "[<id>,...,<id>]"

parseId = do { l <- start
             ; if isPlace (last l) then return (Id l [])
	       else (do { c <- option [] comps
			; u <- many uu
			; return (Id (l++u) c)
			})
	     }
