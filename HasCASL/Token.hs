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

obr = skipChar '[' <?> "" -- don't convey confusing mix-id tokens
cbr = skipChar ']'
ocb = skipChar '{' <?> ""
ccb = skipChar '}'
uu = makeToken (try (string place) <?> "place")

-- simple id
sid = single (makeToken (otherToken <|> scanSigns 
			 <|> scanWords <?> "simple-id"))

curly =  begDoEnd ocb innerList ccb
noComp = begDoEnd obr innerList cbr

innerMix1 = sid <++> option [] innerMix2
innerMix2 = flat (many1 (curly <|> noComp <|> many1 uu))
            <++> option [] innerMix1

innerList =  option [] (innerMix1 <|> innerMix2 <?> "token")

topMix1 = sid <++> option [] topMix2
topMix2 = flat (many1 curly) <++> option [] topMix1

topMix3 = noComp <++> flat (many curly) <++> option [] topMix1

afterPlace = topMix1 <|> topMix2 <|> topMix3

middle = many1 uu <++> option [] afterPlace  

tokStart = afterPlace <++> flat (many middle)

start = tokStart <|> uu <:> (tokStart <|> many1 uu <++> option [] tokStart)
        <?> "id"

comps = obr >> (parseId `sepBy1` skip (char ',')) << cbr 
	<?> "[<id>,...,<id>]"

parseId = do { l <- start
             ; if isPlace (last l) then return (Id l [])
	       else (do { c <- option [] comps
			; u <- many uu
			; return (Id (l++u) c)
			})
	     }
