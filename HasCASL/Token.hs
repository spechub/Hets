module Token where

import Lexer
import Id
import ParsecPos
import ParsecPrim
import ParsecCombinator
import ParsecChar

casl_reserved_ops = [":?","::=",".","\183","|","|->","->","->?"]

special_ops = [":","="]
formula_ops = ["=>","<=>","\\/","/\\","\172"] 

scanTermSigns = reserved casl_reserved_ops scanAnySigns

scanSigns = reserved (special_ops ++ formula_ops) scanTermSigns

casl_reserved_words = words( 
    "and arch assoc axiom axioms closed comm end " ++
    "exists fit forall free from generated get given " ++
    "hide idem lambda library local op ops pred preds " ++
    "result reveal sort sorts spec then to type types " ++
    "unit units var vars version view with within")

-- these words are legal in terms, but illegal in declarations
poly_words = ["def","else","when"]
mono_words = ["false","not","true"]
type_words = ["as","in"]


reserved :: [String] -> Parser String -> Parser String
reserved l p = p `checkWith` (\r -> r `notElem` l) 

scanTermWords = reserved casl_reserved_words scanAnyWords 

scanWords = reserved (poly_words 
		      ++ mono_words
		      ++ type_words
		     ) scanTermWords

-- ----------------------------------------------
-- no-bracket-token, literal or place (for terms)
-- ----------------------------------------------

otherToken = scanDigit <|> scanQuotedChar <|> scanDotWords

scanMixLeaf = makeToken(try scanFloat <|> scanString <|> otherToken 
			<|> scanTermWords <|> try (string "=e=") 
			<|> scanTermSigns <|> scanPlace)

-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------

obr = makeToken (single (char '['))
cbr = makeToken (single (char ']'))
ocb = makeToken (single (char '{'))
ccb = makeToken (single (char '}'))
uu = makeToken (scanPlace)

-- simple id
sid = makeToken (otherToken <|> scanSigns <|> scanWords) <?> "simple-id"

curly =  begDoEnd ocb iList ccb
noComp = begDoEnd obr iList cbr 

singleId = single (sid `notFollowedWith` sid)

iList =  fmap concat (many (many1 uu
	          <|> singleId 
                  <|> curly
	          <|> noComp)) 

afterPlace =  (curly <|> noComp <|> singleId) <++>
		 flat (many (curly <|> singleId))

middle = many1 uu <++> option [] afterPlace  <?> "mix-id"

start = many uu <++>
	option [] (afterPlace <++> flat (many middle))

checkStart = start `checkWith` (\l -> length l > 1 || 
				(length l == 1 && not(isPlace(head l))))
	     <?> "id"

comps = between obr cbr
	(sepBy1 parseId (skip (char ','))) <?> "[<id>,...,<id>]"

parseId = do { l <- checkStart
             ; if isPlace (last l) then return (Id l [])
	       else (do { c <- option [] comps
			; u <- many uu
			; return (Id (l++u) c)
			})
	     }
