-- $Header$
module Token where

import Keywords
import Lexer
import Id (Id(Id), Token(..), Pos, place, isPlace)
import ParsecPos (SourcePos, sourceLine, sourceColumn) -- for setTokPos
import ParsecPrim (GenParser, (<?>), (<|>), getPosition, many, try)
import ParsecCombinator (many1, option, sepBy1)
import ParsecChar (char, string)

-- ----------------------------------------------
-- casl keyword handling
-- ----------------------------------------------

reserved :: [String] -> GenParser Char st String -> GenParser Char st String
-- "try" to avoid reading keywords 
reserved l p = try (p `checkWith` \r -> r `notElem` l)

scanTermSigns = reserved casl_reserved_ops scanAnySigns

scanSigns = reserved formula_ops scanTermSigns

scanTermWords = reserved casl_reserved_words scanAnyWords 

scanWords = reserved formula_words scanTermWords

-- ----------------------------------------------
-- lexical tokens with position
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token s (sourceLine p, sourceColumn p)

makeToken :: GenParser Char st String -> GenParser Char st Token
makeToken parser = skip(bind setTokPos getPosition parser)

asKey = makeToken . toKey

-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------

commaT = asKey commaS

oBracketT = asKey oBracketS <?> "" -- don't convey confusing mix-id tokens
cBracketT = asKey cBracketS
oBraceT = asKey oBraceS <?> ""
cBraceT = asKey cBraceS
placeT = makeToken (try (string place) <?> place)

-- simple id (but more than only words)
sid = makeToken (scanQuotedChar <|> scanDotWords 
		 <|> scanDigit <|> scanSigns 
		 <|> scanWords <?> "simple-id")

-- balanced mixfix-components {...}, [...]
braced = begDoEnd oBraceT innerList cBraceT
noComp = begDoEnd oBracketT innerList cBracketT

-- alternating sid and other mixfix components (including places)
-- no two sid stand side by side
innerMix1 = sid <:> option [] innerMix2
innerMix2 = flat (many1 (braced <|> noComp <|> many1 placeT))
            <++> option [] innerMix1

-- ingredients starting either with an sid or brackets, braces or place 
innerList =  option [] (innerMix1 <|> innerMix2 <?> "token")

-- a mixfix component starting with an sid (outside innerList)
topMix1 = sid <:> option [] topMix2

-- following an sid only braced mixfix-components are acceptable
-- square brackets after an sid will be taken as compound part
topMix2 = flat (many1 braced) <++> option [] topMix1

-- square brackets (as mixfix component) are ok following a place 
topMix3 = noComp <++> flat (many braced) <++> option [] topMix1

afterPlace = topMix1 <|> topMix2 <|> topMix3

-- places and something balanced possibly including places as well  
middle = many1 placeT <++> option [] afterPlace  

-- balanced stuff interspersed with places  
tokStart = afterPlace <++> flat (many middle)

-- at least two places on its own or a non-place possibly preceded by places 
start = tokStart <|> placeT <:> (tokStart <|> 
				 many1 placeT <++> option [] tokStart)
        <?> "id"

-- ----------------------------------------------
-- Mixfix Ids
-- ----------------------------------------------

-- a compound list
comps :: GenParser Char st ([Id], [Pos])
comps = do { o <- oBracketT 
	   ; (is, cs) <- parseId `separatedBy` commaT
	   ; c <- cBracketT
	   ; return (is, tokPos o : map tokPos cs ++ [tokPos c])
	   } <?> "[<id>,...,<id>]"

-- a compound list does not follow a place
-- but after a compound list further places may follow
parseId = do { l <- start
             ; if isPlace (last l) then return (Id l [] [])
	       else (do { (c, p) <- option ([], []) comps
			; u <- many placeT
			; return (Id (l++u) c p)
			})
	     }

-- ----------------------------------------------
-- SORT Ids
-- ----------------------------------------------

-- at least some no-bracket-signs should be disallowed for sorts

isSortId (t) =  tokStr t `notElem` non_sort_signs

-- sortIds are Ids without places, but possibly compound ids
-- only (the above) simple ids are taken here (brackets/braces are illegal) 
sortId = do { s <- sid `checkWith` isSortId
	    ; (c, p) <- option ([], []) comps
	    ; return (Id [s] c p)
	    }

-- ----------------------------------------------
-- SORT Ids
-- ----------------------------------------------
-- no compound ids (just a token) 
varId = sid
