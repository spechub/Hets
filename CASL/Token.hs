-- $Header$
module Token ( scanWords, scanSigns, makeToken, asKey
	     , sepChar, opBrkt, clBrkt, oBrace, cBrace, uu, comma
	     , parseId, sortId, varId, colonChar, equalStr, lessStr
	     , partialSuffix, totalFunArrow, partialFunArrow 
	     , totalFunArrow, productSign, altProductSign
	     ) where

import Lexer
import Id (Id(Id), Token(..), Pos, place, isPlace)
import ParsecPos (SourcePos, sourceLine, sourceColumn) -- for setTokPos
import ParsecPrim (Parser, (<?>), (<|>), getPosition, many, try)
import ParsecCombinator (many1, option, sepBy1)
import ParsecChar (char, string)

-- ----------------------------------------------
-- casl keyword handling
-- ----------------------------------------------

reserved :: [String] -> Parser String -> Parser String
-- "try" to avoid reading keywords 
reserved l p = try (p `checkWith` \r -> r `notElem` l)

-- sign keywords
casl_reserved_ops = [":", ":?","::=",".","\183","|","|->"]

-- these signs are legal in terms, but illegal in declarations
formula_ops = ["=", "=>", "<=>", "\\/", "/\\", "\172"] 

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
formula_words = ["def", "else", "if", "when", "false", "not", "true"]

scanTermWords = reserved casl_reserved_words scanAnyWords 

scanWords = reserved formula_words scanTermWords

-- ----------------------------------------------
-- lexical tokens with position
-- ----------------------------------------------

setTokPos :: SourcePos -> String -> Token
setTokPos p s = Token s (sourceLine p, sourceColumn p)

makeToken parser = skip(bind setTokPos getPosition parser)

sepChar = makeToken . single . char

asKey = makeToken . toKey

-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------

opBrkt = sepChar '[' <?> "" -- don't convey confusing mix-id tokens
clBrkt = sepChar ']'
oBrace = sepChar '{' <?> ""
cBrace = sepChar '}'
uu = makeToken (try (string place) <?> "place")

-- simple id (but more than only words)
sid = makeToken (scanQuotedChar <|> scanDotWords 
		 <|> scanDigit <|> scanSigns 
		 <|> scanWords <?> "simple-id")

-- balanced mixfix-components {...}, [...]
braced = begDoEnd oBrace innerList cBrace
noComp = begDoEnd opBrkt innerList clBrkt

-- alternating sid and other mixfix components (including places)
-- no two sid stand side by side
innerMix1 = sid <:> option [] innerMix2
innerMix2 = flat (many1 (braced <|> noComp <|> many1 uu))
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
middle = many1 uu <++> option [] afterPlace  

-- balanced stuff interspersed with places  
tokStart = afterPlace <++> flat (many middle)

-- at least two places on its own or a non-place possibly preceded by places 
start = tokStart <|> uu <:> (tokStart <|> many1 uu <++> option [] tokStart)
        <?> "id"

comma = sepChar ','

-- ----------------------------------------------
-- Mixfix Ids
-- ----------------------------------------------

-- a compound list
comps :: Parser ([Id], [Pos])
comps = do { o <- opBrkt 
	   ; (is, cs) <- parseId `separatedBy` comma
	   ; c <- clBrkt
	   ; return (is, tokPos o : map tokPos cs ++ [tokPos c])
	   } <?> "[<id>,...,<id>]"

-- a compound list does not follow a place
-- but after a compound list further places may follow
parseId = do { l <- start
             ; if isPlace (last l) then return (Id l [] [])
	       else (do { (c, p) <- option ([], []) comps
			; u <- many uu
			; return (Id (l++u) c p)
			})
	     }

-- ----------------------------------------------
-- SORT Ids
-- ----------------------------------------------

-- at least some no-bracket-signs should be disallowed for sorts
colonChar = ':'
equalStr = "="
lessStr = "<"
partialSuffix = "?"
totalFunArrow = "->"
partialFunArrow = totalFunArrow ++ partialSuffix
productSign = "*"
altProductSign = "\215"

isSortId (t) = 
        tokStr t `notElem` 
          [[colonChar], equalStr, lessStr, productSign, altProductSign, 
	   partialSuffix, totalFunArrow, partialFunArrow]

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
