
{- HetCATS/HasCASL/HToken.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL IDs
   adapted from HetCATS/CASL/Token.hs, v 1.9
-}

module HToken where

import Id
import Keywords
import Lexer
import Parsec

-- ----------------------------------------------
-- further hascasl keyword
-- ----------------------------------------------
assignS = ":="
minusS = "-"
plusS = "+"
pFun = funS ++ quMark
contFun = minusS ++ funS
pContFun = minusS ++ pFun
lamS = "\\"
asP = "@"

classS = "class"
programS = "program"
instanceS = "instance"
caseS = "case"
ofS = "of"
whereS = "where"

-- ----------------------------------------------
-- hascasl keyword handling
-- ----------------------------------------------


hascasl_reserved_ops = [asP, assignS, lamS] ++ casl_reserved_ops

hascasl_type_ops = [funS, pFun, contFun, pContFun, prodS, timesS, quMark, 
		   lessS] 

hascasl_reserved_words = [classS, instanceS, programS, caseS, ofS, whereS] 
			 ++ formula_words ++ casl_reserved_words

scanWords = reserved hascasl_reserved_words scanAnyWords 

-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------

-- simple id (but more than only words)
sid l = pToken (scanQuotedChar <|> scanDotWords 
		<|> scanDigit <|> reserved l scanAnySigns 
		<|> scanWords <?> "simple-id")

-- balanced mixfix-components {...}, [...]
braced l = begDoEnd oBraceT (innerList l) cBraceT
noComp l = begDoEnd oBracketT (innerList l) cBracketT

-- alternating sid and other mixfix components (including places)
-- no two sid stand side by side
innerMix1 l = sid l <:> option [] (innerMix2 l)
innerMix2 l = flat (many1 (braced l <|> noComp l<|> many1 placeT))
            <++> option [] (innerMix1 l)

-- ingredients starting either with an sid or brackets, braces or place 
innerList l =  option [] (innerMix1 l <|> innerMix2 l <?> "token")

-- a mixfix component starting with an sid (outside innerList)
topMix1 l = sid l <:> option [] (topMix2 l)

-- following an sid only braced mixfix-components are acceptable
-- square brackets after an sid will be taken as compound part
topMix2 l = flat (many1 (braced l)) <++> option [] (topMix1 l)

-- square brackets (as mixfix component) are ok following a place 
topMix3 l = noComp l <++> flat (many (braced l)) <++> option [] (topMix1 l)

afterPlace l = topMix1 l <|> topMix2 l<|> topMix3 l

-- places and something balanced possibly including places as well  
middle l = many1 placeT <++> option [] (afterPlace l)  

-- balanced stuff interspersed with places  
tokStart l = afterPlace l <++> flat (many (middle l))

-- at least two places on its own or a non-place possibly preceded by places 
start l = tokStart l <|> placeT <:> (tokStart l <|> 
				 many1 placeT <++> option [] (tokStart l))
				     <?> "id"
-- ----------------------------------------------
-- non-compound mixfix ids (variables)
-- ----------------------------------------------
var :: GenParser Char st Id
var = fmap (\l -> Id l [] []) (start hascasl_reserved_ops)

-- ----------------------------------------------
-- compound/bracketed lists
-- ----------------------------------------------
bracketParser :: GenParser Char st a -> GenParser Char st Token 
	 -> GenParser Char st Token -> GenParser Char st Token
	 -> ([a] -> [Pos] -> b) -> GenParser Char st b

bracketParser parser op cl sep k = 
    do o <- op
       (ts, ps) <- option ([], []) 
		   (parser `separatedBy` sep)
       c <- cl
       return (k ts (map tokPos (o:ps++[c])))

brackets parser k = bracketParser parser oBracketT cBracketT commaT k

-- ----------------------------------------------
-- mixfix and compound ids
-- ----------------------------------------------

-- a compound list
comps :: GenParser Char st ([Id], [Pos])
comps = brackets uninstOpName (,) 
	<?> "[<id>,...,<id>]"

-- a compound list does not follow a place
-- but after a compound list further places may follow
mixId :: [String] -> GenParser Char st Id
mixId keys = do { l <- start keys
		; if isPlace (last l) then return (Id l [] [])
		  else (do { (c, p) <- option ([], []) comps
			   ; u <- many placeT
			   ; return (Id (l++u) c p)
			   })
		}

uninstOpName = mixId hascasl_reserved_ops
typeName = mixId (hascasl_type_ops ++ hascasl_reserved_ops)

-- ----------------------------------------------
-- TYPE-VAR Ids
-- ----------------------------------------------
-- no compound ids (just a word) 
typeVar :: GenParser Char st Token
typeVar = pToken scanWords

className = typeVar