
{- HetCATS/HasCASL/HToken.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL IDs
   adapted from HetCATS/CASL/Token.hs, v 1.9
-}

module HasCASL.HToken where

import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token(casl_reserved_ops, casl_reserved_words
	    , start, comps, mixId)
import Common.Lib.Parsec

-- ----------------------------------------------
-- further hascasl keyword
-- ----------------------------------------------

assignS, minusS, plusS, pFun, contFun, pContFun, lamS, asP :: String
assignS = ":="
minusS = "-"
plusS = "+"
pFun = funS ++ quMark
contFun = minusS ++ funS
pContFun = minusS ++ pFun
lamS = "\\"
asP = "@"

classS, programS, instanceS, caseS, ofS, letS, derivingS :: String
classS = "class"
programS = "program"
instanceS = "instance"
caseS = "case"
ofS = "of"
letS = "let"
derivingS = "deriving"

-- ----------------------------------------------
-- hascasl keyword handling
-- ----------------------------------------------
hascasl_reserved_ops, hascasl_type_ops :: [String]
hascasl_reserved_ops = [dotS++exMark, cDot++exMark, asP, assignS, lamS] 
		       ++ casl_reserved_ops

hascasl_type_ops = [funS, pFun, contFun, pContFun, prodS, timesS, quMark] 

hascasl_reserved_words :: [String]
hascasl_reserved_words = 
    [classS, instanceS, programS, caseS, ofS, letS, derivingS] 
			 ++ casl_reserved_words

scanWords, scanSigns :: GenParser Char st String
scanWords = reserved hascasl_reserved_words scanAnyWords 
scanSigns = reserved hascasl_reserved_ops scanAnySigns 

-- ----------------------------------------------
-- non-compound mixfix ids (variables)
-- ----------------------------------------------

restrictedVar :: [String] -> GenParser Char st Id
restrictedVar ops = fmap (\l -> Id l [] []) 
				 (start (ops ++ hascasl_reserved_ops, 
					 hascasl_reserved_words))
var :: GenParser Char st Id
var = restrictedVar []

-- ----------------------------------------------
-- bracketed lists
-- ----------------------------------------------

bracketParser :: GenParser Char st a -> GenParser Char st Token 
	 -> GenParser Char st Token -> GenParser Char st Token
	 -> ([a] -> [Pos] -> b) -> GenParser Char st b

bracketParser parser op cl sep k = 
    do o <- op
       (ts, ps) <- option ([], []) 
		   (parser `separatedBy` sep)
       c <- cl
       return (k ts (toPos o ps c))

mkBrackets :: GenParser Char st a -> ([a] -> [Pos] -> b) -> GenParser Char st b
mkBrackets parser k = bracketParser parser oBracketT cBracketT commaT k

-- ----------------------------------------------
-- mixIds
-- ----------------------------------------------

hcKeys :: ([String], [String])
hcKeys = (hascasl_reserved_ops, hascasl_reserved_words)

uninstOpId, hconsId, typeId :: GenParser Char st Id
uninstOpId = mixId hcKeys hcKeys
hconsId = mixId (barS:hascasl_reserved_ops, hascasl_reserved_words) 
	  hcKeys

typeId = mixId (quMark:lessS:equalS:barS:hascasl_reserved_ops, 
		hascasl_reserved_words) hcKeys

-- ----------------------------------------------
-- TYPE-VAR Ids
-- ----------------------------------------------

-- no compound ids 
typeVar :: GenParser Char st Id
typeVar = restrictedVar [lessS]

-- simple id with compound list
classId :: GenParser Char st Id
classId = 
    do s <- pToken scanWords
       (c, p) <- option ([], []) $ comps hcKeys 
       return (Id [s] c p)
