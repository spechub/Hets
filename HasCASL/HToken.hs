
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
import Token(casl_reserved_ops, casl_reserved_words
	    , formula_words, formula_ops, start, mixId)
import Parsec

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
hascasl_reserved_ops, hascasl_reserved_fops, hascasl_type_ops :: [String]
hascasl_reserved_ops = [dotS++exMark, cDot++exMark, asP, assignS, lamS] 
		       ++ casl_reserved_ops

hascasl_reserved_fops = formula_ops ++ hascasl_reserved_ops

hascasl_type_ops = [funS, pFun, contFun, pContFun, prodS, timesS, quMark, 
		   lessS] 

hascasl_reserved_words, hascasl_reserved_fwords :: [String]
hascasl_reserved_words = 
    [classS, instanceS, programS, caseS, ofS, letS, derivingS] 
			 ++ casl_reserved_words

hascasl_reserved_fwords = formula_words ++ hascasl_reserved_words

scanWords, scanTermWords :: GenParser Char st String
scanWords = reserved hascasl_reserved_fwords scanAnyWords 
scanTermWords = reserved hascasl_reserved_words scanAnyWords

-- ----------------------------------------------
-- non-compound mixfix ids (variables)
-- ----------------------------------------------
var :: GenParser Char st Id
var = fmap (\l -> Id l [] []) (start (hascasl_reserved_fwords,
				      hascasl_reserved_ops))

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

brackets :: GenParser Char st a -> ([a] -> [Pos] -> b) -> GenParser Char st b
brackets parser k = bracketParser parser oBracketT cBracketT commaT k

-- ----------------------------------------------
-- mixIds
-- ----------------------------------------------

-- allow type_ops as op_symbols (like "*")

uninstOpName, typeName :: GenParser Char st Id
uninstOpName = mixId (hascasl_reserved_fops, hascasl_reserved_fwords)
	       (hascasl_reserved_fops, hascasl_reserved_fwords)

-- prohibit type_ops on the top-level
typeName = mixId (hascasl_type_ops ++ hascasl_reserved_fops,
		  hascasl_reserved_fwords)
	   (hascasl_reserved_fops, hascasl_reserved_fwords)

-- ----------------------------------------------
-- TYPE-VAR Ids
-- ----------------------------------------------

-- no compound ids (just a word) 
typeVar :: GenParser Char st Token
typeVar = pToken scanWords

className :: GenParser Char st Id
className = 
    do s <- typeVar
       (c, p) <- option ([], []) $ brackets typeName (,) 
       return (Id [s] c p)
