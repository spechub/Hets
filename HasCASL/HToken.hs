
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


-- * further HasCASL key signs

assignS, minusS, plusS, pFun, contFun, pContFun, lamS, asP :: String
assignS = ":="
minusS = "-"
plusS = "+"
pFun = funS ++ quMark
contFun = minusS ++ funS
pContFun = minusS ++ pFun
lamS = "\\"
asP = "@"

-- * further HasCASL keywords

internalS, classS, programS, instanceS, caseS, ofS, letS, derivingS :: String
classS = "class"
programS = "program"
instanceS = "instance"
caseS = "case"
ofS = "of"
letS = "let"
derivingS = "deriving"
internalS = "internal"

-- | the new keyword fun ('funS' is already defined differently) 
functS :: String
functS = "fun"

-- * HasCASL keyword handling

hascasl_reserved_ops, hascasl_type_ops :: [String]
hascasl_reserved_ops = [dotS++exMark, cDot++exMark, asP, assignS, lamS] 
		       ++ casl_reserved_ops

hascasl_type_ops = [funS, pFun, contFun, pContFun, prodS, timesS, quMark] 

hascasl_reserved_words :: [String]
hascasl_reserved_words = 
    [functS, functS ++ sS, classS, classS ++ "es", instanceS, instanceS ++ sS,
     programS, programS ++ sS, caseS, ofS, letS, derivingS, internalS] 
			 ++ casl_reserved_words

scanWords, scanSigns :: GenParser Char st String
scanWords = reserved hascasl_reserved_words scanAnyWords 
scanSigns = reserved hascasl_reserved_ops scanAnySigns 

-- * HasCASL 'Id' parsers

-- | non-type variables ('lessS' additionally excluded)
var :: GenParser Char st Id
var = fmap (\l -> Id l [] []) (start (lessS : hascasl_reserved_ops, 
				      hascasl_reserved_words))

-- | the HasCASL keys for 'mixId'
hcKeys :: ([String], [String])
hcKeys = (hascasl_reserved_ops, hascasl_reserved_words)

-- | operation 'Id' (reserved stuff excluded)
uninstOpId :: GenParser Char st Id
uninstOpId = mixId hcKeys hcKeys

-- | constructor 'Id' ('barS' additionally excluded)
hconsId :: GenParser Char st Id
hconsId = mixId (barS:hascasl_reserved_ops, hascasl_reserved_words) 
	  hcKeys

-- | mixfix and compound type 'Id' (more signs excluded) 
typeId :: GenParser Char st Id
typeId = mixId (lessS:equalS:barS:hascasl_type_ops++hascasl_reserved_ops, 
		hascasl_reserved_words) hcKeys

-- | simple 'Id' without compound list (only a words)
typeVar :: GenParser Char st Id
typeVar = do s <- pToken scanWords
	     return $ Id [s] [] [] 
	     
-- | simple 'Id' possibly with compound list
classId :: GenParser Char st Id
classId = 
    do s <- pToken scanWords
       (c, p) <- option ([], []) $ comps hcKeys 
       return $ Id [s] c p


