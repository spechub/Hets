{- |
Module      :  $Header$
Copyright   :  (c)  Daniel Pratsch and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
  

CSP-CASL keywords 

-}

module CspCASL.CCKeywords where

ccspecS, dataS, channelS, processS, letS, skipS, stopS, intChoiceS, synParaS
  , interParaS, hidingS, prefixS, sendS, receiveS, chanRenS :: String

oRBracketS, cRBracketS, oSBracketS, cSBracketS, multiPreS, extChoiceS
  , oRenamingS, cRenamingS, oAlPaS, cAlPaS, oGenPaS, mGenPaS, cGenPaS :: String


ccspecS    = "ccspec"
dataS      = "data"
channelS   = "channel"
processS   = "process"
letS       = "let"
skipS      = "skip"
stopS      = "stop"

-- "[" is a separator and cannot be excluded from identifiers
oRBracketS = "("
cRBracketS = ")"
oSBracketS = "["
cSBracketS = "]"
multiPreS  = "[]" 
extChoiceS = "[]"
oAlPaS     = "[|"
cAlPaS     = "|]"
oGenPaS    = "["
mGenPaS    = "||"
cGenPaS    = "]"
oRenamingS = "[["
cRenamingS = "]]"

synParaS   = "||"
intChoiceS = "|~|"
interParaS = "|||"
hidingS    = "\\"
prefixS    = "->"
sendS      = "!"
receiveS   = "?"
chanRenS   = "<-"

csp_casl_keywords :: [String]
csp_casl_keywords = 
 [ccspecS, dataS, channelS, processS, letS, skipS, stopS, intChoiceS, synParaS
	   , interParaS, hidingS, prefixS, sendS, receiveS, chanRenS]
