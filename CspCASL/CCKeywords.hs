{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}

module CspCASL.CCKeywords where

import Prelude(String)

----------------------------------------------------------------------------
-- csp-casl keywords
----------------------------------------------------------------------------

ccspecS, dataS, channelS, processS, endS, equalS, letS, inS, semicolonS, 
  commaS, colonS, skipS, stopS, ifS, thenS, elseS, whenS, varS, oRBracketS, 
  cRBracketS, oSBracketS, cSBracketS, multiPreS, extChoiceS, intChoiceS, 
  oAlPaS, cAlPaS, oGenPaS, mGenPaS, cGenPaS, synParaS, interParaS, hidingS,
  oRenamingS, cRenamingS, prefixS, sendS, receiveS , chanRenS :: String

ccspecS    = "ccspec"
dataS      = "data"
channelS   = "channel"
processS   = "process"
endS       = "end"
equalS     = "="
letS       = "let"
inS        = "in"
semicolonS = ";"
commaS     = ","
colonS     = ":"
skipS      = "skip"
stopS      = "stop"
ifS        = "if"
thenS      = "then"
elseS      = "else"
whenS      = "when"
varS       = "var"
oRBracketS = "("
cRBracketS = ")"
oSBracketS = "["
cSBracketS = "]"
multiPreS  = "[]" 
extChoiceS = "[]"
intChoiceS = "|~|"
oAlPaS     = "[|"
cAlPaS     = "|]"
oGenPaS    = "["
mGenPaS    = "||"
cGenPaS    = "]"
synParaS   = "||"
interParaS = "|||"
hidingS    = "\\"
oRenamingS = "[["
cRenamingS = "]]"
prefixS    = "->"
sendS      = "!"
receiveS   = "?"
chanRenS   = "<-"

csp_casl_keywords :: [String]
csp_casl_keywords = [ccspecS, dataS, channelS, processS, endS, equalS, letS, 
                     inS, semicolonS, commaS, colonS, skipS, stopS, ifS, 
                     thenS, elseS, whenS, varS, oRBracketS, cRBracketS, 
                     oSBracketS, cSBracketS, multiPreS, extChoiceS, 
                     intChoiceS, oAlPaS, cAlPaS, oGenPaS, mGenPaS, cGenPaS,
                     synParaS, interParaS, hidingS, oRenamingS, cRenamingS,
                     prefixS, sendS, receiveS, chanRenS]
