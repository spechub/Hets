{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}

module CCKeywords where

import Prelude(String)

-- ----------------------------------------------
-- csp-casl keywords
-- ----------------------------------------------

dataS, channelS, processS, endS, semicolonS, commaS,
  colonS, skipS, stopS, ifS, thenS, elseS, whenS, varS,
  oRBracketS, cRBracketS, oSBracketS, cSBracketS, 
  multiPreS, extChoiceS, intChoiceS, oAlPaS, cAlPaS, 
  oGenPaS, mGenPaS, cGenPaS, synParaS, interParaS,
  hidingS, oRenamingS, cRenamingS, prefixS, sendS,
  receiveS , chanRenS   :: String

dataS      = "data"
channelS   = "channel"
processS   = "process"
endS       = "end"
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
csp_casl_keywords = [dataS, channelS, processS, endS, semicolonS, commaS, colonS, skipS, stopS, ifS,
                     thenS, elseS, whenS, varS, oRBracketS, cRBracketS, oSBracketS, cSBracketS, multiPreS, 
                     extChoiceS, intChoiceS, oAlPaS, cAlPaS, oGenPaS, mGenPaS, cGenPaS, synParaS, 
                     interParaS, hidingS, oRenamingS, cRenamingS, multiPreS, sendS, receiveS, prefixS]
