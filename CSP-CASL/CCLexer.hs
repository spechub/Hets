{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}

module CCLexer where

import CCKeywords

-- import Parsec
import Id (Token(..))

-- import Lexer

import ItemList (asKey)
import AnnoState

----------------------------------------------------------------------------
-- Parser for csp-casl-keywords
----------------------------------------------------------------------------
 
ccspecT, dataT, endT, channelT, processT, equalT, letT, inT, skipT, stopT, 
  ifT, thenT, elseT, whenT, varT, multiPreT, prefixT, oRBracketT, 
  cRBracketT, oSBracketT, cSBracketT, sendT, receiveT, extChoiceT, commaT, 
  intChoiceT, synParaT, interParaT, oAlPaT, cAlPaT, oGenPaT, mGenPaT, 
  semicolonT, cGenPaT, hidingT, oRenamingT, cRenamingT, colonT, chanRenT 
            :: AParser Token

ccspecT     = asKey ccspecS
dataT       = asKey dataS
endT        = asKey endS
channelT    = asKey channelS
processT    = asKey processS
equalT      = asKey equalS
letT        = asKey letS 
inT         = asKey inS  
skipT       = asKey skipS
stopT       = asKey stopS
ifT         = asKey ifS
thenT       = asKey thenS
elseT       = asKey elseS
whenT       = asKey whenS
varT        = asKey varS
prefixT     = asKey prefixS
multiPreT   = asKey multiPreS
oRBracketT  = asKey oRBracketS
cRBracketT  = asKey cRBracketS
oSBracketT  = asKey oSBracketS
cSBracketT  = asKey cSBracketS
extChoiceT  = asKey extChoiceS
intChoiceT  = asKey intChoiceS
synParaT    = asKey synParaS
interParaT  = asKey interParaS
oAlPaT      = asKey oAlPaS
cAlPaT      = asKey cAlPaS
oGenPaT     = asKey oGenPaS
mGenPaT     = asKey mGenPaS
cGenPaT     = asKey cGenPaS
hidingT     = asKey hidingS
oRenamingT  = asKey oRenamingS 
cRenamingT  = asKey cRenamingS
sendT       = asKey sendS
receiveT    = asKey receiveS
commaT      = asKey commaS
colonT      = asKey colonS
semicolonT  = asKey semicolonS
chanRenT    = asKey chanRenS 