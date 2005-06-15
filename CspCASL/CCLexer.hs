{- |
Module      :  $Header$
Copyright   :  (c)  Daniel Pratsch and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk@tzi.de
Stability   :  provisional
Portability :  portable


Parser for CSP-CASL keywords

-}

module CspCASL.CCLexer where

import CspCASL.CCKeywords
import Common.Id (Token(..))
import Common.AnnoState
import Common.Keywords
 
ccspecT, dataT, endT, channelT, processT, letT, inT, skipT, stopT, 
  ifT, thenT, elseT, whenT, varT, multiPreT, prefixT, oRBracketT, 
  cRBracketT, oSBracketT, cSBracketT, sendT, receiveT, extChoiceT, 
  intChoiceT, synParaT, interParaT, oAlPaT, cAlPaT, oGenPaT, mGenPaT, 
  semicolonT, cGenPaT, hidingT, oRenamingT, cRenamingT, chanRenT 
            :: AParser st Token

ccspecT     = asKey ccspecS
dataT       = asKey dataS
endT        = asKey endS
channelT    = asKey channelS
processT    = asKey processS
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
semicolonT  = anSemi
chanRenT    = asKey chanRenS 
