{- |
Module      :  $Header$
Copyright   :  (c)  Daniel Pratsch and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable


parser for CSP-CASL simple ids 

-}


module CspCASL.CCToken 

where

import Common.Id (Token(..))
import Common.Token
import Common.Lexer
import CspCASL.CCKeywords
import Common.AnnoState

csp_casl_reserved_words :: [String]
csp_casl_reserved_words = casl_reserved_words ++
                          [dataS, channelS, processS] ++
                          csp_casl_keywords

channelName, var :: AParser Token                          --, namedProcess 
channelName = pToken (reserved csp_casl_reserved_words scanAnyWords)

var = pToken (reserved csp_casl_reserved_words scanAnyWords)

--namedProcess = pToken (reserved csp_casl_reserved_words scanAnyWords)

--opList = pToken (reserved csp_casl_reserved_words scanAnyWords)
