{- |
Module      :  $Header$
Copyright   :  (c)  Daniel Pratsch and Uni Bremen 2002-2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  M.Roggenbach@swansea.ac.uk
Stability   :  provisional
Portability :  portable


parser for CSP-CASL simple ids 

-}


module CspCASL.CCToken 

where

import Common.Id
import Common.Token
import CspCASL.CCKeywords
import Common.AnnoState

{- csp_casl_reserved_words :: [String]
csp_casl_reserved_words = casl_reserved_words ++
                          csp_casl_keywords
-}

channelName, var :: AParser st Token                          --, namedProcess 
channelName = var
var = varId csp_casl_keywords

--namedProcess = pToken (reserved csp_casl_reserved_words scanAnyWords)

--opList = pToken (reserved csp_casl_reserved_words scanAnyWords)
