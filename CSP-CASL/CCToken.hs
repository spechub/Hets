{- **********************************************************************

   $Source$

   $Date$
   $Revision$
   Author: Daniel Pratsch (Last modification by $Author$)

  ************************************************************************** 
-}

module CCToken 

where
{-import Id (Id(Id), Token(..), Pos, toPos, isPlace)-}
import Id (Token(..))
import Token
import Lexer
import CCKeywords

--import Parsec

import AnnoState

csp_casl_reserved_words :: [String]
csp_casl_reserved_words = casl_reserved_words ++
                          [dataS, channelS, processS] ++
                          csp_casl_keywords

channelName, var :: AParser Token                          --, namedProcess 
channelName = pToken (reserved csp_casl_reserved_words scanAnyWords)

var = pToken (reserved csp_casl_reserved_words scanAnyWords)

--namedProcess = pToken (reserved csp_casl_reserved_words scanAnyWords)

--opList = pToken (reserved csp_casl_reserved_words scanAnyWords)