module CCToken 

where

import Id (Id(Id), Token(..), Pos, toPos, isPlace)
import Token
import Lexer
import Keywords
import CCKeywords

import Parsec

csp_casl_reserved_words :: [String]
csp_casl_reserved_words = casl_reserved_words ++
                          [dataS, channelS, processS] 

channelName :: GenParser Char st Token
channelName = pToken (reserved csp_casl_reserved_words scanAnyWords)

namedProcess :: GenParser Char st Token
namedProcess = pToken (reserved csp_casl_reserved_words scanAnyWords)