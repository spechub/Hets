{- |
Module      :  $Header$
Description :  converting (ie. kif) strings to CASL identifiers
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

converting (ie. kif) strings to CASL identifiers
-}

module Common.ToId where

import Common.Id
import Common.Lexer
import Common.Parsec
import Common.ProofUtils
import Common.Token

import qualified Data.Map as Map
import Text.ParserCombinators.Parsec

-- | convert a string to a legal simple CASL identifier
toSimpleId :: String -> Token
toSimpleId s = mkSimpleId $
    case parse (reserved (casl_reserved_words
                          ++ formula_words) scanAnyWords >> eof)
             "Common.ToId" s of
    Left _ -> 'a' : concatMap ( \ c -> '_' : Map.findWithDefault [c] c
                              (Map.insert '_' "U" charMap)) s
    Right _ -> s

-- | convert a string to a legal CASL identifier
toId :: String -> Id
toId = simpleIdToId . toSimpleId
