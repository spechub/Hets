{- |
Module      :  $Header$
Description :  parsers for HasCASL tokens
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

parser for HasCASL IDs extending "Common.Keywords" and "Common.Token"
-}

module HasCASL.HToken where

import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import Text.ParserCombinators.Parsec

-- * HasCASL keyword handling

-- | HasCASL's reserved symbols in lambda terms and patterns
hascasl_reserved_ops :: [String]
hascasl_reserved_ops =
    [dotS ++ exMark, cDot ++ exMark, asP, lamS] ++ casl_reserved_ops

-- | HasCASL's reserved symbols in function types
hascasl_type_ops :: [String]
hascasl_type_ops = [funS, pFun, contFun, pContFun, prodS, timesS, quMark]

-- | HasCASL's reserved words
hascasl_reserved_words :: [String]
hascasl_reserved_words =
    [asS, inS, functS, functS ++ sS, classS, classS ++ "es", instanceS,
     instanceS ++ sS, programS, programS ++ sS, caseS, ofS, letS,
     derivingS, internalS, whereS] ++ casl_reserved_words

-- | HasCASL's identifier words ('scanAnyWords')
scanHCWords :: GenParser Char st String
scanHCWords = reserved hascasl_reserved_words scanAnyWords

-- | HasCASL's identifier signs ('scanAnySigns')
scanHCSigns :: GenParser Char st String
scanHCSigns = reserved hascasl_reserved_ops scanAnySigns

-- * HasCASL 'Id' parsers

-- | non-type variables ('lessS' additionally excluded)
var :: GenParser Char st Id
var = fmap mkId (start (lessS : hascasl_reserved_ops, hascasl_reserved_words))

-- | the HasCASL keys for 'mixId'
hcKeys :: ([String], [String])
hcKeys = (hascasl_reserved_ops, hascasl_reserved_words)

-- | if-then-tokens
ifThen :: GenParser Char st [Token]
ifThen = do
    i <- pToken $ keyWord $ string ifS
    p <- placeT
    t <- pToken $ keyWord $ string thenS
    q <- placeT
    return [i, p , t, q]

-- | if-then-else-identifier
ite :: GenParser Char st Id
ite = do
    ts <- try ifThen
    do  e <- pToken $ keyWord $ string elseS
        p <- placeT
        return (mkId (ts ++ [e, p]))
      <|> return (mkId ts)

-- | operation 'Id' (reserved stuff excluded)
opId :: GenParser Char st Id
opId = (try ite <|> mixId hcKeys hcKeys) <?> "id"

-- | constructor 'Id' ('barS' additionally excluded)
hconsId :: GenParser Char st Id
hconsId = mixId (barS:hascasl_reserved_ops, hascasl_reserved_words) hcKeys

-- | simple 'Id' without compound list (only a words)
typeVar :: GenParser Char st Id
typeVar = fmap (mkId . (: [])) $ pToken scanHCWords

-- | simple 'Id' possibly with compound list
classId :: GenParser Char st Id
classId = do
    s <- pToken scanHCWords
    (c, p) <- option ([], nullRange) $ comps hcKeys
    return $ Id [s] c p
