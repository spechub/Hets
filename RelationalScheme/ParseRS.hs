{- |
Module      :  $Header$
Description :  abstract syntax for Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser for Relational Schemes
-}

module RelationalScheme.ParseRS where

import Common.AnnoState
import Common.Id
import Common.Lexer
import Common.AS_Annotation
import Control.Monad
import RelationalScheme.Keywords
import RelationalScheme.AS
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error

foldRanges :: [Token] -> Range
foldRanges inR = foldl (\x y -> appRange x $ tokPos y) nullRange inR

-- | parse a simple word not in 'rskeywords'
rsVarId :: [String] -> AParser st Token
rsVarId ks =
     do
        tk <- pToken (reserved (ks++rsKeyWords) (scanAnyWords))
        addAnnos
        return tk

parseRSTable :: AParser st RSTable
parseRSTable = 
    do
        tid <- rsVarId []
        oParenT
        cl <- sepBy1 parseRSColumn commaT
        cParenT
        return $ RSTable (simpleIdToId tid) cl $ tokPos tid

parseRSColumn :: AParser st RSColumn
parseRSColumn = 
    do
        iid <- rsVarId []
        cT <- colonT
        dt <- parseRSDatatypes
        iK <- look4Key
        return $ RSColumn (simpleIdToId iid) dt iK $ foldRanges [iid, cT]

look4Key :: AParser st Bool
look4Key = 
    do 
        asKey rsKey
        return True
    <|>
        return False

testParse ::GenParser tok (AnnoState ()) a
            -> [tok]
            -> Either Text.ParserCombinators.Parsec.Error.ParseError a
testParse par st = runParser par (emptyAnnos ()) "" st

-- boring parser for rel types
parseRSRelTypes :: AParser st RSRelType
parseRSRelTypes =
    do
        asKey rs1to1
        return $ RSone_to_one
    <|>
    do
        asKey rs1tom
        return $ RSone_to_many
    <|>
    do
        asKey rsmto1
        return $ RSmany_to_one
     <|>
    do
        asKey rsmtom
        return $ RSmany_to_many
        
-- boring parser for data-types
parseRSDatatypes :: AParser st RSDatatype
parseRSDatatypes = 
    do
        asKey rsBool
        return $ RSboolean
    <|>
    do
        asKey rsBin
        return $ RSbinary
    <|>
    do
        asKey rsDate
        return $ RSdate
     <|>
    do
        asKey rsDatetime
        return $ RSdatetime      
     <|>
    do
        asKey rsDecimal
        return $ RSdecimal        
     <|>
    do
        asKey rsFloat
        return $ RSfloat      
      <|>
    do
        asKey rsInteger
        return $ RSinteger
     <|>
    do
        asKey rsString
        return $ RSstring    
     <|>
    do
        asKey rsText
        return $ RStext
     <|>
    do
        asKey rsTime
        return $ RStime
      <|>
    do
        asKey rsTimestamp
        return $ RStimestamp
        