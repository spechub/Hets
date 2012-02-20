{- |
Module      :  $Header$
Description :  Parser of common logic symbols
Copyright   :  (c) Karl Luc, DFKI Bremen 2010, Eugen Kuksa and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic symbols
-}

module CommonLogic.Parse_Symbols
  ( intNameOrSeqMark
  , symbItems
  , symbMapItems
  ) where

import CommonLogic.AS_CommonLogic
import Common.Id as Id
import Common.Lexer as Lexer
import Common.Keywords as Keywords

import CommonLogic.Lexer_CLIF

import Text.ParserCombinators.Parsec as Parsec

intNameOrSeqMark :: CharParser st NAME_OR_SEQMARK
intNameOrSeqMark = do
    s <- seqmark -- fix seqmark parser for one
    return $ SeqMark s
  <|> do
    n <- identifier
    return $ Name n

-- | Parse a list of comma separated symbols.
symbItems :: GenParser Char st SYMB_ITEMS
symbItems = do
  (is, ps) <- symbs
  return (Symb_items is $ catRange ps)

-- | parse a comma separated list of symbols
symbs :: GenParser Char st ([NAME_OR_SEQMARK], [Token])
symbs = do
       s <- intNameOrSeqMark
       do   c <- commaT `followedWith` intNameOrSeqMark
            (is, ps) <- symbs
            return (s:is, c:ps)
         <|> return ([s], [])

-- | parse a list of symbol mappings
symbMapItems :: GenParser Char st SYMB_MAP_ITEMS
symbMapItems = do
  (is, ps) <- symbMaps
  return (Symb_map_items is $ catRange ps)

-- | parse a comma separated list of symbol mappings
symbMaps :: GenParser Char st ([SYMB_OR_MAP], [Token])
symbMaps = do
  s <- symbMap
  many white
  do  c <- commaT `followedWith` intNameOrSeqMark
      (is, ps) <- symbMaps
      return (s:is, c:ps)
    <|> return ([s], [])

-- | parsing one symbol or a mapping of one to a second symbol
symbMap :: GenParser Char st SYMB_OR_MAP
symbMap = do
    seqMarkMap <- symbMapS
    return seqMarkMap
  <|> do
    nameMap <- symbMapN
    return nameMap

symbMapS :: GenParser Char st SYMB_OR_MAP
symbMapS = do
  s <- seqmark
  do  many white
      f <- pToken $ toKey mapsTo
      t <- seqmark
      return (Symb_mapS s t $ tokPos f)
    <|> return (Symb $ SeqMark s)

symbMapN :: GenParser Char st SYMB_OR_MAP
symbMapN = do
  s <- identifier
  do  many white
      f <- pToken $ toKey mapsTo
      t <- identifier
      return (Symb_mapN s t $ tokPos f)
    <|> return (Symb $ Name s)
