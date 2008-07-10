{- |
Module      :  $Header$
Description :  Parser for symbols in translations and reductions
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parsing symbols for translations and reductions
-}

module CASL.SymbolParser where

import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Text.ParserCombinators.Parsec
import Common.Token
import CASL.Formula

-- | parsing a possibly qualified identifier
symb :: [String] -> GenParser Char st SYMB
symb ks =
    do i <- parseId ks
       do    c <- colonST
             t <- opOrPredType ks
             return (Qual_id i t $ tokPos c)
         <|> return (Symb_id i)

-- | parsing a type for an operation or a predicate
opOrPredType :: [String] -> GenParser Char st TYPE
opOrPredType ks =
    do (b, s, p) <- opSort ks
       if b then return (O_type (Op_type Partial [] s p))
         else do c <- crossT
                 (ts, ps) <- sortId ks `separatedBy` crossT
                 fmap O_type (opFunSort ks (s:ts) (c:ps))
                   <|> return (P_type $ Pred_type (s:ts)
                                      $ catRange $ c:ps)
             <|> fmap O_type (opFunSort ks [s] [])
             <|> return (A_type s)
    <|> fmap P_type predUnitType

-- | parsing one symbol or a mapping of one to second symbol
symbMap :: [String] -> GenParser Char st SYMB_OR_MAP
symbMap ks =
    do s <- symb ks
       do    f <- pToken $ toKey mapsTo
             t <- symb ks
             return (Symb_map s t $ tokPos f)
         <|> return (Symb s)

-- | parse a kind keyword
symbKind :: GenParser Char st (SYMB_KIND, Token)
symbKind = try(
        do q <- pluralKeyword opS
           return (Ops_kind, q)
        <|>
        do q <- pluralKeyword predS
           return (Preds_kind, q)
        <|>
        do q <- pluralKeyword sortS
           return (Sorts_kind, q)) <?> "kind"

-- | parse a possible kinded list of comma separated symbols
symbItems :: [String] -> GenParser Char st SYMB_ITEMS
symbItems ks =
    do (is, ps) <- symbs ks
       return (Symb_items Implicit is $ catRange ps)
    <|>
    do (k, p) <- symbKind
       (is, ps) <- symbs ks
       return (Symb_items k is $ catRange $ p:ps)

-- | parse a comma separated list of symbols
symbs :: [String] -> GenParser Char st ([SYMB], [Token])
symbs ks =
    do s <- symb ks
       do   c <- commaT `followedWith` symb ks
            (is, ps) <- symbs ks
            return (s:is, c:ps)
         <|> return ([s], [])

-- | parse a possible kinded list of symbol mappings
symbMapItems :: [String] -> GenParser Char st SYMB_MAP_ITEMS
symbMapItems ks =
    do s <- symbMap ks
       return (Symb_map_items Implicit [s] nullRange)
    <|>
    do (k, p) <- symbKind
       (is, ps) <- symbMaps ks
       return (Symb_map_items k is $ catRange $ p:ps)

-- | parse a comma separated list of symbol mappings
symbMaps :: [String] -> GenParser Char st ([SYMB_OR_MAP], [Token])
symbMaps ks =
    do s <- symbMap ks
       do   c <- commaT `followedWith` symb ks
            (is, ps) <- symbMaps ks
            return (s:is, c:ps)
         <|> return ([s], [])
