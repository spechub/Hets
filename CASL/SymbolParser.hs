{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

may be needed for structured specs 
-}

module CASL.SymbolParser where

import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Text.ParserCombinators.Parsec
import Common.Token
import CASL.Formula

-- ------------------------------------------------------------------------
-- symbol
-- ------------------------------------------------------------------------

symb :: [String] -> GenParser Char st SYMB
symb ks = 
    do i <- parseId ks
       do    c <- colonST 
             t <- opOrPredType ks 
             return (Qual_id i t $ tokPos c)
         <|> return (Symb_id i)

opOrPredType :: [String] -> GenParser Char st TYPE
opOrPredType ks = 
    do (b, s, p) <- opSort ks
       if b then return (O_type (Op_type Partial [] s p))
         else do c <- crossT 
                 (ts, ps) <- sortId ks `separatedBy` crossT
                 fmap O_type (opFunSort ks (s:ts) (c:ps))
                   <|> return (P_type $ Pred_type (s:ts) 
                                      $ catPos $ c:ps)
             <|> fmap O_type (opFunSort ks [s] [])
             <|> return (A_type s)
    <|> fmap P_type predUnitType

-- ------------------------------------------------------------------------
-- symbol or map, symbKind 
-- ------------------------------------------------------------------------

symbMap :: [String] -> GenParser Char st SYMB_OR_MAP
symbMap ks = 
    do s <- symb ks
       do    f <- pToken $ toKey mapsTo
             t <- symb ks
             return (Symb_map s t $ tokPos f)
         <|> return (Symb s)

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

-- ------------------------------------------------------------------------
-- symb-items
-- ------------------------------------------------------------------------

symbItemsList :: [String] -> GenParser Char st SYMB_ITEMS_LIST
symbItemsList ks = 
    do (is, ps) <- symbItems ks `separatedBy` commaT
       return (Symb_items_list is $ catPos ps)

symbItems :: [String] -> GenParser Char st SYMB_ITEMS
symbItems ks = 
    do (is, ps) <- symbs ks
       return (Symb_items Implicit is $ catPos ps)
    <|> 
    do (k, p) <- symbKind
       (is, ps) <- symbs ks
       return (Symb_items k is $ catPos $ p:ps)

symbs :: [String] -> GenParser Char st ([SYMB], [Token])
symbs ks = 
    do s <- symb ks
       do   c <- commaT `followedWith` symb ks
            (is, ps) <- symbs ks
            return (s:is, c:ps)
         <|> return ([s], [])

-- ------------------------------------------------------------------------
-- symb-map-items
-- ------------------------------------------------------------------------

symbMapItemsList :: [String] -> GenParser Char st SYMB_MAP_ITEMS_LIST
symbMapItemsList ks = 
    do (is, ps) <- symbMapItems ks `separatedBy` commaT
       return (Symb_map_items_list is $ catPos ps)

symbMapItems :: [String] -> GenParser Char st SYMB_MAP_ITEMS
symbMapItems ks = 
    do s <- symbMap ks
       return (Symb_map_items Implicit [s] nullRange)
    <|> 
    do (k, p) <- symbKind
       (is, ps) <- symbMaps ks
       return (Symb_map_items k is $ catPos $ p:ps)

symbMaps :: [String] -> GenParser Char st ([SYMB_OR_MAP], [Token])
symbMaps ks = 
    do s <- symbMap ks
       do   c <- commaT `followedWith` symb ks
            (is, ps) <- symbMaps ks
            return (s:is, c:ps)
         <|> return ([s], [])
