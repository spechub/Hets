
{- HetCATS/CASL/SymbolParser.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   may be needed for structured specs 
-}

module SymbolParser where

import Id
import Keywords
import Lexer
import AS_Basic_CASL
import Parsec
import Token
import Formula

-- ------------------------------------------------------------------------
-- symbol
-- ------------------------------------------------------------------------

symb :: GenParser Char st SYMB
symb = do i <- parseId
	  do c <- colonST 
	     t <- opOrPredType
	     return (Qual_id i t [tokPos c])
	    <|> return (Symb_id i)

opOrPredType :: GenParser Char st TYPE
opOrPredType = 
    do (b, s, p) <- opSort
       if b then return (O_type (Partial_op_type [] s [p]))
	 else do c <- crossT 
		 (ts, ps) <- sortId `separatedBy` crossT
		 fmap O_type (opFunSort (s:ts) (c:ps))
		   <|> return (P_type (Pred_type (s:ts) (map tokPos (c:ps))))
	     <|> fmap O_type (opFunSort [s] [])
	     <|> return (A_type s)
    <|> fmap P_type predUnitType

-- ------------------------------------------------------------------------
-- symbol or map, symbKind 
-- ------------------------------------------------------------------------

symbMap :: GenParser Char st SYMB_OR_MAP
symbMap =   do s <- symb
	       do   f <- asKey mapsTo
		    t <- symb
		    return (Symb_map s t [tokPos f])
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

symbItemsList :: GenParser Char st SYMB_ITEMS_LIST
symbItemsList = do (is, ps) <- symbItems `separatedBy` commaT
		   return (Symb_items_list is (map tokPos ps))

symbItems :: GenParser Char st SYMB_ITEMS
symbItems = do s <- symb
	       return (Symb_items Implicit [s] [])
	    <|> 
	    do (k, p) <- symbKind
               (is, ps) <- symbs
	       return (Symb_items k is (map tokPos (p:ps)))

symbs :: GenParser Char st ([SYMB], [Token])
symbs = do s <- symb 
	   do   c <- commaT `followedWith` symb
	        (is, ps) <- symbs
		return (s:is, c:ps)
	     <|> return ([s], [])

-- ------------------------------------------------------------------------
-- symb-map-items
-- ------------------------------------------------------------------------

symbMapItemsList :: GenParser Char st SYMB_MAP_ITEMS_LIST
symbMapItemsList = do (is, ps) <- symbMapItems `separatedBy` commaT
		      return (Symb_map_items_list is (map tokPos ps))

symbMapItems :: GenParser Char st SYMB_MAP_ITEMS
symbMapItems = 
            do s <- symbMap
	       return (Symb_map_items Implicit [s] [])
	    <|> 
	    do (k, p) <- symbKind
               (is, ps) <- symbMaps
	       return (Symb_map_items k is (map tokPos (p:ps)))

symbMaps :: GenParser Char st ([SYMB_OR_MAP], [Token])
symbMaps = 
        do s <- symbMap 
	   do   c <- commaT `followedWith` symb
	        (is, ps) <- symbMaps
		return (s:is, c:ps)
	     <|> return ([s], [])



    
