
{- HetCATS/CASL/OpItem.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse OP-ITEM and "op/ops OP-ITEM ; ... ; OP-ITEM"
   parse PRED-ITEM and "op/ops PRED-ITEM ; ... ; PRED-ITEM"

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module OpItem where

import AnnoState
import Id
import Keywords
import Lexer
import AS_Basic_CASL
import AS_Annotation
import Common.Lib.Parsec
import Token
import Formula
import ItemList
import Data.List

-- stupid cast
argDecl :: AParser ARG_DECL
argDecl = fmap (\(Var_decl vs s ps) -> Arg_decl vs s ps) varDecl

-- non-empty
predHead :: AParser PRED_HEAD
predHead = do o <- oParenT
	      (vs, ps) <- argDecl `separatedBy` anSemi
	      p <- cParenT
	      return (Pred_head vs (map tokPos (o:ps++[p])))

opHead :: AParser OP_HEAD
opHead = do Pred_head vs ps <- predHead
	    c <- colonST
	    (b, s, _) <- opSort
	    let qs = ps ++ [tokPos c] in 
	      return (if b then Partial_op_head vs s qs
	              else Total_op_head vs s qs)

opAttr :: AParser (OP_ATTR, Token)
opAttr =    do p <- asKey assocS
	       return (Assoc_op_attr, p)
	    <|> 
	    do p <- asKey commS
	       return (Comm_op_attr, p)
	    <|> 
	    do p <- asKey idemS
	       return (Idem_op_attr, p)
	    <|> 
	    do p <- asKey unitS
	       t <- term
	       return (Unit_op_attr t, p)

isConstant :: OP_TYPE -> Bool
isConstant(Total_op_type [] _ _) = True
isConstant(Partial_op_type [] _ _) = True
isConstant _ = False

toHead :: Pos -> OP_TYPE -> OP_HEAD
toHead c (Total_op_type [] s _) = Total_op_head [] s [c] 
toHead c (Partial_op_type [] s _) = Partial_op_head [] s [c] 
toHead _ _ = error "toHead got non-empty argument type"

opItem :: AParser OP_ITEM 
opItem = do (os, cs)  <- parseId `separatedBy` anComma
	    if length os == 1 then 
	      do c <- colonST
		 t <- opType
		 if isConstant t then 
		   opBody (head os) (toHead (tokPos c) t)
		   <|> opAttrs os t [c]  -- this always succeeds
		   else opAttrs os t [c]
	      <|>
	      do h <- opHead
		 opBody (head os) h
	      else
	      do c <- colonST
		 t <- opType
		 opAttrs os t (cs++[c])

opBody :: OP_NAME -> OP_HEAD -> AParser OP_ITEM
opBody o h = do e <- equalT
		a <- annos
		t <- term
		return (Op_defn o h (Annoted t [] a []) [tokPos e])
	  
opAttrs :: [OP_NAME] -> OP_TYPE -> [Token] -> AParser OP_ITEM
opAttrs os t c = do q <- anComma 
		    (as, cs) <- opAttr `separatedBy` anComma
		    let ps = sort (map tokPos (c ++ map snd as ++ (q:cs)))
		      in return (Op_decl os t (map fst as) ps)
                 <|> return (Op_decl os t [] (map tokPos c)) 

-- overlap "o:t" DEF-or DECL "o:t=e" or "o:t, assoc"  		
opItems :: AParser SIG_ITEMS
opItems = itemList opS opItem Op_items

-- ----------------------------------------------------------------------
-- predicates
-- ----------------------------------------------------------------------

predItem :: AParser PRED_ITEM 
predItem = do (ps, cs)  <- parseId `separatedBy` anComma
	      if length ps == 1 then
		predBody (head ps) (Pred_head [] [])
		<|> 
		do h <- predHead
		   predBody (head ps) h
		<|> 
		predTypeCont ps cs
		else predTypeCont ps cs
		
predBody :: PRED_NAME -> PRED_HEAD -> AParser PRED_ITEM	
predBody p h = do e <- asKey equivS
		  a <- annos
		  f <- formula
		  return (Pred_defn p h (Annoted f [] a []) [tokPos e])

predTypeCont :: [PRED_NAME] -> [Token] -> AParser PRED_ITEM	
predTypeCont ps cs = do c <- colonT
			t <- predType
			return (Pred_decl ps t (map tokPos (cs++[c])))

predItems :: AParser SIG_ITEMS
predItems = itemList predS predItem Pred_items
