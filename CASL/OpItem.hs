{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

{-
   parse OP-ITEM and "op/ops OP-ITEM ; ... ; OP-ITEM"
   parse PRED-ITEM and "op/ops PRED-ITEM ; ... ; PRED-ITEM"

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module CASL.OpItem (opItem, predItem) where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Text.ParserCombinators.Parsec
import Common.Token
import CASL.Formula
import Data.List(sort)

-- stupid cast
argDecl :: [String] -> AParser ARG_DECL
argDecl = fmap (\(Var_decl vs s ps) -> Arg_decl vs s ps) . varDecl

-- non-empty
predHead :: [String] -> AParser PRED_HEAD
predHead ks = 
    do o <- oParenT
       (vs, ps) <- argDecl ks `separatedBy` anSemi
       p <- cParenT
       return $ Pred_head vs $ map tokPos (o:ps++[p])

opHead :: [String] -> AParser OP_HEAD
opHead ks = 
    do Pred_head vs ps <- predHead ks
       c <- colonST
       (b, s, _) <- opSort ks
       let qs = ps ++ [tokPos c]
       return $ if b then Partial_op_head vs s qs
	      else Total_op_head vs s qs

opAttr :: AParsable f => [String] -> AParser (OP_ATTR f, Token)
opAttr ks = do p <- asKey assocS
	       return (Assoc_op_attr, p)
	    <|> 
	    do p <- asKey commS
	       return (Comm_op_attr, p)
	    <|> 
	    do p <- asKey idemS
	       return (Idem_op_attr, p)
	    <|> 
	    do p <- asKey unitS
	       t <- term ks
	       return (Unit_op_attr t, p)

isConstant :: OP_TYPE -> Bool
isConstant(Total_op_type [] _ _) = True
isConstant(Partial_op_type [] _ _) = True
isConstant _ = False

toHead :: Pos -> OP_TYPE -> OP_HEAD
toHead c (Total_op_type [] s _) = Total_op_head [] s [c] 
toHead c (Partial_op_type [] s _) = Partial_op_head [] s [c] 
toHead _ _ = error "toHead got non-empty argument type"

opItem :: AParsable f => [String] -> AParser (OP_ITEM f)
opItem ks = 
    do (os, cs)  <- parseId ks `separatedBy` anComma
       if isSingle os then 
	      do c <- colonST
		 t <- opType ks
		 if isConstant t then 
		   opBody ks (head os) (toHead (tokPos c) t)
		   <|> opAttrs ks os t [c]  -- this always succeeds
		   else opAttrs ks os t [c]
	      <|>
	      do h <- opHead ks
		 opBody ks (head os) h
	      else
	      do c <- colonST
		 t <- opType ks
		 opAttrs ks os t (cs++[c])

opBody :: AParsable f => [String] -> OP_NAME -> OP_HEAD -> AParser (OP_ITEM f)
opBody ks o h = 
    do e <- equalT
       a <- annos
       t <- term ks
       return $ Op_defn o h (Annoted t [] a []) [tokPos e]
	  
opAttrs :: AParsable f => [String] -> [OP_NAME] -> OP_TYPE -> [Token] 
	-> AParser (OP_ITEM f)
opAttrs ks os t c = 
    do q <- anComma 
       (as, cs) <- opAttr ks `separatedBy` anComma
       let ps = sort (map tokPos (c ++ map snd as ++ (q:cs)))
       return (Op_decl os t (map fst as) ps)
   <|> return (Op_decl os t [] (map tokPos c)) 

-- overlap "o:t" DEF-or DECL "o:t=e" or "o:t, assoc"  		

-- ----------------------------------------------------------------------
-- predicates
-- ----------------------------------------------------------------------

predItem :: AParsable f => [String] -> AParser (PRED_ITEM f)
predItem ks = 
    do (ps, cs)  <- parseId ks `separatedBy` anComma
       if isSingle ps then
		predBody ks (head ps) (Pred_head [] [])
		<|> 
		do h <- predHead ks
		   predBody ks (head ps) h
		<|> 
		predTypeCont ks ps cs
		else predTypeCont ks ps cs
		
predBody :: AParsable f => [String] -> PRED_NAME -> PRED_HEAD 
	 -> AParser (PRED_ITEM f)	
predBody ks p h = 
    do e <- asKey equivS
       a <- annos
       f <- formula ks
       return $ Pred_defn p h (Annoted f [] a []) [tokPos e]

predTypeCont :: [String] -> [PRED_NAME] -> [Token] -> AParser (PRED_ITEM f)
predTypeCont ks ps cs = 
    do c <- colonT
       t <- predType ks
       return $ Pred_decl ps t $ map tokPos (cs++[c])
