
{- HetCATS/CASL/OpItem.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse OP-ITEM and "op/ops OP-ITEM ; ... ; OP-ITEM"

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module OpItem where

import Id
import Keywords
import Lexer
import AS_Basic_CASL
import AS_Annotation
import Anno_Parser
import Maybe
import Parsec
import Token
import Formula
import ItemAux
import List

argDecl = do { (vs, ps) <- varId `separatedBy` commaT
	     ; c <- colonT
	     ; s <- sortId
	     ; return (Arg_decl vs s (map tokPos ps ++[tokPos c]))
	     }

opHead = do { o <- oParenT
	    ; (vs, ps) <- argDecl `separatedBy` semiT
	    ; p <- cParenT
	    ; c <- makeToken (string colonS) 
	    ; let qs = map tokPos (o:ps++[p,c])
	      in do { s <- sortId 
		    ; return (Total_op_head vs s qs)
		    }
	      <|> do { quMarkT
		     ; s <- sortId
		     ; return (Partial_op_head vs s qs)
		     }
	    }
	 <|> do { c <- makeToken (string colonS)
		; let q = [tokPos c]
		  in do { s <- sortId 
			; return (Total_op_head [] s q)
			}
		  <|> do { quMarkT
			 ; s <- sortId
			 ; return (Partial_op_head [] s q)
			 }
		}

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

opItem :: GenParser Char st OP_ITEM 
opItem = do { o <- parseId
	    ; opTypeAndAttr [o] []
	      <|>
	      do { h <- opHead
		 ; e <- equalT
		 ; a <- annotations
		 ; t <- term
		 ; return (Op_defn o h (Annoted t [] a []) [tokPos e])
		 }
	      <|>
	      do { p <- commaT
		 ; (os, ps) <- parseId `separatedBy` commaT
		 ; opTypeAndAttr (o:os) (p:ps)
		 }
	    }

opTypeAndAttr os ps = do { c <- makeToken (string colonS)
			 ; t <- opType
			 ; let qs = map tokPos (ps++[c]) in 
			   do { q <- commaT 
			      ; (as, cs) <- opAttr `separatedBy` commaT
			      ; let ps = sort (map tokPos (map snd as ++ (q:cs)))
				in return (Op_decl os t (map fst as) (qs++ps))
			      }
			   <|> return (Op_decl os t [] qs)
			 }

-- overlap "o:t" DEF-or DECL "o:t=e" or "o:t, assoc"  		

opItems =   do { p <- pluralKeyword opS
	       ; a <- annotations
	       ; (v:vs, ts, b:ans) <- itemAux opItem
	       ; let s = Annoted v [] a b
		     r = zipWith (\ x y -> Annoted x [] [] y) vs ans 
		 in return (Op_items (s:r) (map tokPos (p:ts)))
	       }


