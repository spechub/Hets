
{- HetCATS/CASL/Parse_AS_Basic.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse DATATYPE-DECL, SIG-ITEMS, BASIC-ITEMS, BASIC-SPEC 

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module Parse_AS_Basic where

import Id
import Keywords
import Lexer
import AS_Basic_CASL
import AS_Annotation
import Maybe
import Parsec
import Token
import Formula
import SortItem
import OpItem

-- ------------------------------------------------------------------------
-- datatypes
-- ------------------------------------------------------------------------

datatype :: GenParser Char st DATATYPE_DECL
datatype = do { s <- sortId
	      ; e <- asKey defnS
	      ;	a <- annos
	      ; (Annoted v _ _ b:as, ps) <- aAlternative 
		`separatedBy` asKey barS
	      ; return (Datatype_decl s (Annoted v [] a b:as) 
			(map tokPos (e:ps)))
	      }

aAlternative :: GenParser Char st (Annoted ALTERNATIVE)
aAlternative = do { a <- alternative
		  ; an <- annos
		  ; return (Annoted a [] [] an)
		  }

alternative :: GenParser Char st ALTERNATIVE
alternative = do { s <- pluralKeyword sortS
		 ; (ts, cs) <- sortId `separatedBy` commaT
		 ; return (Subsorts ts (map tokPos (s:cs)))
		 }
              <|> 
              do { i <- parseId
		 ; do { o <- oParenT
		      ; (cs, ps) <- component `separatedBy` semiT
		      ; c <- cParenT
		      ; let qs = toPos o ps c in
			do { q <- quMarkT
			   ; return (Partial_construct i cs 
				     (qs++[tokPos q]))
			   }
			<|> return (Total_construct i cs qs)
		      }
		   <|> return (Total_construct i [] [])
		 }

isSortId (Id is _ _) = length is == 1 && not (null (tokStr (head is))) 
		       && head (tokStr (head is)) `elem` caslLetters

component :: GenParser Char st COMPONENTS
component = do { (is, cs) <- parseId `separatedBy` commaT
	       ; if length is == 1 && isSortId (head is) then
		 compSort is cs 
		 <|> return (Sort (head is))
		 else compSort is cs
	       }

compSort is cs = do { c <- colonST
		    ; (b, t, _) <- opSort
		    ; let p = map tokPos (cs++[c]) in 
		      return (if b then Partial_select is t p
			      else  Total_select is t p)
		    }

-- ------------------------------------------------------------------------
-- sigItems
-- ------------------------------------------------------------------------

typeItems :: GenParser Char st SIG_ITEMS
typeItems = itemList typeS datatype Datatype_items

sigItems :: GenParser Char st SIG_ITEMS
sigItems = sortItems <|> opItems <|> predItems <|> typeItems

-- ------------------------------------------------------------------------
-- basicItems
-- ------------------------------------------------------------------------

basicItems :: GenParser Char st BASIC_ITEMS
basicItems = fmap Sig_items sigItems
	     <|> do { f <- asKey freeS
		    ; Datatype_items ts ps <- typeItems
		    ; return (Free_datatype ts (tokPos f : ps))
		    }
	     <|> do { g <- asKey generatedS
		    ; do { t <- typeItems
			 ; return (Sort_gen [Annoted t [] [] []] [tokPos g])
			 }
		      <|> 
		      do { o <- oBraceT
			 ; a <- annos
			 ; i:is <- many1 sigItems
			 ; c <- cBraceT
			 ; return (Sort_gen ((Annoted i [] a [])  
					    : map (\x -> Annoted x [] [] []) is)
				   (toPos g [o] c)) 
			 }
		    }
	     <|> do { v <- pluralKeyword varS
		    ; (vs, ps) <- varItems
		    ; return (Var_items vs (map tokPos (v:ps)))
		    }
	     <|> do { f <- asKey forallS 
		    ; (vs, ps) <- varDecl `separatedBy` semiT 
		    ; Axiom_items fs ds <- dotFormulae
		    ; return (Local_var_axioms vs fs (map tokPos (f:ps) ++ ds))
		    }
	     <|> dotFormulae
             <|> do { a <- pluralKeyword axiomS
		    ; (fs, ps, ans) <- itemAux formula
		    ; return (Axiom_items (zipWith 
					   (\ x y -> Annoted x [] [] y) 
					   fs ans) (map tokPos (a:ps)))
		    }

varItems :: GenParser Char st ([VAR_DECL], [Token])
varItems = do { v <- varDecl
	      ; do { s <- semiT
		   ; do { tryItemEnd startKeyword
			; return ([v], [s])
			}
	             <|> 
	             do { (vs, ts) <- varItems
			; return (v:vs, s:ts)
			}
		   }
		<|>
		return ([v], [])
	      }
             
dotFormulae :: GenParser Char st BASIC_ITEMS
dotFormulae = do { d <- dotT
		 ; (fs, ds) <- aFormula `separatedBy` dotT
		 ; let ps = map tokPos (d:ds) in 
		   if null (r_annos(last fs)) then  
		   do { (m, an) <- optSemi
		      ; case m of 
			{ Nothing -> return (Axiom_items fs ps)
			; Just t -> return (Axiom_items 
			       (init fs ++ [appendAnno (last fs) an])
			       (ps ++ [tokPos t]))
			}
		      }
		   else return (Axiom_items fs ps)
		 }

aFormula :: GenParser Char st (Annoted FORMULA)
aFormula = bind appendAnno (annoParser formula) lineAnnos

-- ------------------------------------------------------------------------
-- basicSpec
-- ------------------------------------------------------------------------

basicSpec :: GenParser Char st BASIC_SPEC
basicSpec = (oBraceT >> cBraceT >> return (Basic_spec []))
	    <|> 
	    fmap Basic_spec (many1 aBasicItems)

aBasicItems :: GenParser Char st (Annoted BASIC_ITEMS)
aBasicItems = bind (\ x y -> Annoted y [] x []) annos basicItems