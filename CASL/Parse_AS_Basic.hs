
{- HetCATS/CASL/Parse_AS_Basic.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse SIG-ITEMS, BASIC-ITEMS, BASIC-SPEC 

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
import TypeItem
import ItemList

-- ------------------------------------------------------------------------
-- sigItems
-- ------------------------------------------------------------------------

sigItems :: GenParser Char st SIG_ITEMS
sigItems = sortItems <|> opItems <|> predItems <|> typeItems

-- ------------------------------------------------------------------------
-- basicItems
-- ------------------------------------------------------------------------

basicItems :: GenParser Char st BASIC_ITEMS
basicItems = fmap Sig_items sigItems
	     <|> do f <- asKey freeS
		    Datatype_items ts ps <- typeItems
		    return (Free_datatype ts (tokPos f : ps))
	     <|> do g <- asKey generatedS
		    do t <- typeItems
		       return (Sort_gen [Annoted t [] [] []] [tokPos g])
		      <|> 
		      do o <- oBraceT
			 a <- annos
			 is <- annosParser sigItems
			 c <- cBraceT
			 return (Sort_gen is
				   (toPos g [o] c)) 
	     <|> do v <- pluralKeyword varS
		    (vs, ps) <- varItems
		    return (Var_items vs (map tokPos (v:ps)))
	     <|> do f <- forallT 
		    (vs, ps) <- varDecl `separatedBy` semiT 
		    a <- annos
		    Axiom_items ((Annoted ft qs as rs):fs) ds <- dotFormulae
		    let aft = Annoted ft qs (a++as) rs
		        in return (Local_var_axioms vs (aft:fs) 
				   (map tokPos (f:ps) ++ ds))
	     <|> dotFormulae
             <|> do a <- pluralKeyword axiomS
		    (fs, ps, ans) <- itemAux startKeyword formula
		    return (Axiom_items (zipWith 
					 (\ x y -> Annoted x [] [] y) 
					 fs ans) (map tokPos (a:ps)))

varItems :: GenParser Char st ([VAR_DECL], [Token])
varItems = do v <- varDecl
	      do s <- semiT
		 do tryItemEnd startKeyword
		    return ([v], [s])
	           <|> 
	             do (vs, ts) <- varItems
			return (v:vs, s:ts)
		<|>
		return ([v], [])
             
dotFormulae :: GenParser Char st BASIC_ITEMS
dotFormulae = do d <- dotT
		 (fs, ds) <- aFormula `separatedBy` dotT
		 (m, an) <- optSemi
		 let ps = map tokPos (d:ds) 
		     ns = init fs ++ [appendAnno (last fs) an]
		     in case m of 
			Nothing -> return (Axiom_items ns ps)
			Just t -> return (Axiom_items ns
			       (ps ++ [tokPos t]))
    where aFormula = bind appendAnno (annoParser formula) lineAnnos


-- ------------------------------------------------------------------------
-- basicSpec
-- ------------------------------------------------------------------------

basicSpec :: GenParser Char st BASIC_SPEC
basicSpec = (fmap Basic_spec $ many1 $ 
	    try $ bind addLeftAnno annos basicItems)
            <|> try (oBraceT >> cBraceT >> return (Basic_spec []))

