{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   parse SIG-ITEMS, BASIC-ITEMS, BASIC-SPEC 
-}

{- 
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module CASL.Parse_AS_Basic where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Common.Lib.Parsec
import CASL.Formula
import CASL.SortItem
import CASL.OpItem

-- ------------------------------------------------------------------------
-- sigItems
-- ------------------------------------------------------------------------

sortItems :: AParser SIG_ITEMS
sortItems = itemList sortS sortItem Sort_items

typeItems :: AParser SIG_ITEMS
typeItems = itemList typeS datatype Datatype_items

opItems :: AParser SIG_ITEMS
opItems = itemList opS opItem Op_items

predItems :: AParser SIG_ITEMS
predItems = itemList predS predItem Pred_items

sigItems :: AParser SIG_ITEMS
sigItems = sortItems <|> opItems <|> predItems <|> typeItems

-- ------------------------------------------------------------------------
-- basicItems
-- ------------------------------------------------------------------------

basicItems :: AParser BASIC_ITEMS
basicItems = fmap Sig_items sigItems
	     <|> do f <- asKey freeS
		    Datatype_items ts ps <- typeItems
		    return (Free_datatype ts (tokPos f : ps))
	     <|> do g <- asKey generatedS
		    do t <- typeItems
		       return (Sort_gen [Annoted t [] [] []] [tokPos g])
		      <|> 
		      do o <- oBraceT
			 is <- annosParser sigItems
			 c <- cBraceT
			 return (Sort_gen is
				   (toPos g [o] c)) 
	     <|> do v <- pluralKeyword varS
		    (vs, ps) <- varItems
		    return (Var_items vs (map tokPos (v:ps)))
	     <|> do f <- forallT 
		    (vs, ps) <- varDecl `separatedBy` anSemi 
		    a <- annos
		    Axiom_items ((Annoted ft qs as rs):fs) ds <- dotFormulae
		    let aft = Annoted ft qs (a++as) rs
		        in return (Local_var_axioms vs (aft:fs) 
				   (map tokPos (f:ps) ++ ds))
	     <|> dotFormulae
             <|> do a <- pluralKeyword axiomS
		    (fs, ps, ans) <- itemAux startKeyword (annoParser formula)
		    return (Axiom_items (zipWith 
					 (\ x y -> Annoted (item x) 
					           [] (l_annos x) y) 
					 fs ans) (map tokPos (a:ps)))

varItems :: AParser ([VAR_DECL], [Token])
varItems = do v <- varDecl
	      do s <- try (addAnnos >> Common.Lexer.semiT << addLineAnnos)
		 do tryItemEnd startKeyword
		    return ([v], [s])
	           <|> 
	             do (vs, ts) <- varItems
			return (v:vs, s:ts)
		<|>
		return ([v], [])
             
dotFormulae :: AParser BASIC_ITEMS
dotFormulae = do d <- dotT
		 (fs, ds) <- aFormula `separatedBy` dotT
		 (m, an) <- optSemi
		 let ps = map tokPos (d:ds) 
		     ns = init fs ++ [appendAnno (last fs) an]
		     in case m of 
			Nothing -> return (Axiom_items ns ps)
			Just t -> return (Axiom_items ns
			       (ps ++ [tokPos t]))

aFormula  :: AParser (Annoted FORMULA)
aFormula = bind appendAnno (annoParser formula) lineAnnos

-- ------------------------------------------------------------------------
-- basicSpec
-- ------------------------------------------------------------------------

basicSpec :: AParser BASIC_SPEC
basicSpec = (fmap Basic_spec $ annosParser basicItems)
            <|> (oBraceT >> cBraceT >> return (Basic_spec []))
