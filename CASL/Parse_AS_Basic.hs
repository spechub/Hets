{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   parse SIG-ITEMS, BASIC-ITEMS, BASIC-SPEC 
   Follows Sect. II:3.1 of the CASL Reference Manual.
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

sortItems :: (AParsable b, AParsable s, AParsable f) => 
             AParser (SIG_ITEMS b s f)
sortItems = itemList sortS sortItem Sort_items

typeItems :: (AParsable b, AParsable s, AParsable f) => 
             AParser (SIG_ITEMS b s f)
typeItems = itemList typeS datatype Datatype_items

opItems :: (AParsable b, AParsable s, AParsable f) => 
           AParser (SIG_ITEMS b s f)
opItems = itemList opS opItem Op_items

predItems :: (AParsable b, AParsable s, AParsable f) => AParser (SIG_ITEMS b s f)
predItems = itemList predS predItem Pred_items

sigItems :: (AParsable b, AParsable s, AParsable f) => AParser (SIG_ITEMS b s f)
sigItems = sortItems <|> opItems <|> predItems <|> typeItems
           <|> do s <- aparser []
                  return (Ext_SIG_ITEMS s)


---- helpers ----------------------------------------------------------------

datatypeToFreetype :: (AParsable b, AParsable s, AParsable f) =>
                      SIG_ITEMS b s f -> Pos -> BASIC_ITEMS b s f 
datatypeToFreetype d pos =
   case d of
     Datatype_items ts ps -> Free_datatype ts (pos : ps)
     _ -> error "datatypeToFreetype"

axiomToLocalVarAxioms :: (AParsable b, AParsable s, AParsable f) => 
     BASIC_ITEMS b s f -> [Annotation] -> [VAR_DECL] -> [Pos] 
     -> BASIC_ITEMS b s f
axiomToLocalVarAxioms ai a vs posl =
   case ai of
     Axiom_items ((Annoted ft qs as rs):fs) ds ->  
	 let aft = Annoted ft qs (a++as) rs
	     in Local_var_axioms vs (aft:fs) (posl ++ ds)
     _ -> error "axiomToLocalVarAxioms"

-- ------------------------------------------------------------------------
-- basicItems
-- ------------------------------------------------------------------------

basicItems :: (AParsable b, AParsable s, AParsable f) => 
              AParser (BASIC_ITEMS b s f)
basicItems = 
         fmap Sig_items sigItems
	     <|> do f <- asKey freeS
		    ti <- typeItems
		    return (datatypeToFreetype ti (tokPos f))
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
		    ai <- dotFormulae
		    return (axiomToLocalVarAxioms ai a vs (map tokPos (f:ps)))
	     <|> dotFormulae
             <|> do a <- pluralKeyword axiomS
		    (fs, ps, ans) <- itemAux startKeyword (annoParser formula)
		    return (Axiom_items (zipWith 
					 (\ x y -> Annoted (item x) 
					           [] (l_annos x) y) 
					 fs ans) (map tokPos (a:ps)))
             <|> do b <- aparser []
                    return (Ext_BASIC_ITEMS b)

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
             
dotFormulae :: (AParsable b, AParsable s, AParsable f) => AParser (BASIC_ITEMS b s f)
dotFormulae = do d <- dotT
		 (fs, ds) <- aFormula `separatedBy` dotT
		 (m, an) <- optSemi
		 let ps = map tokPos (d:ds) 
		     ns = init fs ++ [appendAnno (last fs) an]
		     in case m of 
			Nothing -> return (Axiom_items ns ps)
			Just t -> return (Axiom_items ns
			       (ps ++ [tokPos t]))

aFormula  :: AParsable f => AParser (Annoted (FORMULA f))
aFormula = bind appendAnno (annoParser formula) lineAnnos

-- ------------------------------------------------------------------------
-- basicSpec
-- ------------------------------------------------------------------------

basicSpec :: (AParsable f, AParsable s, AParsable b) => 
	     AParser (BASIC_SPEC b s f)
basicSpec = (fmap Basic_spec $ annosParser basicItems)
            <|> (oBraceT >> cBraceT >> return (Basic_spec []))
