{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.
-}

module CASL.SimplifySen(simplifySen, rmTypesT, rmTypesF) where

import Common.GlobalAnnotations
import Common.Result
import Common.PrettyPrint
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map
import CASL.Sign
import CASL.AS_Basic_CASL 
import CASL.Overload
import Control.Exception (assert)

{- |
   simplifies formula\/term informations for 'show theory' of HETS-graph representation.
-}
simplifySen :: (PrettyPrint f, Eq f) =>
	       (Min f e) -- ^ extension type analysis
	    -> (Sign f e -> f -> f) -- ^ simplifySen for ExtFORMULA 
	    -> (Sign f e -> f -> f) -- ^ remove type information in ExtFORMULA
	    -> Sign f e -> FORMULA f -> 
	       FORMULA f
simplifySen min_func e_func rmTypE_func sign formula = 
    case formula of
    Quantification q vars f pos -> Quantification q vars (simplifySenCall f) pos 
    Conjunction fs pos -> Conjunction (map simplifySenCall fs) pos 
    Disjunction fs pos -> Disjunction (map simplifySenCall fs) pos
    Implication f1 f2 bool pos -> Implication (simplifySenCall f1) (simplifySenCall f2) bool pos
    Equivalence f1 f2 pos -> Equivalence (simplifySenCall f1) (simplifySenCall f2) pos
    Negation f pos ->  Negation (simplifySenCall f) pos
    True_atom x -> True_atom x
    False_atom x -> False_atom x
    f@(Predication _ _ _) -> anaFormulaCall f
    f@(Definedness _ _ ) -> anaFormulaCall f
    f@(Existl_equation _ _ _) -> anaFormulaCall f
    f@(Strong_equation _ _ _) -> anaFormulaCall f
    f@(Membership _ _ _) -> anaFormulaCall f
    ExtFORMULA f -> ExtFORMULA $ e_func sign f
    f@(Sort_gen_ax _ _) -> f
    f -> error ("Error in simplifySen " ++ show f)
    where
        simplifySenCall = simplifySen min_func e_func rmTypE_func sign
	anaFormulaCall = anaFormula min_func rmTypE_func sign

{- |
   simplifies the TERM such that there are no type-information in it.
-}
rmTypesT :: (PrettyPrint f, Eq f) => 
	    Min f e -- for 'anaFormula' in case of 'Conditional'
	 ->(Sign f e -> f -> f) -- ^ remove type information in ExtFORMULA
	 -> Sign f e -> TERM f -> TERM f
rmTypesT minT rmTypE_func signT termT = 
    case termT of
         Qual_var v _ _ -> Simple_id v
	 Sorted_term (Application (Qual_op_name name typ pos1) terms pos2) sort pos3 ->
	       let -- opmap = opMap signT -- =  Map Id (Set OpType)
		   -- maybeOpset = Map.lookup name opmap
		   terms' = map rmTypesTCall terms
	       in  -- case maybeOpset of
	           -- Just otSet -> Application (Op_name name) terms' pos2
		   -- Nothing -> error "Set of OP_NAME not found."
                   Application (Op_name name) terms' pos2
         Sorted_term t _ _ -> rmTypesTCall t 
	 Cast term sort pos -> Cast (anaTermC term) sort pos
	 Application opSymb@(Op_name _) ts pos -> Application opSymb (map rmTypesTCall ts) pos
	                  -- Application opSymb (map anaTermC terms) pos
	 Application (Qual_op_name oName _ _) ts ps -> Application (Op_name oName) (map rmTypesTCall ts) ps
	 Conditional term1 formula term2 pos -> Conditional (anaTermC term1) (anaFormula minT rmTypE_func signT formula) (anaTermC term2) pos
	 t -> error ("Error in rmTypesT " ++ show t)

   where  rmTypesTCall = rmTypesT minT rmTypE_func signT
	  anaTermC = anaTerm minT rmTypE_func signT
	  checkLeqF ot1 ot2 = or $ map (leqF signT ot1) ot2

{- |
   analyzes the TERM if it is the Minimal Expansions of a TERM
-}
anaTerm :: (PrettyPrint f, Eq f) => Min f e -> (Sign f e ->f -> f) -> Sign f e -> TERM f -> TERM f
anaTerm minA rmtFunc signA term = 
    case maybeResult $ minExpTerm minA emptyGlobalAnnos signA (rtc term) of
         Just _  -> rtc term
	 Nothing -> Sorted_term (rtc term) s p
    where (s, p) = case term of 
		        Sorted_term _ s1 p1 -> (s1, p1)
		        t -> error ("Error in anaTerm " ++ show t)
          rtc = rmTypesT minA rmtFunc signA 

{- |
    simplifies the FORMULA such that there are no type-information in it.
-}
rmTypesF ::(PrettyPrint f, Eq f) => Min f e 
	 -> (Sign f e ->f -> f) -- ^ remove type information in ExtFORMULA
	 -> Sign f e -> FORMULA f -> FORMULA f
rmTypesF minF rmTypesFunc signF form = 
    case form of
         Predication pS@(Pred_name _) tl pos -> Predication pS (map anaTermCall tl) pos 
	 Predication (Qual_pred_name pName _ _) tl pos -> Predication (Pred_name pName) (map anaTermCall tl) pos 
	 Definedness t pos -> Definedness (anaTermCall t) pos                
	 Existl_equation t1 t2 pos -> Existl_equation (anaTermCall t1) (anaTermCall t2) pos  	
	 Strong_equation t1 t2 pos -> Strong_equation (anaTermCall t1) (anaTermCall t2) pos  
	 Membership t sort pos -> Membership (anaTermCall t) sort pos          
	 Quantification q vars formula pos -> Quantification q vars (rmTypesFCall formula) pos 
	 Conjunction formulas pos -> Conjunction (map rmTypesFCall formulas) pos 
	 Disjunction formulas pos -> Disjunction (map rmTypesFCall formulas) pos
	 Implication f1 f2 bool pos -> Implication (rmTypesFCall f1) (rmTypesFCall f2) bool pos
	 Equivalence f1 f2 pos -> Equivalence (rmTypesFCall f1) (rmTypesFCall f2) pos
	 True_atom x  -> True_atom x
	 False_atom x -> False_atom x
	 Negation f pos ->  Negation (rmTypesFCall f) pos
	 f@(Sort_gen_ax _ _) -> f			   
	 -- Mixfix_formula t	->  Mixfix_formula (anaTerm t) 	
	 ExtFORMULA f -> ExtFORMULA $ rmTypesFunc signF f
	 f -> error ("Error in rmTypesF " ++  show f) 
      where rmTypesFCall = rmTypesF minF rmTypesFunc signF 
	    anaTermCall = anaTerm minF rmTypesFunc signF

{- |
    analyzes the Formula if it is the Minimal Expansions of a FORMULA.
-}
anaFormula :: (PrettyPrint f, Eq f) => Min f e -> (Sign f e ->f -> f) -> Sign f e -> FORMULA f -> FORMULA f
anaFormula minF rmTypeE_func sign' form1 = 
    let rmf = rmTypesF minF rmTypeE_func sign' form1 
	atc = anaTerm minF rmTypeE_func sign'
    in  case maybeResult $ minExpFORMULA minF emptyGlobalAnnos sign' rmf of
             Just _ -> rmf
	     Nothing -> case form1 of
			Predication predSymb tl pos -> Predication predSymb (map atc tl) pos  
			Definedness t pos -> Definedness (atc t) pos                
			Existl_equation t1 t2 pos -> Existl_equation (atc t1) (atc t2) pos  	
			Strong_equation t1 t2 pos -> Strong_equation (atc t1) (atc t2) pos  
			Membership t sort pos -> Membership (atc t) sort pos          
			f -> error ("Error in anaFormula " ++ show f)
