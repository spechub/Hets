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

module CASL.SimplifySen(simplifySen, rmTypesT) where

import Common.GlobalAnnotations
import Common.Id
import Common.Result
import Common.PrettyPrint
import Common.Lib.State
import CASL.Sign
import CASL.AS_Basic_CASL 
import CASL.Overload

{- | simplifies formula\/term informations for 'show theory' of
   HETS-graph representation.  -}
simplifySen :: PrettyPrint f =>
	       (Min f e) -- ^ extension type analysis
	    -> (Sign f e -> f -> f) -- ^ simplifySen for ExtFORMULA 
	    -> Sign f e -> FORMULA f -> FORMULA f
simplifySen minF simpF sign formula = 
    case formula of
    Quantification q vars f pos -> 
            -- add 'vars' to signature
           let (_, sign') = runState (mapM_ addVars vars) sign
           in Quantification q vars (simplifySen minF simpF sign' f) pos 
    Conjunction fs pos -> Conjunction (map simplifySenCall fs) pos 
    Disjunction fs pos -> Disjunction (map simplifySenCall fs) pos
    Implication f1 f2 bool pos -> 
        Implication (simplifySenCall f1) (simplifySenCall f2) bool pos
    Equivalence f1 f2 pos -> 
        Equivalence (simplifySenCall f1) (simplifySenCall f2) pos
    Negation f pos ->  Negation (simplifySenCall f) pos
    True_atom x -> True_atom x
    False_atom x -> False_atom x
    f@(Predication _ _ _) -> anaFormulaCall f
    f@(Definedness _ _ ) -> anaFormulaCall f
    f@(Existl_equation _ _ _) -> anaFormulaCall f
    f@(Strong_equation _ _ _) -> anaFormulaCall f
    f@(Membership _ _ _) -> anaFormulaCall f
    ExtFORMULA f -> ExtFORMULA $ simpF sign f
    f@(Sort_gen_ax _ _) -> f
    f -> error ("Error in simplifySen " ++ show f)
    where
        simplifySenCall = simplifySen minF simpF sign
	anaFormulaCall = anaFormula minF simpF sign

{- |
   simplifies the TERM such that there are no type-information in it.
-}
rmTypesT :: PrettyPrint f => 
            Min f e -- for 'anaFormula' in case of 'Conditional'
	 -> (Sign f e -> f -> f) -- ^ simplifySen for ExtFORMULA
	 -> Sign f e -> TERM f -> TERM f
rmTypesT minF simpF signT termT = 
    case termT of
         Qual_var v _ _ -> Simple_id v
	 Sorted_term (Application (Qual_op_name name _ _) terms pos2) _ _ ->
	       let -- opmap = opMap signT -- =  Map Id (Set OpType)
		   -- maybeOpset = Map.lookup name opmap
		   terms' = map anaTermC terms
	       in  -- case maybeOpset of
	           -- Just otSet -> Application (Op_name name) terms' pos2
		   -- Nothing -> error "Set of OP_NAME not found."
                   Application (Op_name name) terms' pos2
         Sorted_term t _ _ -> anaTermC t 
	 Cast term sort pos -> Cast (anaTermC term) sort pos
	 Application opSymb@(Op_name _) ts pos -> 
             Application opSymb (map anaTermC ts) pos
	                  -- Application opSymb (map anaTermC terms) pos
	 Application (Qual_op_name oName _ _) ts ps -> 
             Application (Op_name oName) (map anaTermC ts) ps
	 Conditional term1 formula term2 pos -> 
             Conditional (anaTermC term1) 
               (simplifySen minF simpF signT formula) 
               (anaTermC term2) pos
	 t -> error ("Error in rmTypesT " ++ show t)

   where anaTermC = anaTerm minF simpF signT

{- |
   analyzes the TERM if it is the Minimal Expansions of a TERM
-}
anaTerm :: PrettyPrint f => Min f e -> (Sign f e -> f -> f) 
        -> Sign f e -> TERM f -> TERM f
anaTerm minF simpF signA term = 
    let s = term_sort term
        ps = case term of 
		        Sorted_term _ _ p -> p
		        Application _ _ p -> p
                        Cast _ _ p -> p
                        Conditional _ _ _ p -> p
                        Simple_id tok -> filter (/=nullPos) [tokPos tok]
                        _ -> error ("Error in anaTerm " ++ show term)
        rtc = rmTypesT minF simpF signA term
    in case maybeResult $ minExpTerm minF emptyGlobalAnnos signA rtc of
         Just _  -> rtc
	 Nothing -> case rtc of
                    Simple_id v -> Qual_var v s ps
                    _ -> Sorted_term rtc s ps

{- |
    simplifies the FORMULA such that there are no type-information in it.
-}
rmTypesF :: PrettyPrint f => Min f e 
	 -> (Sign f e ->f -> f) -- ^ simplifySen for ExtFORMULA 
	 -> Sign f e -> FORMULA f -> FORMULA f
rmTypesF minF simpF signF form = 
    case form of
         Predication pS@(Pred_name _) tl pos -> 
             Predication pS (map anaTermCall tl) pos 
	 Predication (Qual_pred_name pName _ _) tl pos -> 
             Predication (Pred_name pName) (map anaTermCall tl) pos 
	 Definedness t pos -> Definedness (anaTermCall t) pos                
	 Existl_equation t1 t2 pos -> 
             Existl_equation (anaTermCall t1) (anaTermCall t2) pos  	
	 Strong_equation t1 t2 pos -> 
             Strong_equation (anaTermCall t1) (anaTermCall t2) pos  
	 Membership t sort pos -> Membership (anaTermCall t) sort pos
	 f -> error ("Error in rmTypesF " ++  show f) 
      where anaTermCall = anaTerm minF simpF signF

{- |
    analyzes the Formula if it is the Minimal Expansions of a FORMULA.
-}
anaFormula :: PrettyPrint f => Min f e -> (Sign f e -> f -> f) 
           -> Sign f e -> FORMULA f -> FORMULA f
anaFormula minF simpF sign' form1 = 
    let rmf = rmTypesF minF simpF sign' form1 
	atc = anaTerm minF simpF sign'
    in  case maybeResult $ minExpFORMULA minF emptyGlobalAnnos sign' rmf of
             Just _ -> rmf
	     Nothing -> case form1 of
			Predication predSymb tl pos -> 
                            Predication predSymb (map atc tl) pos  
			Definedness t pos -> Definedness (atc t) pos 
			Existl_equation t1 t2 pos -> 
                            Existl_equation (atc t1) (atc t2) pos  	
			Strong_equation t1 t2 pos -> 
                            Strong_equation (atc t1) (atc t2) pos  
			Membership t sort pos -> Membership (atc t) sort pos
			f -> error ("Error in anaFormula " ++ show f)
