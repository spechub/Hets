{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, C. Maeder, Uni Bremen 2004-2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   simplification of formulas and terms for output after analysis

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
    Definedness t pos -> Definedness (simplifyTermCall t) pos 
    f@(Existl_equation _ _ _) -> anaFormulaCall f
    f@(Strong_equation _ _ _) -> anaFormulaCall f
    Membership t sort pos -> Membership (simplifyTermCall t) sort pos
    ExtFORMULA f -> ExtFORMULA $ simpF sign f
    f@(Sort_gen_ax _ _) -> f
    f -> error ("Error in simplifySen " ++ show f)
    where
        simplifySenCall = simplifySen minF simpF sign
        simplifyTermCall = simplifyTerm minF simpF sign
	anaFormulaCall = anaFormula minF simpF sign

rmSort :: TERM f -> TERM f
rmSort term = case term of
         Sorted_term t _ _ -> t
         _ -> term

{- |
   simplifies the TERM such that there are no type-information in it.
-}
rmTypesT :: PrettyPrint f => 
            Min f e -- for 'anaFormula' in case of 'Conditional'
	 -> (Sign f e -> f -> f) -- ^ simplifySen for ExtFORMULA
	 -> Sign f e -> TERM f -> TERM f
rmTypesT minF simpF sign term = 
    let simTerm = simplifyTerm minF simpF sign term
        minTerm = rmSort simTerm
    in case maybeResult $ oneExpTerm minF sign minTerm of
       Just _ -> minTerm
       _ -> simTerm

oneExpTerm :: PrettyPrint f => Min f e -> Sign f e -> TERM f -> Result (TERM f)
oneExpTerm minF sign term = do 
    ts <- minExpTerm minF emptyGlobalAnnos sign term
    is_unambiguous term ts []


{- |
   simplify the TERM and keep its typing information if it had one
-}
simplifyTerm :: PrettyPrint f => Min f e -> (Sign f e -> f -> f) 
        -> Sign f e -> TERM f -> TERM f
simplifyTerm minF simpF sign term = 
    let simplifyTermC = simplifyTerm minF simpF sign
        minT = maybeResult . oneExpTerm minF sign
    in case term of
       Qual_var v sort pos -> 
           let minTerm = Application (Op_name $ simpleIdToId v) [] []
               simT = Sorted_term minTerm sort pos
           in case minT minTerm of
              Just _ -> minTerm
              Nothing -> case minT simT of
                  Just _ -> simT
                  _ -> term
       Sorted_term t sort pos ->     
           let simT = simplifyTermC t
               minTerm = rmSort simT
           in case minT minTerm of
              Just _ -> minTerm
              _ -> case minT simT of 
                   Just _ -> simT
                   Nothing -> Sorted_term minTerm sort pos
       Conditional term1 formula term2 pos -> 
           let t1 = simplifyTermC term1
               t2 = simplifyTermC term2
               f = simplifySen minF simpF sign formula
               minCond = Conditional (rmSort t1) f (rmSort t2) pos
           in case minT minCond of
              Just _ -> minCond
              Nothing -> Conditional t1 f t2 pos
       Cast t sort pos -> 
           let simT = simplifyTermC t 
               minCast = Cast (rmSort simT) sort pos
           in case minT minCast of
              Just _ -> minCast
              _ -> Cast simT sort pos
       Application opSymb@(Op_name _) ts pos -> 
           let args = map simplifyTermC ts
               minOp = Application opSymb (map rmSort args) pos
           in case minT minOp of 
              Just _ -> minOp
              Nothing -> Application opSymb args pos
       Application q@(Qual_op_name ide ty ps) tl pos -> 
           let args = zipWith (\ t s -> simplifyTermC $ Sorted_term t s ps)
                      tl $ args_OP_TYPE ty
               minArgs = map rmSort args
               res = res_OP_TYPE ty
               opSymb = Op_name ide
               unqualOp = Sorted_term (Application opSymb args pos) res ps
               minOp = Sorted_term (Application opSymb minArgs pos) res ps
           in case minT minOp of
              Just _ -> minOp
              Nothing -> case minT unqualOp of
                  Just _ -> unqualOp
                  Nothing -> Application q minArgs pos
       _ -> term

{- |
    analyzes the Formula if it is the Minimal Expansions of a FORMULA.
-}
anaFormula :: PrettyPrint f => Min f e -> (Sign f e -> f -> f) 
           -> Sign f e -> FORMULA f -> FORMULA f
anaFormula minF simpF sign form1 = 
    let minForm = maybeResult . minExpFORMULA minF emptyGlobalAnnos sign      
	simplifyTermCall = simplifyTerm minF simpF sign
        simpForm = case form1 of
	    Existl_equation t1 t2 pos -> Existl_equation 
              (simplifyTermCall t1) (simplifyTermCall t2) pos  	
	    Strong_equation t1 t2 pos -> Strong_equation 
              (simplifyTermCall t1) (simplifyTermCall t2) pos  
	    f -> error ("Error in anaFormula1 " ++ show f)
        rmForm = case simpForm of 
	    Existl_equation t1 t2 pos -> Existl_equation 
              (rmSort t1) (rmSort t2) pos  	
	    Strong_equation t1 t2 pos -> Strong_equation 
              (rmSort t1) (rmSort t2) pos  
	    f -> error ("Error in anaFormula2 " ++ show f)
     in case form1 of 
        Predication predSymb@(Pred_name _) tl pos -> 
           let args = map simplifyTermCall tl
               minPred = Predication predSymb (map rmSort args) pos
           in case minForm minPred of 
              Just _ -> minPred
              Nothing -> Predication predSymb args pos
        Predication p@(Qual_pred_name pName (Pred_type sl ps) _) tl pos -> 
           let args = zipWith (\ t s -> simplifyTermCall $ Sorted_term t s ps)
                      tl sl 
               minArgs = map rmSort args
               predSymb = Pred_name pName
               unqualPred = Predication predSymb args pos
               minPred = Predication predSymb minArgs pos
           in case minForm minPred of
              Just _ -> minPred
              Nothing -> case minForm unqualPred of
                  Just _ -> unqualPred
                  Nothing -> Predication p minArgs pos
        _ -> case minForm rmForm of 
             Just _ -> rmForm
             _ -> simpForm
