{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

  Free variables; getting rid of superfluous quantifications
    
-}
module CASL.Quantification where

import CASL.AS_Basic_CASL
import Common.Id
import Data.List(nubBy)
import qualified Common.Lib.Set as Set

flatVAR_DECLs :: [VAR_DECL] -> [(VAR, SORT)]
flatVAR_DECLs = concatMap (\ (Var_decl vs s _) -> map (\ v -> (v, s)) vs)

freeVars :: FORMULA f -> Set.Set VAR
freeVars f = case f of 
    Quantification _ vdecl phi _ -> foldr Set.delete (freeVars phi) $ 
		    concatMap ( \ (Var_decl vs _ _) -> vs) vdecl
    Conjunction phis _ -> Set.unions $ map freeVars  phis
    Disjunction phis _ -> Set.unions $ map freeVars phis
    Implication phi1 phi2 _ _ -> freeVars phi1 `Set.union` freeVars phi2
    Equivalence phi1 phi2 _ -> freeVars phi1 `Set.union` freeVars phi2
    Negation phi _ -> freeVars phi
    Predication _ args _ -> Set.unions $ map freeTermVars args
    Definedness t _ -> freeTermVars t
    Existl_equation t1 t2 _ -> freeTermVars t1 `Set.union` freeTermVars t2
    Strong_equation t1 t2 _ -> freeTermVars t1 `Set.union` freeTermVars t2
    Membership t _ _ -> freeTermVars t
    _ -> Set.empty


freeTermVars :: TERM f -> Set.Set VAR
freeTermVars t = case t of 
    Simple_id v -> Set.single v
    Qual_var v _ _ -> Set.single v
    Application _ args _ -> Set.unions $ map freeTermVars args
    Sorted_term st _ _ -> freeTermVars st
    Cast st _ _ -> freeTermVars st
    Conditional t1 phi t2 _ -> freeVars phi `Set.union` 
			       freeTermVars t1 `Set.union` freeTermVars t2
    _ -> Set.empty

-- quantify only over free variables (and only once)
effQuantify :: QUANTIFIER -> [VAR_DECL] -> FORMULA f -> [Pos] -> FORMULA f
effQuantify q vdecls phi pos =
    let fvs = freeVars phi 
	filterVAR_DECL (Var_decl vs s ps) =
	    Var_decl (filter (`Set.member` fvs) vs) s ps
	flatVAR_DECL (Var_decl vs s ps) = 
	    map (\v -> Var_decl [v] s ps) vs
	newDecls = concatMap (flatVAR_DECL . filterVAR_DECL) vdecls
	myNub = nubBy (\ (Var_decl v1 _ _) (Var_decl v2 _ _) -> v1 == v2)
	in if null newDecls then phi else 
	   Quantification q (reverse $ myNub $ reverse newDecls) phi pos
	
-- strip superfluous (or nested) quantifications
stripQuant :: FORMULA f -> FORMULA f
stripQuant (Quantification quant vdecl phi pos) =
    let newF = stripQuant phi 
	qF = effQuantify quant vdecl phi pos in 
	case newF of 
		 Quantification quant2 vd2 f2 ps -> 
		     if quant == quant2 then 
			effQuantify quant (vdecl ++ vd2) f2 (pos ++ ps)
		     else qF
		 _ -> qF
stripQuant (Conjunction phis pos) =
  Conjunction (map stripQuant phis) pos
stripQuant (Disjunction phis pos) =
  Disjunction (map stripQuant phis) pos
stripQuant (Implication phi1 phi2 b pos) =
  Implication (stripQuant phi1) (stripQuant phi2) b pos
stripQuant (Equivalence phi1 phi2 pos) =
  Equivalence (stripQuant phi1) (stripQuant phi2) pos
stripQuant (Negation phi pos) =
  Negation (stripQuant phi) pos
stripQuant phi = phi
