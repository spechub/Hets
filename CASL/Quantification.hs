{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Free variables; getting rid of superfluous quantifications
    
-}
module CASL.Quantification where

import CASL.AS_Basic_CASL
import CASL.Fold
import Common.Id
import Data.List(nubBy)
import qualified Common.Lib.Set as Set

flatVAR_DECLs :: [VAR_DECL] -> [(VAR, SORT)]
flatVAR_DECLs = concatMap (\ (Var_decl vs s _) -> map (\ v -> (v, s)) vs)

type VarSet = Set.Set (VAR, SORT)

freeVarsRecord :: (f -> VarSet) -> Record f VarSet VarSet
freeVarsRecord mf = (constRecord mf Set.unions Set.empty) 
    { foldQual_var = \ _ v s _ -> Set.singleton (v, s)
    , foldQuantification = \ _ _ vdecl phiVars _ -> 
           Set.difference phiVars $ 
                    Set.fromList $ flatVAR_DECLs vdecl
    }

freeVars :: FORMULA f -> VarSet
freeVars = foldFormula $ freeVarsRecord $ const Set.empty

-- | quantify only over free variables (and only once)
effQuantify :: QUANTIFIER -> [VAR_DECL] -> FORMULA f -> Range -> FORMULA f
effQuantify q vdecls phi pos =
    let fvs = freeVars phi 
	filterVAR_DECL (Var_decl vs s ps) =
	    Var_decl (filter (\ v -> Set.member (v,s) fvs) vs) s ps
	flatVAR_DECL (Var_decl vs s ps) = 
	    map (\v -> Var_decl [v] s ps) vs
	newDecls = concatMap (flatVAR_DECL . filterVAR_DECL) vdecls
	myNub = nubBy (\ (Var_decl v1 _ _) (Var_decl v2 _ _) -> v1 == v2)
	in if null newDecls && q /= Unique_existential then phi else 
	   Quantification q (reverse $ myNub $ reverse newDecls) phi pos


stripRecord :: (f -> f) -> Record f (FORMULA f) (TERM f) 
stripRecord mf = (mapRecord mf) 
    { foldQuantification = \ _ quant vdecl newF pos -> 
      let qF = effQuantify quant vdecl newF pos in 
      case newF of 
		 Quantification quant2 vd2 f2 ps -> 
		     if quant == quant2 then 
			effQuantify quant (vdecl ++ vd2) f2 (pos `appRange` ps)
		     else qF
		 _ -> qF
    }
	
-- | strip superfluous (or nested) quantifications
stripQuant :: FORMULA f -> FORMULA f
stripQuant = foldFormula $ stripRecord id
