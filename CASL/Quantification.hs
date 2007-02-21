{- |
Module      :  $Header$
Description :  Free variables; getting rid of superfluous quantifications
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
import Data.List
import qualified Data.Set as Set

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
    let flatVAR_DECL (Var_decl vs s ps) = 
            map (\v -> Var_decl [v] s ps) vs
        joinVarDecl = foldr1 ( \ (Var_decl v1 s1 ps) (Var_decl v2 _s2 _) -> 
                          Var_decl (v1 ++ v2) s1 ps)
        cleanDecls = 
            map joinVarDecl . myGroup . reverse . myNub . reverse . 
                   concatMap flatVAR_DECL
        myGroup = groupBy ( \ (Var_decl _ s1 _) (Var_decl _ s2 _) -> s1 == s2)
        myNub = nubBy ( \ (Var_decl v1 _ _) (Var_decl v2 _ _) -> v1 == v2)
        in case q of 
           Unique_existential -> Quantification q (cleanDecls vdecls) phi pos
           _ -> let fvs = freeVars phi 
                    filterVAR_DECL (Var_decl vs s ps) =
                        Var_decl (filter (\ v -> Set.member (v,s) fvs) vs) s ps
                    newDecls = cleanDecls $ map filterVAR_DECL vdecls
                in if null newDecls then phi else 
                   Quantification q newDecls phi pos


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
