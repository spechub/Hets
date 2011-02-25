{- |
Module      :  $Header$
Description :  Free variables; getting rid of superfluous quantifications
Copyright   :  (c) Till Mossakowski and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Free variables; getting rid of superfluous quantifications

-}
module CASL.Quantification where

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.Utils (nubOrdOn)

import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

flatVAR_DECLs :: [VAR_DECL] -> [(VAR, SORT)]
flatVAR_DECLs = concatMap (\ (Var_decl vs s _) -> map (\ v -> (v, s)) vs)

freeVarsRecord :: (f -> VarSet) -> Record f VarSet VarSet
freeVarsRecord mf = (constRecord mf Set.unions Set.empty)
    { foldQual_var = \ _ v s _ -> Set.singleton (v, s)
    , foldQuantification = \ _ _ vdecl phiVars _ ->
           Set.difference phiVars $
                    Set.fromList $ flatVAR_DECLs vdecl
    }

freeTermVars :: TermExtension f => Sign f e -> TERM f -> VarSet
freeTermVars = foldTerm . freeVarsRecord . freeVarsOfExt

freeVars :: TermExtension f => Sign f e -> FORMULA f -> VarSet
freeVars = foldFormula . freeVarsRecord . freeVarsOfExt

-- | quantify only over free variables (and only once)
effQuantify :: TermExtension f => Sign f e -> QUANTIFIER -> [VAR_DECL]
            -> FORMULA f -> Range -> FORMULA f
effQuantify sign q vdecls phi pos =
    let flatVAR_DECL (Var_decl vs s ps) =
            map (\ v -> Var_decl [v] s ps) vs
        joinVarDecl = foldr1 ( \ (Var_decl v1 s1 ps) (Var_decl v2 _s2 _) ->
                          Var_decl (v1 ++ v2) s1 ps)
        cleanDecls =
            map joinVarDecl . myGroup . reverse . myNub . reverse .
                   concatMap flatVAR_DECL
        myGroup = groupBy (\ (Var_decl _ s1 _) (Var_decl _ s2 _) -> s1 == s2)
        myNub = nubOrdOn (\ (Var_decl v _ _) -> v)
        in case q of
           Unique_existential -> Quantification q (cleanDecls vdecls) phi pos
           _ -> let fvs = freeVars sign phi
                    filterVAR_DECL (Var_decl vs s ps) =
                        Var_decl (filter (\ v -> Set.member (v, s) fvs
                            || Set.member s (emptySortSet sign)) vs) s ps
                    newDecls = cleanDecls $ map filterVAR_DECL vdecls
                in if null newDecls then phi else
                   Quantification q newDecls phi pos


stripRecord :: TermExtension f => Sign f e -> (f -> f)
            -> Record f (FORMULA f) (TERM f)
stripRecord s mf = (mapRecord mf)
    { foldQuantification = \ _ quant vdecl newF pos ->
      let qF = effQuantify s quant vdecl newF pos in
      case newF of
        Quantification quant2 vd2 f2 ps ->
            if quant /= quant2 then qF else
                effQuantify s quant (vdecl ++ vd2) f2 (pos `appRange` ps)
        _ -> qF
    }

-- | strip superfluous (or nested) quantifications
stripQuant :: TermExtension f => Sign f e -> FORMULA f -> FORMULA f
stripQuant s = foldFormula $ stripRecord s id

-- | strip all universal quantifications
stripAllQuant :: FORMULA f -> FORMULA f
stripAllQuant f = case f of
  Quantification Universal _ phi _ -> stripAllQuant phi
  _ -> f

-- | get top-level variables
getQuantVars :: FORMULA f -> VarSet
getQuantVars f = case f of
  Quantification Universal vds _ _ -> Set.fromList $ flatVAR_DECLs vds
  _ -> Set.empty

-- | get top-level variables for all sentences
getTopVars :: [Named (FORMULA f)] -> VarSet
getTopVars = Set.unions . map (getQuantVars . sentence)

diffVars :: Map.Map VAR SORT -> VarSet -> Map.Map VAR SORT
diffVars = Set.fold (\ (v, s) m -> case Map.lookup v m of
    Just t | t == s -> Map.delete v m
    _ -> m)

warnUnusedVars :: String -> Sign f e -> VarSet -> [Diagnosis]
warnUnusedVars msg sig = map (mkDiag Warning $ "unused" ++ msg ++ "variable")
  . Map.keys . diffVars (varMap sig)

warnUnused :: Sign f e -> [Named (FORMULA f)] -> [Diagnosis]
warnUnused sig = warnUnusedVars " " sig . getTopVars
