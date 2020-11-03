{- |
Module      :  ./CASL/Utils.hs
Description :  Utilities for CASL and its comorphisms
Copyright   :  (c) Klaus Luettich and Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Utilities for CASL and its comorphisms

-}

module CASL.Utils where

import Data.Maybe
import Data.List

import qualified Data.Set as Set
import qualified Data.HashMap.Strict as Map

import Common.Id

import CASL.AS_Basic_CASL
import CASL.Fold

type Subst f = Map.HashMap VAR (TERM f)

-- | specialized delete that deletes all shadowed variables
deleteVMap :: [VAR_DECL] -> Subst f -> Subst f
deleteVMap vDecls m = foldr Map.delete m
  $ concatMap (\ (Var_decl vs _ _) -> vs) vDecls

replaceVarsRec :: Subst f -> (f -> f) -> Record f (FORMULA f) (TERM f)
replaceVarsRec m mf = (mapRecord mf)
     { foldQual_var = \ qv v _ _ ->
           fromMaybe qv $ Map.lookup v m
     , foldQuantification = \ orig _ _ _ _ ->
               let Quantification q vs f ps = orig
                   nm = deleteVMap vs m
               in Quantification q vs (replaceVarsF nm mf f) ps
     }

{- | replaceVars replaces all Qual_var occurences that are supposed
to be replaced according to the Subst -}
replaceVarsF :: Subst f
             -> (f -> f)
             -- ^ this function replaces Qual_var in ExtFORMULA
             -> FORMULA f -> FORMULA f
replaceVarsF m = foldFormula . replaceVarsRec m

{- | buildVMap constructs a mapping between a list of old variables and
corresponding fresh variables based on two lists of VAR_DECL -}
buildVMap :: [VAR_DECL] -> [VAR_DECL] -> Subst f
buildVMap vDecls fVDecls =
    Map.fromList (concat (zipWith toTups vDecls fVDecls))
    where toTups (Var_decl vars1 sor1 _) (Var_decl vars2 sor2 _) =
            if sor1 == sor2 then zipWith (toTup sor1) vars1 vars2
            else error "CASL.Utils.buildVMap"
          toTup s v1 v2 = (v1, mkVarTerm v2 s)

codeOutUniqueRecord :: (f -> f) -> (f -> f) -> Record f (FORMULA f) (TERM f)
codeOutUniqueRecord rf mf = (mapRecord mf)
    { foldQuantification = \ _ q vDecl f' ps ->
         case q of
         Unique_existential -> let
            eqForms (Var_decl vars1 sor1 _) (Var_decl vars2 sor2 _) =
              if sor1 == sor2 then zipWith (eqFor sor1) vars1 vars2
              else error "codeOutUniqueRecord1"
            eqFor s v1 v2 = mkStEq (mkVarTerm v1 s) (mkVarTerm v2 s)
            {- freshVars produces new variables based on a list
            of defined variables
            args: (1) set of already used variable names
            (2) list of variables -}
            freshVars = mapAccumL freshVar
            freshVar accSet (Var_decl vars sor _) =
              let accSet' = Set.union (Set.fromList vars) accSet
                  (accSet'', vars') = mapAccumL nVar accSet' vars
              in (accSet'', Var_decl vars' sor nullRange)
            genVar t i = mkSimpleId $ tokStr t ++ '_' : show i
            nVar aSet v =
              let v' = fromJust (find (not . flip Set.member aSet)
                                 [genVar v (i :: Int) | i <- [1 ..]])
              in (Set.insert v' aSet, v')
            (vSet', vDecl') = freshVars Set.empty vDecl
            (_vSet'', vDecl'') = freshVars vSet' vDecl
            f'_rep_x = replaceVarsF (buildVMap vDecl vDecl') rf f'
            f'_rep_y = replaceVarsF (buildVMap vDecl vDecl'') rf f'
            allForm = mkForallRange (vDecl' ++ vDecl'')
                        (mkImpl
                              (conjunct [f'_rep_x, f'_rep_y])
                              implForm) ps
            implForm = conjunct $ concat (zipWith eqForms vDecl' vDecl'')
            in Junction Con
                   [Quantification Existential vDecl f' ps,
                    allForm] ps
         _ -> Quantification q vDecl f' ps
    }

{- | codeOutUniqueExtF compiles every unique_existential quantification
to simple quantifications. It works recursively through the whole
formula and only touches Unique_existential quantifications:
exists! x . phi(x) ==>
(exists x. phi(x)) /\ (forall x,y . phi(x) /\ phi(y) => x=y) -}
codeOutUniqueExtF :: (f -> f)
                  -- ^ this function replaces Qual_var in ExtFORMULA
                  -> (f -> f)
                  -- ^ codes out Unique_existential in ExtFORMULA
                  -> FORMULA f -> FORMULA f
codeOutUniqueExtF rf = foldFormula . codeOutUniqueRecord rf

codeOutCondRecord :: (Eq f) => (f -> f)
                  -> Record f (FORMULA f) (TERM f)
codeOutCondRecord fun =
    (mapRecord fun)
          { foldPredication = \ phi _ _ _ ->
                    either (codeOutConditionalF fun) id
                               (codeOutCondPredication phi)
          , foldEquation = \ o _ _ _ _ ->
                let Equation t1 e t2 ps = o in
                  either (codeOutConditionalF fun) id
                    (mkEquationAtom (`Equation` e) t1 t2 ps)
          , foldMembership = \ o _ _ _ ->
                let Membership t s ps = o in
                  either (codeOutConditionalF fun) id
                    (mkSingleTermF (`Membership` s) t ps)
          , foldDefinedness = \ o _ _ ->
                let Definedness t ps = o in
                  either (codeOutConditionalF fun) id
                    (mkSingleTermF Definedness t ps)
          }

codeOutCondPredication :: (Eq f) => FORMULA f
                   -> Either (FORMULA f) (FORMULA f)
                   {- ^ Left means check again for Conditional,
                   Right means no Conditional left -}
codeOutCondPredication phi@(Predication _ ts _) =
    maybe (Right phi) (Left . constructExpansion phi)
          $ listToMaybe $ mapMaybe findConditionalT ts
codeOutCondPredication _ = error "CASL.Utils: Predication expected"

constructExpansion :: (Eq f) => FORMULA f
                   -> TERM f
                   -> FORMULA f
constructExpansion atom c@(Conditional t1 phi t2 ps) =
    Junction Con [ Relation phi Implication (substConditionalF c t1 atom) ps
                 , Relation (Negation phi ps) Implication
                              (substConditionalF c t2 atom) ps] ps
constructExpansion _ _ = error "CASL.Utils: Conditional expected"

mkEquationAtom :: (Eq f) => (TERM f -> TERM f -> Range -> FORMULA f)
               -- ^ equational constructor
               -> TERM f -> TERM f -> Range
               -> Either (FORMULA f) (FORMULA f)
               {- ^ Left means check again for Conditional,
               Right means no Conditional left -}
mkEquationAtom cons t1 t2 ps =
    maybe (Right phi) (Left . constructExpansion phi)
          $ listToMaybe $ mapMaybe findConditionalT [t1, t2]
    where phi = cons t1 t2 ps

mkSingleTermF :: (Eq f) => (TERM f -> Range -> FORMULA f)
              -- ^ single term atom constructor
               -> TERM f -> Range
               -> Either (FORMULA f) (FORMULA f)
               {- ^ Left means check again for Conditional,
               Right means no Conditional left -}
mkSingleTermF cons t ps =
    maybe (Right phi) (Left . constructExpansion phi)
          (findConditionalT t)
    where phi = cons t ps

{- |
'codeOutConditionalF' implemented via 'CASL.Fold.foldFormula'

at each atom with a term find first (most left,no recursion into
   terms within it) Conditional term and report it (findConditionalT)

substitute the original atom with the conjunction of the already
   encoded atoms and already encoded formula

encoded atoms are the result of the substition (substConditionalF)
   of the Conditional term with each result term of the Conditional
   term plus recusion of codingOutConditionalF

encoded formulas are the result of codingOutConditionalF

expansion of conditionals according to CASL-Ref-Manual:
\'@A[T1 when F else T2]@\' expands to
\'@(A[T1] if F) /\\ (A[T2] if not F)@\'
-}
codeOutConditionalF :: (Eq f) =>
                       (f -> f)
                    -> FORMULA f -> FORMULA f
codeOutConditionalF = foldFormula . codeOutCondRecord

findConditionalRecord :: Record f (Maybe (TERM f)) (Maybe (TERM f))
findConditionalRecord =
    (constRecord (error "findConditionalRecord")
     (listToMaybe . catMaybes) Nothing)
    { foldConditional = \ cond _ _ _ _ -> Just cond }

findConditionalT :: TERM f -> Maybe (TERM f)
findConditionalT =
    foldOnlyTerm (error "findConditionalT") findConditionalRecord

substConditionalRecord :: (Eq f)
                       => TERM f -- ^ Conditional to search for
                       -> TERM f -- ^ newly inserted term
                       -> Record f (FORMULA f) (TERM f)
substConditionalRecord c t = (mapRecord id)
     { foldConditional = \ c1 _ _ _ _ ->
       {- FIXME: correct implementation would use an equality
       which checks for correct positions also! -}
             if c1 == c then t else c1
     }

substConditionalF :: (Eq f)
                  => TERM f -- ^ Conditional to search for
                  -> TERM f -- ^ newly inserted term
                  -> FORMULA f -> FORMULA f
substConditionalF c = foldFormula . substConditionalRecord c

{- |
  Subsitute predications with strong equation if it is equivalent to.
-}
eqSubstRecord :: Set.Set PRED_SYMB -- ^ equivalent predicates
              -> (f -> f) -> Record f (FORMULA f) (TERM f)
eqSubstRecord eqPredSet extFun =
      (mapRecord extFun) {foldPredication = foldPred}
    where foldPred _ psymb tList rng =
            if Set.member psymb eqPredSet
              then let [f, s] = tList in Equation f Strong s rng
              else Predication psymb tList rng

substEqPreds :: Set.Set PRED_SYMB -> (f -> f) -> FORMULA f -> FORMULA f
substEqPreds eqPredSet = foldFormula . eqSubstRecord eqPredSet
