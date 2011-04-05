{- |
Module      :  $Header$
Description :  Derive induction schemes from sort generation constraints
Copyright   :  (c) Till Mossakowski, Rainer Grabbe and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

We provide both second-order induction schemes as well as their
instantiation to specific first-order formulas.
-}

module CASL.Induction (inductionScheme, generateInductionLemmas) where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Fold
import CASL.Quantification (flatVAR_DECLs)
import CASL.ToDoc

import Common.AS_Annotation as AS_Anno
import Common.Id
import Common.Utils (combine, number)

import qualified Data.Set as Set
import Data.List
import Data.Maybe

{- | derive a second-order induction scheme from a sort generation constraint
the second-order predicate variables are represented as predicate
symbols P[s], where s is a sort -}
inductionScheme :: FormExtension f => [Constraint] -> FORMULA f
inductionScheme constrs =
  induction $ map predSubst constrs
  where sorts = map newSort constrs
        injective = isInjectiveList sorts
        predSubst constr =
          (constr, \ t -> Predication predSymb [t] nullRange)
          where
          predSymb = Qual_pred_name ident typ nullRange
          Id ts cs ps =
              if injective then newSort constr else origSort constr
          ident = Id [mkSimpleId $ genNamePrefix ++ "P_"
                          ++ showId (Id ts [] ps) ""] cs ps
          typ = Pred_type [newSort constr] nullRange

{- | Function for derivation of first-order instances of sort generation
constraints.
Given a list of formulas with a free sorted variable, instantiate the
sort generation constraint for this list of formulas
It is assumed that the (original) sorts of the constraint
match the sorts of the free variables -}
instantiateSortGen :: FormExtension f
  => [(Constraint, (FORMULA f, (VAR, SORT)))] -> FORMULA f
instantiateSortGen phis =
  induction (map substFormula phis)
  where substFormula (c, (phi, (v, s))) = (c, \ t -> substitute v s t phi)

-- | substitute a term for a variable in a formula
substitute :: FormExtension f => VAR -> SORT -> TERM f -> FORMULA f -> FORMULA f
substitute v s t = foldFormula
 (mapRecord id) { foldQual_var = \ t2 v2 s2 _ ->
                  if v == v2 && s == s2 then t else t2
                , foldQuantification = \ t2 q vs p r ->
                  if elem (v, s) $ flatVAR_DECLs vs
                  then t2 else Quantification q vs p r
                }

{- | derive an induction scheme from a sort generation constraint
using substitutions as induction predicates -}
induction :: FormExtension f => [(Constraint, TERM f -> FORMULA f)] -> FORMULA f
induction constrSubsts =
   let mkVar i = mkSimpleId ("x_" ++ show i)
       sortInfo = map (\ ((cs, sub), i) -> (sub, (mkVar i, newSort cs)))
         $ number constrSubsts
       mkConclusion (subst, v) =
         mkForall [uncurry mkVarDecl v] (subst (uncurry mkVarTerm v)) nullRange
       inductionConclusion = conjunct $ map mkConclusion sortInfo
       inductionPremises = map (mkPrems $ map snd constrSubsts) constrSubsts
       inductionPremise = conjunct $ concat inductionPremises
   in mkImpl inductionPremise inductionConclusion

{- | construct premise set for the induction scheme
for one sort in the constraint -}
mkPrems :: FormExtension f => [TERM f -> FORMULA f]
  -> (Constraint, TERM f -> FORMULA f) -> [FORMULA f]
mkPrems substs (constr, sub) = map (mkPrem substs sub) (opSymbs constr)

-- | construct a premise for the induction scheme for one constructor
mkPrem :: FormExtension f => [TERM f -> FORMULA f] -> (TERM f -> FORMULA f)
  -> (OP_SYMB, [Int]) -> FORMULA f
mkPrem substs subst (opSym@(Qual_op_name _ (Op_type _ argTypes _ _) _), idx) =
  mkForall qVars phi nullRange
  where
  qVars = map (\ (a, i) -> mkVarDeclStr ("y_" ++ show i) a) $ number argTypes
  phi = if null indHyps then indConcl
           else mkImpl (conjunct indHyps) indConcl
  indConcl = subst $ mkAppl opSym $ map toQualVar qVars
  indHyps = mapMaybe indHyp (zip qVars idx)
  indHyp (v1, i) =
    if i < 0 then Nothing -- leave out sorts from outside the constraint
     else Just $ (substs !! i) $ toQualVar v1
mkPrem _ _ (opSym, _) =
  error ("CASL.Induction. mkPrems: "
        ++ "unqualified operation symbol occuring in constraint: "
        ++ show opSym)

-- | for goals try to generate additional implications based on induction
generateInductionLemmas :: FormExtension f => Bool
  -> (Sign f e, [Named (FORMULA f)]) -> (Sign f e, [Named (FORMULA f)])
generateInductionLemmas b (sig, sens) = let
   sortGens = foldr (\ s cs -> case sentence s of
     Sort_gen_ax c _ -> c : cs
     _ -> cs) [] axs
   (axs, goals) = partition isAxiom sens
   in (sig, (if b then sens else axs)
       ++ generateInductionLemmasAux b sortGens goals)

generateInductionLemmasAux
  :: FormExtension f => Bool
  -- ^ if True create additional implication otherwise replace goals
  -> [[Constraint]] -- ^ the constraints of a theory
  -> [AS_Anno.Named (FORMULA f)] -- ^ all goals of a theory
  -> [AS_Anno.Named (FORMULA f)]
{- ^ all the generated induction lemmas
and the labels are derived from the goal-names -}
generateInductionLemmasAux b sort_gen_axs goals = let
    findVar s [] = error ("CASL.generateInductionLemmas:\n"
                       ++ "No VAR found of SORT " ++ show s ++ "!")
    findVar s ((vl, sl) : lst) = if s == sl then vl else findVar s lst
    removeVarsort v s f = case f of
      Quantification Universal varDecls formula rng ->
        let vd' = newVarDecls varDecls
        in if null vd' then formula
            else Quantification Universal vd' formula rng
      _ -> f
      where
        newVarDecls = filter (\ (Var_decl vs _ _) -> not $ null vs) .
            map (\ var_decl@(Var_decl vars varsort r) ->
                   if varsort == s
                     then Var_decl (filter (/= v) vars) s r
                     else var_decl)
    (uniQuantGoals, restGoals) =
            foldr ( \ goal (ul, rl) -> case sentence goal of
                     Quantification Universal varDecl _ _ ->
                         ((goal, flatVAR_DECLs varDecl) : ul, rl)
                     _ -> (ul, goal : rl)) ([], []) goals

    {- For each constraint we get a list of goals out of uniQuantGoals
    which contain the constraint's newSort. Afterwards all combinations
    are created. -}
    constraintGoals = combine
      . map (\ c -> filter (any ((newSort c ==) . snd) . snd)
                                 uniQuantGoals)
    combis =
         {- returns big list containing tuples of constraints and a matching
         combination (list) of goals. -}
         (concatMap (\ c ->
                          map (\ combi -> (c, combi)) $ constraintGoals c)
                       sort_gen_axs)
    singleDts = map head $ filter isSingle sort_gen_axs
    indSorts = Set.fromList $ map newSort singleDts
    (simpleIndGoals, rest2) = foldr (\ (gs, vs) (ul, rl) ->
       case dropWhile (not . (`Set.member` indSorts) . snd) vs of
         [] -> (ul, gs : rl)
         (v, s) : _ -> case find ((== s) . newSort) singleDts of
           Nothing -> (ul, gs : rl)
           Just c -> ((gs, (v, s), c) : ul, rl)) ([], []) uniQuantGoals
    toIndPrem (gs, (v, s), c) =
      let f = removeVarsort v s $ sentence gs
          sb t = substitute v s t f
          ps = mkPrems [sb] (c, sb)
      in gs { sentence = conjunct ps }
    in if b then
    map (\ (cons, formulas) ->
            let formula = instantiateSortGen
                    $ map (\ (c, (f, varsorts)) ->
                       let s = newSort c
                           vs = findVar s varsorts
                       in (c, (removeVarsort vs s $ sentence f, (vs, s))))
                    $ zip cons formulas

                sName = (if null formulas then id else tail)
                        (foldr ((++) . (++) "_" . senAttr . fst) "" formulas
                         ++ "_induction")
            in makeNamed sName formula
         ) combis
    else map toIndPrem simpleIndGoals ++ rest2 ++ restGoals
