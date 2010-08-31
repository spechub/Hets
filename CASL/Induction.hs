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
import Common.AS_Annotation as AS_Anno
import Common.Id
import Common.Result
import Common.DocUtils
import Common.Utils (combine, number)
import Data.Maybe

-- | derive a second-order induction scheme from a sort generation constraint
-- | the second-order predicate variables are represented as predicate
-- | symbols P[s], where s is a sort
inductionScheme :: Pretty f =>  [Constraint] -> Result (FORMULA f)
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

-- | Function for derivation of first-order instances of sort generation
-- | constraints.
-- | Given a list of formulas with a free sorted variable, instantiate the
-- | sort generation constraint for this list of formulas
-- | It is assumed that the (original) sorts of the constraint
-- | match the sorts of the free variables
instantiateSortGen :: Pretty f =>  [(Constraint, (FORMULA f, VAR))]
                        -> Result (FORMULA f)
instantiateSortGen phis =
  induction (map substFormula phis)
  where substFormula (c, (phi, v)) = (c, \ t -> substitute v t phi)

-- | substitute a term for a variable in a formula
substitute :: Pretty f =>  VAR -> TERM f -> FORMULA f -> FORMULA f
substitute v t = foldFormula
 (mapRecord id) { foldQual_var = \ t2 v2 _ _ ->
                  if v == v2 then t else t2
                , foldQuantification = \ t2 q vs p r ->
                  if elem v $ concatMap ( \ (Var_decl l _ _) -> l) vs
                  then t2 else Quantification q vs p r
                }

-- | derive an induction scheme from a sort generation constraint
-- | using substitutions as induction predicates
induction :: Pretty f => [(Constraint, TERM f -> FORMULA f)]
          -> Result (FORMULA f)
induction constrSubsts = do
   let mkVar i = mkSimpleId ("x_" ++ show i)
       sortInfo = map (\ ((cs, sub), i) -> (cs, sub, (mkVar i, newSort cs)))
         $ number constrSubsts
       mkConclusion (_, subst, v) =
         mkForall [uncurry mkVarDecl v] (subst (uncurry mkVarTerm v)) nullRange
       inductionConclusion = conjunct $ map mkConclusion sortInfo
   inductionPremises <- mapM (mkPrems $ map snd constrSubsts) sortInfo
   let inductionPremise = conjunct $ concat inductionPremises
   return $ mkImpl inductionPremise inductionConclusion

-- | construct premise set for the induction scheme
-- | for one sort in the constraint
mkPrems :: Pretty f => [TERM f -> FORMULA f]
            -> (Constraint, TERM f -> FORMULA f, (VAR, SORT))
            -> Result [FORMULA f]
mkPrems substs info@(constr,_,_) = mapM (mkPrem substs info) (opSymbs constr)

-- | construct a premise for the induction scheme for one constructor
mkPrem :: Pretty f =>  [TERM f -> FORMULA f]
           -> (Constraint, TERM f -> FORMULA f, (VAR, SORT))
           -> (OP_SYMB, [Int])
           -> Result (FORMULA f)
mkPrem substs (_,subst,_)
       (opSym@(Qual_op_name _ (Op_type _ argTypes _ _) _), idx) =
  return $ mkForall qVars phi nullRange
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
  fail ("CASL.Induction. mkPrems: "
        ++ "unqualified operation symbol occuring in constraint: "
        ++ show opSym)

-- !! documentation is missing
generateInductionLemmas :: Pretty f =>  (Sign f e, [Named (FORMULA f)])
                        -> (Sign f e, [Named (FORMULA f)])
generateInductionLemmas (sig, axs) = (sig, axs ++ inductionAxs) where
   sortGens = filter isSortGen (map sentence axs)
   goals = filter (not . isAxiom) axs
   inductionAxs = fromJust $ maybeResult
     $ generateInductionLemmasAux sortGens goals

-- | determine whether a formula is a sort generation constraint
isSortGen :: FORMULA a -> Bool
isSortGen (Sort_gen_ax _ _) = True
isSortGen _ = False

generateInductionLemmasAux
  :: Pretty f => [FORMULA f] -- ^ only Sort_gen_ax of a theory
  -> [AS_Anno.Named (FORMULA f)] -- ^ all goals of a theory
  -> Result ([AS_Anno.Named (FORMULA f)])
-- ^ all the generated induction lemmas
-- and the labels are derived from the goal-names
generateInductionLemmasAux sort_gen_axs goals =
    mapM (\ (cons, formulas) -> do
            formula <- instantiateSortGen
                $ map (\ (c, (f, varsorts)) ->
                       let s = newSort c
                           vs = findVar s varsorts
                       in (c, (removeVarsort vs s $ sentence f, vs)))
                    $ zip cons formulas

            let sName = (if null formulas then id else tail)
                        (foldr ((++) . (++) "_" . senAttr . fst) "" formulas
                         ++ "_induction")
            return $ makeNamed sName formula
         )
         -- returns big list containing tuples of constraints and a matching
         -- combination (list) of goals.
         (concatMap (\ (Sort_gen_ax c _) ->
                          map (\ combi -> (c, combi)) $ constraintGoals c)
                       sort_gen_axs)
  where
    findVar s [] = error ("CASL.generateInductionLemmas:\n"
                       ++ "No VAR found of SORT " ++ show s ++ "!")
    findVar s ((vl, sl) : lst) = if s == sl then vl else findVar s lst
    removeVarsort v s f = case f of
      Quantification Universal varDecls formula rng ->
        let vd' = newVarDecls varDecls
        in  if null vd' then formula
            else Quantification Universal vd' formula rng
      _ -> f
      where
        newVarDecls = filter (\ (Var_decl vs _ _) -> not $ null vs) .
            map (\ var_decl@(Var_decl vars varsort r) ->
                   if varsort == s
                     then Var_decl (filter (not . (==) v) vars) s r
                     else var_decl)
    uniQuantGoals =
            foldr ( \ goal l -> case sentence goal of
                                  Quantification Universal varDecl _ _ ->
                                     (goal, flatVAR_DECLs varDecl) : l
                                  _ -> l) [] goals
    -- For each constraint we get a list of goals out of uniQuantGoals
    -- which contain the constraint's newSort. Afterwards all combinations
    -- are created.
    constraintGoals = combine
      . map (\ c -> filter (any ((newSort c ==) . snd) . snd)
                                 uniQuantGoals)
