{- |
Module:  $Header$
Copyright   :  (c) Zicheng Wang, C. Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Comorphisms.PCFOL2CFOL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.AS_Annotation
import Data.List

--CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as SL hiding (bottom)
import CASL.Overload
import CASL.Simplify
import CASL.Fold

-- | The identity of the comorphism
data PCFOL2CFOL = PCFOL2CFOL deriving (Show)

instance Language PCFOL2CFOL -- default definition is okay

instance Comorphism PCFOL2CFOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol () where
    sourceLogic PCFOL2CFOL = CASL
    sourceSublogic PCFOL2CFOL = SL.top { sub_features = NoSub }
    targetLogic PCFOL2CFOL = CASL
    mapSublogic PCFOL2CFOL sl = if has_part sl then sl
                      { has_part = False -- partiality is coded out
                      , has_eq = True
                      , which_logic = max Horn $ which_logic sl
                      , has_pred = True
                      } else sl
    map_theory PCFOL2CFOL = mkTheoryMapping ( \ sig ->
          let e = sig2FOL sig in return (e, generateFOLAxioms sig))
          (map_sentence PCFOL2CFOL)
    map_morphism PCFOL2CFOL m = return m
                { msource = sig2FOL $ msource m
                , mtarget = sig2FOL $ mtarget m
                , fun_map = Map.map (\ (i, _) -> (i, Total)) $
                            fun_map m }
    map_sentence PCFOL2CFOL sig =
        return . simplifyFormula id . totalizeFormula (sortsWithBottom sig) id
    map_symbol PCFOL2CFOL s =
      Set.singleton s { symbType = totalizeSymbType $ symbType s }

totalizeSymbType :: SymbType -> SymbType
totalizeSymbType t = case t of
  OpAsItemType ot -> OpAsItemType ot { opKind = Total }
  _ -> t

sortsWithBottom :: Sign f e -> Set.Set SORT
sortsWithBottom sign =
    let ops = Map.elems $ opMap sign
        resSortsOfPartialFcts =
            Set.unions $ map (Set.map opRes .
                                 Set.filter ( \ t -> opKind t == Partial))
            ops
        collect given =
            let more = Set.unions $ map (Set.map opRes .
                                 Set.filter ( \ t -> any
                                 (flip Set.member given) $ opArgs t)) ops
            in if Set.isSubsetOf more given then given
               else collect $ Set.union more given
     in collect resSortsOfPartialFcts

sig2FOL :: Sign f e -> Sign f e
sig2FOL sig = sig { opMap=newOpMap, predMap = newpredMap }
 where
   newTotalMap = Map.map (Set.map $ makeTotal Total) $ opMap sig
   botType x = OpType {opKind = Total, opArgs=[], opRes=x }
   bsorts = sortsWithBottom sig
   botTypes = Set.map botType bsorts
   newOpMap  = Map.insert bottom botTypes newTotalMap
   defType x = PredType{predArgs=[x]}
   defTypes = Set.map defType bsorts
   newpredMap = Map.insert defPred defTypes $ predMap sig

bottom :: Id
bottom = mkId[mkSimpleId "g__bottom"]
defPred :: Id
defPred = mkId[mkSimpleId "g__defined"]

generateFOLAxioms :: Sign f e -> [Named(FORMULA ())]
generateFOLAxioms sig = filter (not . is_True_atom . sentence) $ map
  (mapNamed (simplifyFormula id .
  rmDefs bsorts id)) $
  concat
   ([inlineAxioms CASL
      " sort s          \
      \ pred d:s        \
      \ . exists x:s.d(x)            %(ga_nonEmpty)%" ++
     inlineAxioms CASL
      " sort s              \
      \ op bottom:s         \
      \ pred d:s            \
      \ forall x:s . not d(x) <=> x=bottom            %(ga_notDefBottom)%"
        | s <- sortList ] ++
    [inlineAxioms CASL
      " sort t             \
      \ sorts s_i          \
      \ sorts s_k          \
      \ op f:s_i->t     \
      \ var y_k:s_k             \
      \ forall y_i:s_i . def f(y_i) <=> def y_k /\\ def y_k %(ga_totality)%"
        | (f,typ) <- opList, opKind typ == Total,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL
      " sort t             \
      \ sorts s_i          \
      \ sorts s_k          \
      \ op f:s_i->t     \
      \ var y_k:s_k             \
      \ forall y_i:s_i . def f(y_i) => def y_k /\\ def y_k %(ga_strictness)%"
        | (f,typ) <- opList, opKind typ == Partial,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL
      " sorts s_i          \
      \ sorts s_k          \
      \ pred p:s_i     \
      \ var y_k:s_k             \
      \ forall y_i:s_i . p(y_i) => def y_k /\\ def y_k \
      \ %(ga_predicate_strictness)%"
        | (p,typ) <- predList, let s=predArgs typ; y=mkVars (length s) ] )
 where
  d = defPred
  bsorts = sortsWithBottom sig
  sortList = Set.toList bsorts
  opList = [(f,t) | (f,types) <- Map.toList $ opMap sig,
                    t <- Set.toList types ]
  predList = [(p,t) | (p,types) <- Map.toList $ predMap sig,
                    t <- Set.toList types ]
  x = mkSimpleId "x"
  mkVars n = [mkSimpleId ("x_"++show i) | i<-[1..n]]

defined :: Set.Set SORT -> TERM f -> SORT -> Range -> FORMULA f
defined bsorts t s ps =
  if Set.member s bsorts then
     Predication (Qual_pred_name defPred (Pred_type [s] nullRange) nullRange) [t] ps
  else True_atom ps

defVards :: Set.Set SORT -> [VAR_DECL] -> FORMULA f
defVards bs [vs@(Var_decl [_] _ _)] = head $ defVars bs vs
defVards bs vs = Conjunction (concatMap (defVars bs) vs) nullRange
defVars :: Set.Set SORT -> VAR_DECL -> [FORMULA f]
defVars bs (Var_decl vns s _) = map (defVar bs s) vns
defVar :: Set.Set SORT -> SORT -> Token -> FORMULA f
defVar bs s v = defined bs (Qual_var v s nullRange) s nullRange

totalizeOpSymb :: OP_SYMB -> OP_SYMB
totalizeOpSymb o = case o of
                            Qual_op_name i (Op_type _ args res ps) qs ->
                                Qual_op_name i (Op_type Total args res ps) qs
                            _ -> o

totalizeConstraint :: Constraint -> Constraint
totalizeConstraint c =
    c { opSymbs = map ( \ (o, is) -> (totalizeOpSymb o, is)) $ opSymbs c }

totalRecord :: Set.Set SORT -> (f -> f) -> Record f (FORMULA f) (TERM f)
totalRecord bsrts mf = (mapRecord mf)
    { foldQuantification = \  _ q vs qf ps ->
      case q of
      Universal -> Quantification q vs (Implication (defVards bsrts vs) qf False ps) ps
      _ -> Quantification q vs (Conjunction [defVards bsrts vs, qf] ps) ps
    , foldDefinedness = \ _ t ps -> defined bsrts t (term_sort t) ps
    , foldExistl_equation = \ _ t1 t2 ps ->
      Conjunction[Strong_equation t1 t2 ps,
                  defined bsrts t1 (term_sort t1) ps] ps
    , foldMembership = \ _ t s ps -> if term_sort t == s
      then defined bsrts t s ps else error "totalizeFormula:Membership"
    , foldSort_gen_ax = \ _ cs b -> Sort_gen_ax (map totalizeConstraint cs) b
    , foldApplication = \ _ o args ps -> Application (totalizeOpSymb o) args ps
    , foldSorted_term = \ _ tr s _ ->
      if term_sort tr == s then tr else  error "totalizeFormula:Sorted_term"
    , foldCast = \ _ tr s _ ->
      if term_sort tr == s then tr else error "totalizeFormula:Cast"
    }

totalizeTerm :: Set.Set SORT -> (f -> f) -> TERM f -> TERM f
totalizeTerm bsrts = foldTerm . totalRecord bsrts

totalizeFormula :: Set.Set SORT -> (f -> f) -> FORMULA f -> FORMULA f
totalizeFormula bsrts = foldFormula . totalRecord bsrts

rmDefsRecord :: Set.Set SORT -> (f -> f) ->  Record f (FORMULA f) (TERM f)
rmDefsRecord  bsrts mf = (mapRecord mf)
    { foldDefinedness = \ _ t ps -> defined bsrts t (term_sort t) ps }

rmDefs :: Set.Set SORT -> (f -> f) -> FORMULA f -> FORMULA f
rmDefs bsrts = foldFormula . rmDefsRecord bsrts
