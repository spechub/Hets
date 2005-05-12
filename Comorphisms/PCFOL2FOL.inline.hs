{-                                                                          
Module:  $Header: /repository/HetCATS/Comorphisms/PFOL2FOL.inline.hs,      v 
1.20 2004/06/02 19:52:39 mnd Exp $                                            
Copyright   :  (c) Zicheng Wang, C. Maeder, Uni Bremen 2002-2005                         
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt          
                                                                               
Maintainer  :  hets@tzi.de                                                     
Stability   :  provisional                                                     
Portability :  portable                                                        
-}

{- todo
  generate axioms
  translate formulas
  optimize for total sigs
  translate morphisms (remove partiality)
-}

module Comorphisms.PCFOL2FOL where

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
import CASL.Sublogic hiding (bottom)
import CASL.Overload
import CASL.Simplify

-- | The identity of the comorphism
data PCFOL2FOL = PCFOL2FOL deriving (Show)

instance Language PCFOL2FOL -- default definition is okay

instance Comorphism PCFOL2FOL
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
    sourceLogic PCFOL2FOL = CASL
    sourceSublogic PCFOL2FOL = CASL_SL
                      { has_sub = False,
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic PCFOL2FOL = CASL
    targetSublogic PCFOL2FOL = CASL_SL
                      { has_sub = False, 
                        has_part = False, -- partiality is coded out
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    map_theory PCFOL2FOL = mkTheoryMapping ( \ sig ->
          let e = sig2FOL sig in return (e, generateFOLAxioms sig)) 
          (map_sentence PCFOL2FOL)
    map_morphism PCFOL2FOL m = return m
                { msource = sig2FOL $ msource m
                , mtarget = sig2FOL $ mtarget m
                , fun_map = Map.map (\ (i, _) -> (i, Total)) $ 
                            fun_map m }
    map_sentence PCFOL2FOL sig = 
        return . simplifyFormula id . totalizeFormula (sortsWithBottom sig) id
    map_symbol PCFOL2FOL s = 
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
 
generateFOLAxioms :: Eq f => Sign f e -> [Named(FORMULA f)]
generateFOLAxioms sig = filter ((/= True_atom []) . sentence) $ map 
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
      \ forall y_i:s_i . def f(y_i) => def y_k /\\ def y_k %(ga_stricntess)%"
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
  opList = [(f,t) | (f,types) <- Map.assocs $ opMap sig,
                    t <- Set.toList types ]
  predList = [(p,t) | (p,types) <- Map.assocs $ predMap sig,
                    t <- Set.toList types ]
  x = mkSimpleId "x"
  mkVars n = [mkSimpleId ("x_"++show i) | i<-[1..n]]

defined :: Set.Set SORT -> TERM f -> SORT -> [Pos] -> FORMULA f
defined bsorts t s ps =
  if Set.member s bsorts then  
     Predication (Qual_pred_name defPred (Pred_type [s] []) []) [t] ps
  else True_atom ps

defVards :: Set.Set SORT -> [VAR_DECL] -> FORMULA f
defVards bs [vs@(Var_decl [_] _ _)] = head $ defVars bs vs
defVards bs vs = Conjunction (concatMap (defVars bs) vs) []
defVars :: Set.Set SORT -> VAR_DECL -> [FORMULA f]
defVars bs (Var_decl vns s _) = map (defVar bs s) vns
defVar :: Set.Set SORT -> SORT -> Token -> FORMULA f
defVar bs s v = defined bs (Qual_var v s []) s []

totalizeTerm :: Set.Set SORT -> (f -> f) -> TERM f -> TERM f
totalizeTerm bsrts mf t = case t of
   Application o args ps -> 
       Application (totalizeOpSymb o) (map (totalizeTerm bsrts mf) args) ps
   Conditional t1 f t2 ps -> let
       t3 = totalizeTerm bsrts mf t1
       newF = totalizeFormula bsrts mf f
       t4 = totalizeTerm bsrts mf t2
       in Conditional t3 newF t4 ps 
   Sorted_term tr s _ | term_sort tr == s -> totalizeTerm bsrts mf tr
   Cast tr s _ | term_sort tr == s -> totalizeTerm bsrts mf tr
   Qual_var _ _ _ -> t
   _ -> error "PCFOL2CFOL.totalizeTerm"
   where totalizeOpSymb o = case o of 
                            Qual_op_name i (Op_type _ args res ps) qs -> 
                                Qual_op_name i (Op_type Total args res ps) qs
                            _ -> o

totalizeFormula :: Set.Set SORT -> (f -> f) -> FORMULA f -> FORMULA f
totalizeFormula bsrts mf form = case form of 
   Quantification q vs qf ps -> Quantification q vs 
       (Implication (defVards bsrts vs) (totalizeFormula bsrts mf qf) 
        False ps) ps
   Conjunction fs ps -> Conjunction (map (totalizeFormula bsrts mf) fs) ps
   Disjunction fs ps -> Disjunction (map (totalizeFormula bsrts mf) fs) ps
   Implication f1 f2 b ps -> let
       f3 = totalizeFormula bsrts mf f1
       f4 = totalizeFormula bsrts mf f2
       in Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = totalizeFormula bsrts mf f1
       f4 = totalizeFormula bsrts mf f2
       in Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = totalizeFormula bsrts mf nf
       in Negation newF ps
   Predication p args ps -> 
       let newArgs = map (totalizeTerm bsrts mf) args in
       Predication p newArgs ps
   Definedness t ps -> let 
       newT = totalizeTerm bsrts mf t
       srt = term_sort newT 
       in defined bsrts newT srt ps
   Existl_equation t1 t2 ps -> let
       t3 = totalizeTerm bsrts mf t1
       t4 = totalizeTerm bsrts mf t2
       in Conjunction[Strong_equation t3 t4 ps,
                      defined bsrts t3 (term_sort t3) ps] ps
   Strong_equation t1 t2 ps -> let
       t3 = totalizeTerm bsrts mf t1
       t4 = totalizeTerm bsrts mf t2
       in Strong_equation t3 t4 ps
   ExtFORMULA ef -> ExtFORMULA $ mf ef
   Membership t s ps | term_sort t == s -> True_atom ps
   Sort_gen_ax _ _ -> form
   True_atom _ -> form 
   False_atom _ -> form 
   _ -> error "PCFOL2CFOL.totalizeFormula"

rmDefs :: Set.Set SORT -> (f -> f) -> FORMULA f -> FORMULA f
rmDefs bsrts mf form = case form of 
   Quantification q vs qf ps -> Quantification q vs (rmDefs bsrts mf qf) ps
   Conjunction fs ps -> Conjunction (map (rmDefs bsrts mf) fs) ps
   Disjunction fs ps -> Disjunction (map (rmDefs bsrts mf) fs) ps
   Implication f1 f2 b ps -> let
       f3 = rmDefs bsrts mf f1
       f4 = rmDefs bsrts mf f2
       in Implication f3 f4 b ps
   Equivalence f1 f2 ps -> let
       f3 = rmDefs bsrts mf f1
       f4 = rmDefs bsrts mf f2
       in Equivalence f3 f4 ps
   Negation nf ps -> let
       newF = rmDefs bsrts mf nf
       in Negation newF ps
   Definedness t ps -> defined bsrts t (term_sort t) ps
   ExtFORMULA ef -> ExtFORMULA $ mf ef
   _ -> form 
