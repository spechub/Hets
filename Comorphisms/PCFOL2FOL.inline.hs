{-                                                                          
Module:  $Header: /repository/HetCATS/Comorphisms/PFOL2FOL.inline.hs,      v 
1.20 2004/06/02 19:52:39 mnd Exp $                                            
Copyright   :  (c) Zicheng Wang, Uni Bremen 2002-2004                         
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

--import Test
import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
--import Comorphisms.CASL2PCFOL


--CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic
import CASL.Overload
import List (nub,delete)
import Common.ListUtils
import Data.List


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
    map_sign PCFOL2FOL sig = 
      let e = sig2FOL sig in return (e, generateFOLAxioms sig)
    map_morphism PCFOL2FOL = return . id
    map_sentence PCFOL2FOL sig = return . mapSen
    map_symbol PCFOL2FOL = Set.single . id


sig2FOL::Sign f e-> Sign f e
sig2FOL  sig =sig {opMap=newOpMap,predMap=newpredMap }
 where
   sig2sort=Set.toList(sortSet sig)
   undef x = OpType{opKind = Total, opArgs=[],opRes=x}
   setundef = Set.fromList (map undef sig2sort)
   map2list = Map.toList(opMap sig)
   set2list = map (\(x,y)->(x,Set.toList y)) map2list
   par2total [] = []
   par2total (x:xs) = if ((opKind x)==Partial) then  (x{opKind=Total}):(par2total xs) else  x:(par2total xs)
   newTotalMap =Map.fromList [(x,Set.fromList(par2total y))|(x,y)<-set2list]
   newOpMap  = Map.insert bottom setundef newTotalMap
   undefpred x = PredType{predArgs=[x]}
   setundefpred = Set.fromList(map undefpred sig2sort)
   newpredMap = Map.insert defPred setundefpred (predMap sig)

bottom = mkId[mkSimpleId "_bottom"]
defPred = mkId[mkSimpleId "_D"]
 
generateFOLAxioms :: Sign f e -> [Named(FORMULA f)]
--generateFOLAxioms _ = []
generateFOLAxioms sig = 
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
        | s<-sortList ] ++
    [inlineAxioms CASL 
      " sort t             \
      \ sorts s_i          \
      \ sorts s_k          \
      \ op f:s_i->t     \
      \ preds d:t; d:s_i; d:s_k        \
      \ var y_k:s_k             \
      \ forall y_i:s_i . d(f(y_i)) <=> d(y_k) /\\ d(y_k) %(ga_totality)%"
        | (f,typ) <- opList, opKind typ == Total,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL 
      " sort t             \
      \ sorts s_i          \
      \ sorts s_k          \
      \ op f:s_i->t     \
      \ preds d:t; d:s_i; d:s_k        \
      \ var y_k:s_k             \
      \ forall y_i:s_i . d(f(y_i)) => d(y_k) /\\ d(y_k) %(ga_stricntess)%"
        | (f,typ) <- opList, opKind typ == Partial,
          let s=opArgs typ; t=opRes typ; y= mkVars (length s) ] ++
    [inlineAxioms CASL 
      " sorts s_i          \
      \ sorts s_k          \
      \ pred p:s_i     \
      \ preds d:s_i; d:s_k        \
      \ var y_k:s_k             \
      \ forall y_i:s_i . p(y_i) => d(y_k) /\\ d(y_k) %(ga_predicate_strictness)%"
        | (p,typ) <- predList, let s=predArgs typ; y=mkVars (length s) ] ) 
 where 
  d = defPred
  sortList = Set.toList (sortSet sig)
  opList = [(f,t) | (f,types) <- Map.assocs $ opMap sig,
                    t <- Set.toList types ]
  predList = [(p,t) | (p,types) <- Map.assocs $ predMap sig,
                    t <- Set.toList types ]
  x = mkSimpleId "x"
  bottom = mkId [mkSimpleId "_bottom"]
  mkVars n = [mkSimpleId ("x_"++show i) | i<-[1..n]]

defined t s ps =
  Predication (Qual_pred_name defPred (Pred_type [s] []) []) [t] ps

defVards [vs@(Var_decl [v] s _)] = head $ defVars vs
defVards vs = Conjunction (concatMap defVars vs) []
defVars (Var_decl vns s _) = map (defVar s) vns
defVar s v = defined (Qual_var v s []) s []

mapSen :: FORMULA f -> FORMULA f
mapSen f = case f of
    Quantification q vs frm ps -> 
       Implication (defVards vs) (Quantification q vs (mapSen frm) ps) False ps
    Conjunction fs ps -> Conjunction (map mapSen fs) ps
    Disjunction fs ps -> Disjunction (map mapSen fs) ps
    Implication f1 f2 b ps -> Implication (mapSen f1) (mapSen f2) b ps
    Equivalence f1 f2 ps -> Equivalence (mapSen f1) (mapSen f2) ps
    Negation frm ps -> Negation (mapSen frm) ps
    True_atom ps -> True_atom ps
    False_atom ps -> False_atom ps
    Existl_equation t1 t2 ps ->
       Conjunction[Strong_equation t1 t2 ps,
                   defined t1 (term_sort t1) ps] ps
    Strong_equation t1 t2 ps -> Strong_equation t1 t2 ps
    Predication pn ts qs -> Predication pn ts qs
    Definedness t ps -> defined t (term_sort t) ps
    Membership t ty ps -> error "PCFOL2FOL: no subsorted formula allowed"
    Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
    _ -> error "PCFOL2FOL: wrong formula type"

