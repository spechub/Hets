{- |
Module      :  $Header$
Copyright   :  (c) Zicheng Wang, C.Maeder Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Coding out partiality (SubPCFOL= -> SubCFOL=), 
-}

module Comorphisms.CASL2SubCFOL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Data.List

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism 
import CASL.Sublogic hiding(bottom)
import CASL.Overload
import CASL.Fold
import CASL.Project
import CASL.Simplify
import Comorphisms.PCFOL2CFOL

-- | The identity of the comorphism
data CASL2SubCFOL = CASL2SubCFOL deriving (Show)

instance Language CASL2SubCFOL -- default definition is okay

instance Comorphism CASL2SubCFOL
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
    sourceLogic CASL2SubCFOL = CASL
    sourceSublogic CASL2SubCFOL = CASL_SL
                      { sub_features = Sub,
                        has_part = True,
                        cons_features = SortGen { emptyMapping = False,
                                                  onlyInjConstrs = False},
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2SubCFOL = CASL
    targetSublogic CASL2SubCFOL = CASL_SL
                      { sub_features = Sub,
                        has_part = False,  -- partiality is coded out
                        cons_features = SortGen { emptyMapping = False,
                                                  onlyInjConstrs = False},
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    mapSublogic CASL2SubCFOL sl = sl { has_part    = False
                                     , has_pred    = True
                                     , which_logic = FOL
                                     , has_eq      = True} 
    map_theory CASL2SubCFOL = mkTheoryMapping ( \ sig -> 
      let e = encodeSig sig in return (e, generateAxioms sig))
      (map_sentence CASL2SubCFOL)
    map_morphism CASL2SubCFOL mor = return 
      (mor  { msource =  encodeSig $ msource mor,
              mtarget =  encodeSig $ mtarget mor })
      -- other components need not to be adapted!
    map_sentence CASL2SubCFOL sig = return . codeFormula (sortSet sig)
    map_symbol CASL2SubCFOL = Set.singleton . id

-- | Add projections to the signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig = if Set.null bsorts then sig else 
    sig { opMap = projOpMap, predMap = newpredMap } where
   newTotalMap = Map.map (Set.map $ makeTotal Total) $ opMap sig
   botType x = OpType {opKind = Total, opArgs=[], opRes=x }
   bsorts = sortSet sig -- all sorts must be considered for as and in forms
   botTypes = Set.map botType bsorts
   botOpMap  = Map.insert bottom botTypes newTotalMap
   defType x = PredType{predArgs=[x]}
   defTypes = Set.map defType bsorts
   newpredMap = Map.insert defPred defTypes $ predMap sig
   rel = Rel.irreflex $ sortRel sig
   total (s, s') = OpType{opKind = Total, opArgs = [s'], opRes = s}
   setprojOptype = Set.map total $ Rel.toSet rel
   projOpMap = Set.fold ( \ t -> 
                          Map.insert (uniqueProjName $ toOP_TYPE t)
                        $ Set.singleton t) botOpMap setprojOptype

generateAxioms :: Sign () e -> [Named (FORMULA ())]
generateAxioms sig = filter (not . is_True_atom . sentence) $ 
  map (mapNamed $ simplifyFormula id . rmDefs bsorts id . renameFormula id) $
  concat(
    [inlineAxioms CASL
      " sort s < s'    \
      \ op pr : s'->s  \
      \ pred d:s       \
      \ forall x,y:s'. d(pr(x)) /\\ d(pr(y)) /\\ pr(x)=pr(y) => x=y \
      \ %(ga_projection_injectivity)% " 
    ++ inlineAxioms CASL
     " sort s < s'     \
      \ op pr : s'->s  \
      \ pred d:s       \
      \ forall x:s . d(x) => pr(x)=x     %(ga_projection)% " 
      | s <- sorts, let y =  mkSimpleId "y",
        s' <- minSupers s] ++
    [inlineAxioms CASL 
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
        x = mkSimpleId "x"
        pr = projName
        minSupers so = keepMinimals sig2 id $ Set.toList $ Set.delete so 
                           $ supersortsOf so sig2
        sorts = Set.toList $ sortSet sig
        sig2 = sig { sortRel = Rel.irreflex $ sortRel sig }
        d = defPred
        bsorts = sortSet sig
        sortList = Set.toList bsorts
        opList = [(f,t) | (f,types) <- Map.toList $ opMap sig,
                  t <- Set.toList types ]
        predList = [(p,t) | (p,types) <- Map.toList $ predMap sig,
                    t <- Set.toList types ]
        mkVars n = [mkSimpleId ("x_"++show i) | i<-[1..n]]

codeRecord :: Set.Set SORT -> (f -> f) -> Record f (FORMULA f) (TERM f)
codeRecord bsrts mf = (mapRecord mf)
    { foldQuantification = \  _ q vs qf ps ->
      case q of 
      Universal -> 
          Quantification q vs (Implication (defVards bsrts vs) qf False ps) ps
      _ -> Quantification q vs (Conjunction [defVards bsrts vs, qf] ps) ps
    , foldDefinedness = \ _ t ps -> defined bsrts t (term_sort t) ps
    , foldExistl_equation = \ _ t1 t2 ps ->
      Conjunction[Strong_equation t1 t2 ps,
                  defined bsrts t1 (term_sort t1) ps] ps
    , foldMembership = \ _ t s ps -> 
          defined bsrts (projectUnique Total ps t s) s ps
    , foldSort_gen_ax = \ _ cs b -> Sort_gen_ax (map totalizeConstraint cs) b
    , foldApplication = \ _ o args ps -> Application (totalizeOpSymb o) args ps
    , foldCast = \ _ t s ps -> projectUnique Total ps t s
    }

codeFormula :: Set.Set SORT -> FORMULA () -> FORMULA ()
codeFormula bsorts = foldFormula (codeRecord bsorts $ error "CASL2SubCFol")
