{- |
Module      :  $Header$
Copyright   :  (c) Zicheng Wang, C.Maeder Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Coding out subsorting (SubPCFOL= -> PCFOL=),
   following Chap. III:3.1 of the CASL Reference Manual
-}

module Comorphisms.CASL2PCFOL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Data.List

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as Sublogic
import CASL.Inject
import CASL.Project
import CASL.Overload
import CASL.StaticAna

-- | The identity of the comorphism
data CASL2PCFOL = CASL2PCFOL deriving (Show)

instance Language CASL2PCFOL -- default definition is okay

instance Comorphism CASL2PCFOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol Q_ProofTree
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol Q_ProofTree where
    sourceLogic CASL2PCFOL = CASL
    sourceSublogic CASL2PCFOL = Sublogic.caslTop
    targetLogic CASL2PCFOL = CASL
    mapSublogic CASL2PCFOL sl = Just $
                                if has_sub sl then -- subsorting is coded out
                                      sl { sub_features = NoSub
                                         , has_part    = True
                                         , which_logic = max Horn
                                                         $ which_logic sl
                                         , has_eq      = True}
                                  else sl
    map_theory CASL2PCFOL = mkTheoryMapping ( \ sig ->
      let e = encodeSig sig in
      return (e, monotonicities sig ++ generateAxioms sig))
      (map_sentence CASL2PCFOL)
    map_morphism CASL2PCFOL mor = return
      (mor  { msource = encodeSig $ msource mor,
              mtarget = encodeSig $ mtarget mor })
      -- other components need not to be adapted!
    map_sentence CASL2PCFOL _ = return . f2Formula
    map_symbol CASL2PCFOL = Set.singleton . id
    has_model_expansion CASL2PCFOL = True
    is_weakly_amalgamable CASL2PCFOL = True

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig
  = if Rel.null rel then sig else
      sig{sortRel = Rel.empty, opMap = projOpMap}
  where
        rel = sortRel sig
        total (s, s') = OpType{opKind = Total, opArgs = [s], opRes = s'}
        partial (s, s') = OpType{opKind = if Rel.member s' s rel
                                 then Total
                                 else Partial, opArgs = [s'], opRes = s}
        setinjOptype = Set.map total $ Rel.toSet rel
        setprojOptype = Set.map partial $ Rel.toSet rel
        injOpMap = Set.fold (\ t -> addOpTo (uniqueInjName $ toOP_TYPE t) t)
          (opMap sig) setinjOptype
        projOpMap = Set.fold (\ t -> addOpTo (uniqueProjName $ toOP_TYPE t) t)
          injOpMap setprojOptype
    -- membership predicates are coded out

generateAxioms :: Sign f e -> [Named (FORMULA ())]
generateAxioms sig = map (mapNamed $ renameFormula id) $ concat $
      [inlineAxioms CASL
     "  sorts s, s' \
      \ op inj : s->s' \
      \ forall x,y:s . inj(x)=e=inj(y) => x=e=y  %(ga_embedding_injectivity)% "
    ++ inlineAxioms CASL
      " sort s, s' \
      \ op pr : s'->?s \
      \ forall x,y:s'. pr(x)=e=pr(y)=>x=e=y   %(ga_projection_injectivity)% "
    ++ inlineAxioms CASL
     " sort s, s' \
      \ op pr : s'->?s ; inj:s->s' \
      \ forall x:s . pr(inj(x))=e=x             %(ga_projection)% "
      | s <- sorts,
        s' <- realSupers s]
   ++ [inlineAxioms CASL
     " sort s, s', s'' \
      \ op inj:s'->s'' ; inj: s->s' ; inj:s->s'' \
      \ forall x:s . inj(inj(x))=e=inj(x)      %(ga_transitivity)% "
          | s <- sorts,
            s' <- realSupers s,
            s'' <- realSupers s',
            s'' /= s]
   ++ [inlineAxioms CASL
     " sort s, s' \
      \ op inj:s->s' ; inj: s'->s \
      \ forall x:s . inj(inj(x))=e=x      %(ga_identity)% "
          | s <- sorts,
            s' <- realSupers s,
            Set.member s $ supersortsOf s' sig]
    where
        x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = injName
        pr = projName
        realSupers so = Set.toList $ supersortsOf so sig
        sorts = Set.toList $ sortSet sig

monotonicities :: Sign f e -> [Named (FORMULA f)]
monotonicities sig =
    concatMap (makeMonos sig) (Map.toList $ opMap sig)
    ++ concatMap (makePredMonos sig) (Map.toList $ predMap sig)

makeMonos :: Sign f e -> (Id, Set.Set OpType) -> [Named (FORMULA f)]
makeMonos sig (o, ts) = makeEquivMonos o sig $ Set.toList ts

makePredMonos :: Sign f e -> (Id, Set.Set PredType) -> [Named (FORMULA f)]
makePredMonos sig (p, ts) = makeEquivPredMonos p sig $ Set.toList ts

makeEquivMonos :: Id -> Sign f e -> [OpType] -> [Named (FORMULA f)]
makeEquivMonos o sig ts =
  case ts of
  [] -> []
  t : rs -> concatMap (makeEquivMono o sig t) rs ++
            makeEquivMonos o sig rs

makeEquivPredMonos :: Id -> Sign f e -> [PredType] -> [Named (FORMULA f)]
makeEquivPredMonos o sig ts =
  case ts of
  [] -> []
  t : rs -> concatMap (makeEquivPredMono o sig t) rs ++
            makeEquivPredMonos o sig rs

makeEquivMono :: Id -> Sign f e -> OpType -> OpType -> [Named (FORMULA f)]
makeEquivMono o sig o1 o2 =
      let rs = minimalSupers sig (opRes o1) (opRes o2)
          a1 = opArgs o1
          a2 = opArgs o2
          args = if length a1 == length a2 then
                 combine $ zipWith (maximalSubs sig) a1 a2
                 else []
      in concatMap (makeEquivMonoRs o o1 o2 rs) args

makeEquivMonoRs :: Id -> OpType -> OpType ->
                   [SORT] -> [SORT] -> [Named (FORMULA f)]
makeEquivMonoRs o o1 o2 rs args = map (makeEquivMonoR o o1 o2 args) rs

makeEquivMonoR :: Id -> OpType -> OpType ->
                  [SORT] -> SORT -> Named (FORMULA f)
makeEquivMonoR o o1 o2 args res =
    let vds = zipWith (\ s n -> Var_decl [mkSelVar "x" n] s nullRange)
              args [1..]
        inject = injectUnique nullRange
        a1 = zipWith (\ v s -> inject (toQualVar v) s) vds $ opArgs o1
        a2 = zipWith (\ v s -> inject (toQualVar v) s) vds $ opArgs o2
        t1 = inject (Application (Qual_op_name o (toOP_TYPE o1)
                                            nullRange) a1 nullRange) res
        t2 = inject (Application (Qual_op_name o (toOP_TYPE o2)
                                            nullRange) a2 nullRange) res
    in makeNamed "ga_function_monotonicity" $ mkForall vds
           (Existl_equation t1 t2 nullRange) nullRange

makeEquivPredMono :: Id -> Sign f e -> PredType -> PredType
                  -> [Named (FORMULA f)]
makeEquivPredMono o sig o1 o2 =
      let a1 = predArgs o1
          a2 = predArgs o2
          args = if length a1 == length a2 then
                 combine $ zipWith (maximalSubs sig) a1 a2
                 else []
      in map (makeEquivPred o o1 o2) args

makeEquivPred :: Id -> PredType -> PredType -> [SORT] -> Named (FORMULA f)
makeEquivPred o o1 o2 args =
    let vds = zipWith (\ s n -> Var_decl [mkSelVar "x" n] s nullRange)
              args [1..]
        inject = injectUnique nullRange
        a1 = zipWith (\ v s -> inject (toQualVar v) s) vds $ predArgs o1
        a2 = zipWith (\ v s -> inject (toQualVar v) s) vds $ predArgs o2
        t1 = Predication (Qual_pred_name o (toPRED_TYPE o1) nullRange) a1
             nullRange
        t2 = Predication (Qual_pred_name o (toPRED_TYPE o2) nullRange) a2
             nullRange
    in makeNamed "ga_predicate_monotonicity" $ mkForall vds
           (Equivalence t1 t2 nullRange) nullRange


f2Formula :: FORMULA f -> FORMULA f
f2Formula = projFormula Partial id . injFormula id
