{- 
Module      :  $Header$
Copyright   :  (c) Zicheng Wang, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Coding out subsorting (SubPCFOL= -> PCFOL=), 
   following Chap. III:3.1 of the CASL Reference Manual
-}

{-
   todo
   predicate_monotonicity  (wie function_monotonicty)
   encodeFORMULA
   treat inj(u_i) separately
   map_morphism should modify sort_map etc.
   map_sign should avoid to generate OpNames with empty set of profiles
-}

module Comorphisms.CASL2PCFOL where

--import Test
import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism 
import CASL.Sublogic
import CASL.Inject
import CASL.Project
import CASL.Overload
import Common.ListUtils
import Data.List

-- | The identity of the comorphism
data CASL2PCFOL = CASL2PCFOL deriving (Show)

instance Language CASL2PCFOL -- default definition is okay

instance Comorphism CASL2PCFOL
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
    sourceLogic CASL2PCFOL = CASL
    sourceSublogic CASL2PCFOL = CASL_SL
                      { has_sub = True,
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2PCFOL = CASL
    targetSublogic CASL2PCFOL = CASL_SL
                      { has_sub = False, -- subsorting is coded out
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    map_theory CASL2PCFOL = mkTheoryMapping ( \ sig -> 
      let e = encodeSig sig in return (e, generateAxioms sig))
      (map_sentence CASL2PCFOL)
    map_morphism CASL2PCFOL mor = return 
      (mor  { msource =  encodeSig $ msource mor,
              mtarget =  encodeSig $ mtarget mor })
      -- other components need to be adapted as well!
    map_sentence CASL2PCFOL _ = return . f2Formula
    map_symbol CASL2PCFOL = Set.single . id

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig = if Rel.isEmpty rel then sig -- nothing to do
    else sig {sortRel = Rel.empty, opMap = projOpMap }
    where 
    rel = Rel.irreflex $ sortRel sig
    relList = Rel.toList $ Rel.union rel $ Rel.fromList
              $ map ( \ s -> (s, s)) $ Set.toList $ sortSet sig
              -- we need identity injections for monotonicity formulas
    total (s, s') = OpType {opKind=Total,opArgs=[s],opRes=s'}
    partial (s, s') = OpType {opKind=Partial,opArgs=[s'],opRes=s} 
    setinjOptype = Set.fromList(map total relList)  
    setprojOptype = Set.fromList (map partial $ Rel.toList rel)  
    injOpMap = Map.insert injName setinjOptype (opMap sig) 
    projOpMap = Map.insert projName setprojOptype (injOpMap)  
    -- membership predicates are coded out

generateAxioms :: Sign f e -> [Named (FORMULA f)]
generateAxioms sig = 
  concat 
  ([inlineAxioms CASL
     "  sorts s < s' \
      \ op inj : s->s' \
      \ forall x,y:s . inj(x)=inj(y) => x=y   %(ga_embedding_injectivity)% "
    ++ inlineAxioms CASL
     " sort s< s' \
      \ op pr : s'->?s ; inj:s->s' \
      \ forall x:s . pr(inj(x))=x             %(ga_projection)% " 
    ++ inlineAxioms CASL
      " sort s<s' \
      \ op pr : s'->?s \
      \ forall x,y:s'. pr(x)=e=pr(y)=>x=e=y   %(ga_projection_injectivity)% " 
      | (s,s') <- rel2List]                         
    ++ [inlineAxioms CASL
      " sort s \
      \ op inj : s->s \
      \ forall x:s . inj(x)=x                 %(ga_identity)%" 
          | s <- Set.toList $ sortSet sig]
   ++ [inlineAxioms CASL
     " sort s<s';s'<s'' \
      \ op inj:s'->s'' ; inj: s->s' ; inj:s->s'' \
      \ forall x:s . inj(inj(x))=inj(x)      %(ga_transitivity)% "  
          |(s,s')<-rel2List, s'' <- Set.toList(supersortsOf s' sig),
           s' /= s'']
   ++ [inlineAxioms CASL
    " sort s'<s ; s''<s ; w'_i ; w''_i ; w_i; w_j  \
    \ ops f:w'_i->s' ; f:w''_i->s'' ; \
    \     inj: s' -> s ; inj: s''->s ; inj: w_i->w'_i ; inj:w_i -> w''_i  \
    \ var u_j : w_i   \
    \ forall u_i : w_i . \
    \ inj((op f:w'_i->s')(inj(u_j)))=inj((op f:w''_i->s'')(inj(u_j))) \
    \                                           %(ga_function_monotonicity)%"
    
          |(f,l)<- ftTL, t1<-l,t2<-l, t1 < t2, leqF sig t1 t2,
           let w' = opArgs t1, let w'' = opArgs t2,
           let s' = opRes t1, let s'' = opRes t2,
           s<-Set.toList $ common_supersorts sig s' s'',
           w<- permute $ map findsubsort $ zip w' w'',
           let u = [mkSimpleId ("u"++show i) | i<-[1..length w]]]
   ++ [inlineAxioms CASL                                 
    " sort w'_i ; w''_i ; w_i  \ 
    \ pred p: w'_i;  pred p: w''_i;  \
    \ ops inj:w_i->w'_i;   inj:w_i->w''_i \ 
    \ forall  v_i:w_i . (pred p:w'_i)(inj(v_i)) <=> (pred p:w''_i)(inj(v_i)) \
    \                                           %(ga_predicate_monotonicity)%"
        | (p,l)<-pred2List, t1<-l, t2<-l, t1<t2, 
          leqP sig t1 t2,
          let w'= predArgs t1, let w''= predArgs t2, 
          w<-permute $ map findsubsort $ zip w' w'',
          let v = [mkSimpleId ("v"++show i) | i<-[1..length w]] ]) 
    where 
        x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = injName
        pr = projName
        rel2List=Rel.toList $ Rel.irreflex $ sortRel sig
        pred2List = map (\(i, ps)->(i, Set.toList ps)) 
                    $ Map.toList $ predMap sig
        findsubsort (a, b) = Set.toList $ common_subsorts sig a b
        ftTL = map (\(i, os) -> (i, Set.toList os)) 
               $ Map.toList $ opMap sig


f2Formula :: FORMULA f -> FORMULA f
f2Formula = projFormula id . injFormula id 
