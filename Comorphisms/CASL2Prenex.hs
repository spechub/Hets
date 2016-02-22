{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  prenex normal form for sentences of a CASL theory
Copyright   :  (c) Mihai Codescu, 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codescu@iws.cs.uni-magdeburg.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Comorphism)

as described in 
http://resources.mpi-inf.mpg.de/departments/rg1/teaching/autrea-ss10/script/lecture10.pdf

-}

module Comorphisms.CASL2Prenex where

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as SL hiding (bottom)
import CASL.Induction
import CASL.Quantification
import CASL.ToDoc

import Common.Result
import Common.Id
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.AS_Annotation
import Common.ProofTree
import qualified Common.Lib.MapSet as MapSet

import qualified Common.Lib.Rel as Rel

import Data.List(partition)

import Debug.Trace

data CASL2Prenex = CASL2Prenex deriving Show

instance Language CASL2Prenex where
    language_name CASL2Prenex = "CASL2Prenex"
       
instance Comorphism CASL2Prenex
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree where
    sourceLogic CASL2Prenex = CASL
    sourceSublogic CASL2Prenex = SL.caslTop --TODO
    targetLogic CASL2Prenex = CASL
    mapSublogic CASL2Prenex sl = Just sl -- TODO
    map_theory CASL2Prenex = mapTheory
    map_morphism CASL2Prenex = error "nyi"
    map_sentence CASL2Prenex _ _ = error "nyi"
    map_symbol CASL2Prenex _ = Set.singleton . id
    has_model_expansion CASL2Prenex = True -- check
    is_weakly_amalgamable CASL2Prenex = True --check

-- rules:
-- 1. F <-> G becomes F -> G and G -> F
-- 2. not (Q x . F) becomes (dual Q) x . not F
-- 3. (Q x . F) conn G becomes
-- Q y . (F[y/x] conn G) 
-- where y is fresh, conn is /\ or \/
-- 4. (Q x .F) => G becomes
-- (dual Q) y . (F[y/x] => G)
-- where y is fresh
-- 5. F conn (Q x . G) becomes
-- Q y (F conn G[y/x])
-- with y fresh and conn in {/\,\/,->}  

-- starting index for fresh variables
-- signature
-- formula that we compute normal form of
prenexNormalForm :: Int -> CASLSign -> CASLFORMULA -> (Int,CASLFORMULA)
prenexNormalForm n sig sen = case sen of
 -- this covers 1. 
 Relation sen1 Equivalence sen2 _ -> let sen1' = Relation sen1 Implication sen2 nullRange
                                         sen2' = Relation sen2 Implication sen1 nullRange 
                                     in trace "1" $ prenexNormalForm n sig $ Junction Con [sen1', sen2'] nullRange
 -- this covers 2.
 Negation (Quantification q vdecls qsen _) _ -> let 
   (n', qsen') = prenexNormalForm n sig $ Negation qsen nullRange
  in trace "2" $ (n', Quantification (dualQuant q) vdecls qsen' nullRange)
 -- in the remanining cases for negation, apply recursion
 Negation nsen _ -> let 
   (n', nsen') = prenexNormalForm n sig nsen
  in trace "ng rec" $ (n', Negation nsen' nullRange)
 -- this covers 3.
 Junction j ((Quantification q vdecls qsen _):sens) _ -> 
   let 
       vars = flatVAR_DECLs vdecls 
       (n', vars') = getFreshVars vars n
       vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
       qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $ map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
       (n'', jsen) = trace "4" $ prenexNormalForm n' sig $ Junction j (qsen':sens) nullRange
    in trace "3" $ (n'', Quantification q vdecls' jsen nullRange)
 -- this covers 5. for conjunction and disjunction
 Junction j (nqsen:(Quantification q vdecls qsen _):sens) _ -> let
   vars = flatVAR_DECLs vdecls
   (n', vars') = getFreshVars vars n'
   vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
   qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $ map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
   (n'', jsen) = prenexNormalForm n' sig $ 
                   Junction j (qsen':sens) nullRange
  in trace "5 conj & disj" $ (n'', Quantification q vdecls' jsen nullRange)
 -- don't forget recursion for other cases 
 Junction j jsens _ -> let 
   (n', jsens') = foldl (\(x,sens0) s -> let (x',s') = prenexNormalForm x sig s 
                                       in (x', s':sens0)) 
                     (n, []) jsens
   (n'', sen') = prenexNormalForm n' sig $ Junction j jsens' nullRange
  in trace "junction recursion" $ (n'', sen')
 -- both two next cases cover 4.
 Relation (Quantification q vdecls qsen _) Implication sen2 _ -> let
   vars = flatVAR_DECLs vdecls 
   (n', vars') = getFreshVars vars n
   vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
   qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $ map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
  in trace "4.1" $  prenexNormalForm n' sig $ Quantification (dualQuant q) vdecls' (Relation qsen' Implication sen2 nullRange) nullRange
 Relation sen1 RevImpl (Quantification q vdecls qsen _) _ -> let
   vars = flatVAR_DECLs vdecls
   (n', vars') = getFreshVars vars n
   vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
   qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $ map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
  in trace "4.2" $ prenexNormalForm n' sig $ Quantification (dualQuant q) vdecls' (Relation sen1 RevImpl qsen' nullRange) nullRange 
 -- next two cases cover 5. for implication
 Relation sen1 Implication (Quantification q vdecls qsen _) _ -> let
   vars = flatVAR_DECLs vdecls
   (n', vars') = getFreshVars vars n'
   vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
   qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $ map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
  in trace "5.1" $ prenexNormalForm n' sig $ Quantification q vdecls' (Relation sen1 Implication qsen' nullRange) nullRange
 Relation (Quantification q vdecls qsen _) RevImpl sen2 _ -> let
   vars = flatVAR_DECLs vdecls
   (n', vars') = getFreshVars vars n
   vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
   qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $ map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
  in trace "5.2" $ prenexNormalForm n' sig $ Quantification q vdecls' (Relation qsen' RevImpl sen2 nullRange) nullRange
 -- recursion for other cases
 Relation sen1 rel sen2 _ -> let
   (n', sen1')  = prenexNormalForm n sig sen1
   (n'', sen2') = prenexNormalForm n' sig sen2
  in trace ("recursion impl") $ prenexNormalForm n'' sig $ Relation sen1' rel sen2' nullRange  
 Quantification q vars qsen _ -> let 
   (n', qsen') = prenexNormalForm n sig qsen
  in trace "recursion quant" $ (n', Quantification q vars qsen' nullRange) 
 -- for atoms and similars, do nothing
 x -> trace "atoms" $ (n, x)

getFreshVars :: [(VAR,SORT)] -> Int -> (Int, [((VAR,SORT),(VAR,SORT))])
getFreshVars oldVars n = let 
  (n', newVars) = foldl (\(x, vs) (v, s) -> (n+1, (genNumVar "x" n, s):vs)) (n, []) $ oldVars
 in (n', zip newVars $ reverse oldVars)
  
mapTheory :: (CASLSign, [Named CASLFORMULA]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (sig, nsens) = do
 let sens = foldl (\sens0 s -> let (_, s') = trace (show $ negationNormalForm s) $ prenexNormalForm 0 sig $ negationNormalForm s -- no sense to call miniscope here
                               in s':sens0) [] $ map sentence nsens
 return (sig, map (makeNamed "") sens)


-- this should go some place where it's available for all comorphisms 
negationNormalForm :: CASLFORMULA -> CASLFORMULA
negationNormalForm sen = case sen of
 Quantification q vars qsen _ -> Quantification q vars (negationNormalForm qsen) nullRange 
 Junction j sens _ -> Junction j (map negationNormalForm sens) nullRange 
 Relation sen1 Implication sen2 _ -> let sen1' = negationNormalForm $ Negation (negationNormalForm sen1) nullRange
                                         sen2' = negationNormalForm sen2
                                     in Junction Dis [sen1', sen2'] nullRange
 Relation sen1 RevImpl sen2 _ -> let sen2' = negationNormalForm $ Negation (negationNormalForm sen2) nullRange
                                     sen1' = negationNormalForm sen1
                                 in Junction Dis [sen1', sen2'] nullRange
 Relation sen1 Equivalence sen2 _ -> let sen1' = Relation sen1 Implication sen2 nullRange
                                         sen2' = Relation sen2 Implication sen1 nullRange 
                                     in negationNormalForm $ Junction Con [sen1', sen2'] nullRange 
 Negation (Negation sen' _) _ -> negationNormalForm sen'
 Negation (Junction Con sens _) _ -> Junction Dis (map (\x -> negationNormalForm $ Negation x nullRange) sens) nullRange
 Negation (Junction Dis sens _) _ -> Junction Con (map (\x -> negationNormalForm $ Negation x nullRange) sens) nullRange
 Negation (Quantification Unique_existential _vars _sen _) _-> error "nyi"
 Negation (Quantification q vars qsen _) _ -> Quantification (dualQuant q) vars (negationNormalForm $ Negation qsen nullRange) nullRange
 x -> x
