{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  skolemization as an institution comorphism
Copyright   :  (c) Mihai Codescu, 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codescu@iws.cs.uni-magdeburg.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Comorphism)

removing existential quantifiers from every formula
follows http://resources.mpi-inf.mpg.de/departments/rg1/teaching/autrea-ss10/script/lecture10.pdf

-}

module Comorphisms.CASL2Skolem where

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as SL hiding (bottom)
import CASL.Induction
import CASL.Quantification

import Common.Result
import Common.Id
import qualified Data.Set as Set
import Common.AS_Annotation
import Common.ProofTree
import qualified Common.Lib.MapSet as MapSet

import qualified Common.Lib.Rel as Rel

import Data.List(partition)

data CASL2Skolem = CASL2Skolem deriving Show

instance Language CASL2Skolem where
    language_name CASL2Skolem = "CASL2Skolem"
       
instance Comorphism CASL2Skolem
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
    sourceLogic CASL2Skolem = CASL
    sourceSublogic CASL2Skolem = SL.caslTop --TODO
    targetLogic CASL2Skolem = CASL
    mapSublogic CASL2Skolem sl = Just sl -- TODO
    map_theory CASL2Skolem = mapTheory
    map_morphism CASL2Skolem = error "nyi"
    map_sentence CASL2Skolem _ _ = error "nyi"
    map_symbol CASL2Skolem _ = Set.singleton . id
    has_model_expansion CASL2Skolem = True -- check
    is_weakly_amalgamable CASL2Skolem = True --check

mapTheory :: (CASLSign, [Named CASLFORMULA]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (sig, nsens) = do
 let sens = map sentence nsens
     (_, nsig, sens') = foldl (\(n, nsig0, sens0) sen -> 
                                 let (n', nsig', sen1) = skolemize n [] sig nsig0 $ miniscoping sig $ negationNormalForm sen 
                                 in (n', nsig', sen1:sens0)) (0, emptySign (), []) sens
     sig' = uniteCASLSign sig nsig
 return (sig', map (makeNamed "") sens')

-- variable renaming
-- such that they are all distinct

-- skipped this step for now, we don't get overlaps when translating from OWL

mkSkolemFunction :: Int -> Id
mkSkolemFunction x = 
 genName $ "sk_f" ++ show x

-- replace each variable from an argument list vars 
-- in a sentence sen'
-- with a new skolem function of arguments in a list fVars
-- the names are generated starting with a given number

replaceBoundVars :: [(VAR, SORT)] -> [(VAR, SORT)] -> Int -> CASLFORMULA -> (CASLSign, CASLFORMULA)
replaceBoundVars vars fVars n sen = let 
   -- for each variable that occurs free in sen, generate a new skolem function name
   fNames = map (mkSkolemFunction . snd) $ zip fVars $ [n..]
   -- for each such name, its arguments will be the types of vars and the result, the corresponding sort in fVars
   otypes = map (\x -> Op_type Total (map snd vars) x nullRange) $ map snd fVars
   -- now create the operation symbols with names in fNames and arity in otypes
   osyms = map (\(x, y) -> Qual_op_name x y nullRange) $ zip fNames otypes
   -- the arguments are the outer variables
   args = map (\(v,s) -> Qual_var v s nullRange) vars
   -- now create the term gn_sk_k(outerVariables)
   tms = map (\os -> Application os args nullRange) osyms
   substs = map (\((a,b),c) -> (a,b,c)) $ zip fVars tms
   sen' = foldl (\f (v,s,t)-> substitute v s t f) sen substs
   sign' = (emptySign ()) { 
               sortRel = foldl (\r x -> Rel.insertKey x r) Rel.empty $ map snd  $ vars ++ fVars,
               opMap = foldl (\m (f,o) -> MapSet.insert f (toOpType o) m) MapSet.empty $ zip fNames otypes 
            }
  in (sign', sen')

-- skolemization:
-- exists x H =>
-- H(f(y_1,...,y_n)/x)
-- where y_1, ..., y_n are free in exists x H
-- f is a new function symbol of arity n
skolemize :: Int -> [(VAR, SORT)] -> CASLSign -> CASLSign -> CASLFORMULA -> (Int, CASLSign, CASLFORMULA)
skolemize n outerFreeVars osig nsig sen = case sen of
 Quantification Existential vdecls sen1 _ -> let 
   vars = flatVAR_DECLs vdecls
   (n', nsig', sen') = skolemize n outerFreeVars osig nsig sen1 
   --fVars = freeVars osig sen'
   n'' =  n' + (length vars) 
   (nsig0, sen'') = replaceBoundVars outerFreeVars vars n sen'
   nsig'' = uniteCASLSign nsig' nsig0
  in (n'', nsig'', sen'') 
 Quantification q vars sen1 _ -> let (n', nsig', sen') = skolemize n (outerFreeVars ++ flatVAR_DECLs vars) osig nsig sen1 in 
                                 (n', nsig', Quantification q vars sen' nullRange)
 Junction j sens _ -> let
   (n', nsig', sens') = foldl (\(x, nsig0, sens0) s -> let (y, nsig1, s') = skolemize x outerFreeVars osig nsig0 s
                                                       in (y, uniteCASLSign nsig1 nsig0, s':sens0))
                       (n, nsig, []) sens
  in (n', nsig', Junction j sens' nullRange) 
 Relation sen1 rel sen2 _ -> let 
   (n', nsig', sen') = skolemize n outerFreeVars osig nsig sen1
   (n'', nsig'', sen'') = skolemize n' outerFreeVars osig nsig' sen2
  in (n'', nsig'', Relation sen' rel sen'' nullRange)
 Negation sen1 _ -> let (n', nsig', sen') = skolemize n outerFreeVars osig nsig sen1 in 
                    (n', nsig', Negation sen' nullRange)
 x -> (n, nsig, x) 

-- nnf, implemented recursively

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

-- miniscoping: 
-- Qx(G and F) => QxG and F
-- Qx(G or F) => QxG or F
-- forall x (G and H) => (forall x G) and (forall x H)
-- exists x (G or H) => (exists x G) or (exists x H)
-- where x occurs freely in G, H
-- but not in F

miniscoping :: CASLSign -> CASLFORMULA -> CASLFORMULA
miniscoping sig sen = case sen of
 Quantification q vdecls (Junction j sens _) _ -> 
   let 
    vars = Set.fromList $ flatVAR_DECLs vdecls 
    (sensVarsFree, sensNoVars) = partition (\s -> let svars = freeVars sig s in (svars /= Set.difference svars vars)) sens
    sensVarsFree' = map (miniscoping sig) sensVarsFree
    sensNoVars' = map (miniscoping sig) sensNoVars
   in case (q, j) of
       (Existential, Con) -> 
         Junction Con ((Quantification Existential vdecls (Junction Con sensVarsFree' nullRange) nullRange):sensNoVars') 
                  nullRange
       (Existential, Dis) -> 
         Junction Dis ((map (\s -> Quantification Existential vdecls s nullRange) sensVarsFree') ++ sensNoVars') nullRange
       (Universal, Con) ->  
         Junction Con ((map (\s -> Quantification Universal vdecls s nullRange) sensVarsFree') ++ sensNoVars') nullRange
       (Universal, Dis) ->
         Junction Dis ((Quantification Universal vdecls (Junction Dis sensVarsFree' nullRange) nullRange):sensNoVars') nullRange
       _ -> error "miniscoping nyi for exists uniquely"
 Quantification q vdecls qsen _ -> Quantification q vdecls (miniscoping sig qsen) nullRange
 Junction j sens _ -> Junction j (map (miniscoping sig) sens) nullRange
 Relation sen1 rel sen2 _ -> Relation (miniscoping sig sen1) rel (miniscoping sig sen2) nullRange
 Negation nsen _ -> Negation (miniscoping sig nsen) nullRange
 x -> x


