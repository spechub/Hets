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

import Common.Result
import Common.Id
import qualified Data.Set as Set

import Common.AS_Annotation
import Common.ProofTree

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

-- remove equivalences and implications, turn arbitrary junctions into binary ones
preprocessSen :: CASLFORMULA -> CASLFORMULA
preprocessSen sen = case sen of
 Relation sen1 Equivalence sen2 _ -> let -- remove equivalences
   sen1' = preprocessSen sen1
   sen2' = preprocessSen sen2
  in Junction Con [Junction Dis [Negation sen1' nullRange, sen2'] nullRange,
                   Junction Dis [Negation sen2' nullRange, sen1'] nullRange
                  ] nullRange
 Relation sen1 Implication sen2 _ -> let -- remove implications
   sen1' = preprocessSen sen1
   sen2' = preprocessSen sen2
  in Junction Dis [Negation sen1' nullRange, sen2'] nullRange
 Relation sen1 RevImpl sen2 _ -> let -- remove reverse implications
   sen1' = preprocessSen sen1
   sen2' = preprocessSen sen2
  in Junction Dis [Negation sen2' nullRange, sen1'] nullRange
 Junction j sens _ -> let -- only binary junctions
   sens' = map preprocessSen sens 
   bindLeft [] = Junction j [] nullRange
   bindLeft [x] = Junction j [x] nullRange 
   bindLeft [x,y] = Junction j [x,y] nullRange
   bindLeft (x:y:s') = Junction j [x, bindLeft (y:s')] nullRange
  in bindLeft sens'
 Quantification q vdecls qsen _ -> let -- recursion
   qsen' = preprocessSen qsen
  in Quantification q vdecls qsen' nullRange
 _ -> sen

-- function 2: computePNF
-- see page 292 in LPL.pdf
-- but instead of checking that a variable occurs free in a formula
-- I do a alpha renaming such that this property is ensured

computePNF :: Int -> CASLFORMULA -> (Int, CASLFORMULA)
computePNF n sen = case sen of
 Negation nsen _ -> let 
   (n', nsen') = computePNF n nsen
   (n'', nsen'') = case nsen' of
    Quantification q vdecls qsen _ -> -- deMorgan
       (n', Quantification (dualQuant q) vdecls (Negation qsen nullRange) nullRange)
    _ -> (n', Negation nsen' nullRange)
  in (n'', nsen'') 
 Junction j [sen1, sen2] _ -> let
   (n', sen1') = computePNF n sen1
   (n'', sen2') = computePNF n' sen2
   (n3, sen') = case (sen1', sen2') of 
     (Quantification q vdecls qsen _, aSen) -> let
         vars = flatVAR_DECLs vdecls
         (n''', vars') = getFreshVars vars n''
         vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
         qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $  
                        map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
         (n4, qsen'') = computePNF n''' (Junction j [qsen', aSen] nullRange)
        in (n4, Quantification q vdecls' qsen'' nullRange)
     (aSen, Quantification q vdecls qsen _) -> let
         vars = flatVAR_DECLs vdecls
         (n''', vars') = getFreshVars vars n''
         vdecls' = map (\(v,s) -> mkVarDecl v s) $ map fst vars'
         qsen' = foldl (\f (v,s,t)-> substitute v s t f) qsen $  
                        map (\((x,y),(z,t)) -> (z, t, Qual_var x y nullRange)) vars'
         (n4, qsen'') = computePNF n''' (Junction j [aSen, qsen'] nullRange)
        in (n4, Quantification q vdecls' qsen'' nullRange)
     _ -> (n'', Junction j [sen1', sen2'] nullRange)
  in (n3, sen')
 Quantification q vars qsen _ -> let 
   (n', qsen') = computePNF n qsen
  in (n', Quantification q vars qsen' nullRange) 
 _ -> (n, sen)

getFreshVars :: [(VAR,SORT)] -> Int -> (Int, [((VAR,SORT),(VAR,SORT))])
getFreshVars oldVars n = let 
  (n', newVars) = foldl (\(x, vs) (_, s) -> (x+1, (genNumVar "x" n, s):vs)) (n, []) $ oldVars
 in (n', zip newVars $ reverse oldVars)
  
mapTheory :: (CASLSign, [Named CASLFORMULA]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (sig, nsens) = do
 let sens = foldl (\sens0 s -> let (_, s') =  computePNF 0 $ preprocessSen s
                               in s':sens0) [] $ map sentence nsens
 return (sig, map (makeNamed "") sens)

