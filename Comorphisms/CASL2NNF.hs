{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  negation normal form
Copyright   :  (c) Mihai Codescu, 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codescu@iws.cs.uni-magdeburg.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Comorphism)

-}

module Comorphisms.CASL2NNF where

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic as SL hiding (bottom)

import Common.Result
import Common.Id
import qualified Data.HashSet as Set
import Common.AS_Annotation
import Common.ProofTree

data CASL2NNF = CASL2NNF deriving Show

instance Language CASL2NNF where
    language_name CASL2NNF = "CASL2NNF"

instance Comorphism CASL2NNF
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
    sourceLogic CASL2NNF = CASL
    sourceSublogic CASL2NNF = SL.caslTop
    targetLogic CASL2NNF = CASL
    mapSublogic CASL2NNF sl = if SL.which_logic sl == SL.Horn 
                                then Just $ sl {SL.which_logic = SL.FOL}
                                else Just sl
    map_theory CASL2NNF = mapTheory
    map_morphism CASL2NNF = return -- morphisms are mapped identically
    map_sentence CASL2NNF _ s = return $ negationNormalForm s
    map_symbol CASL2NNF _ = Set.singleton . id
    has_model_expansion CASL2NNF = True
    is_weakly_amalgamable CASL2NNF = True

mapTheory :: (CASLSign, [Named CASLFORMULA]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (sig, nsens) = do
 return (sig, map (\nsen -> nsen{sentence = negationNormalForm $ sentence nsen}) nsens)

-- nnf, implemented recursively

negationNormalForm :: CASLFORMULA -> CASLFORMULA
negationNormalForm sen = case sen of
 Quantification q vars qsen _ ->
   Quantification q vars (negationNormalForm qsen) nullRange
 Junction j sens _ ->
   Junction j (map negationNormalForm sens) nullRange
 Relation sen1 Implication sen2 _ ->
   let sen1' = negationNormalForm $
                Negation (negationNormalForm sen1) nullRange
       sen2' = negationNormalForm sen2
   in Junction Dis [sen1', sen2'] nullRange
 -- During parsing, "f2 if f1" is saved as "Relation f1 RevImpl f2 _"
 Relation sen1 RevImpl sen2 _ ->
   let sen1' = negationNormalForm $
                Negation (negationNormalForm sen1) nullRange
       sen2' = negationNormalForm sen2
   in Junction Dis [sen1', sen2'] nullRange
 Relation sen1 Equivalence sen2 _ ->
   let sen1' = Relation sen1 Implication sen2 nullRange
       sen2' = Relation sen2 Implication sen1 nullRange
   in negationNormalForm $ Junction Con [sen1', sen2'] nullRange
 Negation (Negation sen' _) _ ->
   negationNormalForm sen'
 Negation (Junction j sens _) _ ->
   Junction (dualJunctor j)
     (map (\x -> negationNormalForm $ Negation x nullRange) sens)
     nullRange
 Negation (Quantification Unique_existential _vars _sen _) _->
    error "negation normal form for unique existentials nyi"
 Negation (Quantification q vars qsen _) _ ->
   Quantification (dualQuant q) vars
     (negationNormalForm $ Negation qsen nullRange)
     nullRange
 Negation (Relation sen1 Implication sen2 _) _ ->  
  negationNormalForm $ 
    Negation (Junction Dis [Negation sen1 nullRange, sen2] nullRange) nullRange
 Negation (Relation sen1 RevImpl sen2 _) _ ->  
  negationNormalForm $ 
    Negation (Junction Dis [Negation sen2 nullRange, sen1] nullRange) nullRange
 Negation (Relation sen1 Equivalence sen2 _) _ -> 
  negationNormalForm $
    Negation (Junction Con [Junction Dis [Negation sen1 nullRange, sen2] nullRange,
                            Junction Dis [Negation sen2 nullRange, sen1] nullRange] 
              nullRange) 
    nullRange
 x -> x
