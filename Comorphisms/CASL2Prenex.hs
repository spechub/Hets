{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  prenex normal form for sentences of a CASL theory
Copyright   :  (c) Mihai Codescu, 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codescu@iws.cs.uni-magdeburg.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Comorphism)

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
    sourceSublogic CASL2Prenex = SL.caslTop
    targetLogic CASL2Prenex = CASL
    mapSublogic CASL2Prenex sl = 
      Just $ min sl (sl{SL.which_logic = SL.Prenex})
    map_theory CASL2Prenex = mapTheory
    map_morphism CASL2Prenex = return
    map_sentence CASL2Prenex sig = return . (mapSentence sig)
    map_symbol CASL2Prenex _ = Set.singleton . id
    has_model_expansion CASL2Prenex = True
    is_weakly_amalgamable CASL2Prenex = True

-- remove equivalences
preprocessSen :: CASLFORMULA -> CASLFORMULA
preprocessSen sen = case sen of
 Quantification q vdecls sen' r ->
   Quantification q vdecls (preprocessSen sen') r
 Junction j sens r -> 
   Junction j (map preprocessSen sens) r
 Relation sen1 Equivalence sen2 _ -> let
    sen1' = Relation sen1 Implication sen2 nullRange
    sen2' = Relation sen2 Implication sen1 nullRange
   in Junction Con [sen1', sen2'] nullRange
 Relation sen1 rel sen2 r -> 
   Relation (preprocessSen sen1) rel 
            (preprocessSen sen2) r
 Negation sen' r -> 
   Negation (preprocessSen sen') r
 _ -> sen

-- make variables distinct: 
-- if a variable v of sort s already appears in a formula
-- substitute it with a fresh variable
mkDistVars :: CASLFORMULA -> CASLFORMULA
mkDistVars sen = 
 let (_, _, sen') = mkDistVarsAux 0 [] sen
 in sen'

mkDistVarsAux :: Int -- first available suffix for vars
              -> [(VAR, SORT)] -- vars encountered so far
              -> CASLFORMULA
              -> (Int, [(VAR, SORT)], CASLFORMULA)
mkDistVarsAux n vlist sen = case sen of
 Quantification q vdecls form range -> let
   -- first make variables distinct for form
   dvars = flatVAR_DECLs vdecls
   (n', _, form') = mkDistVarsAux n (dvars ++ vlist) form
   -- here we are not interested in the variables generated for the quantified form, so we can forget them
   replVarDecl vds oN nN s = reverse $ 
                              foldl (\usedD vd@(Var_decl names sort r) -> 
                                       if sort == s then -- found it, replace oN with nN in names
                                         let vd' = Var_decl (map (\x -> if x == oN then nN else x) names) sort r  
                                         in vd':usedD
                                       else vd:usedD 
                                 ) [] vds
   checkAndReplace (n0, knownV, quantF, quants) (x, s) =
      if (x,s) `elem` knownV 
       then
         let  
           x' = genNumVar "x" n0
           quants' = replVarDecl quants x x' s
           quantF' = substitute x s (Qual_var x' s nullRange) quantF
         in (n0 + 1, (x', s):knownV, quantF', quants')
       else (n0    , (x , s):knownV, quantF , quants )  
   (n'', vlist', form'', vdecls') = foldl checkAndReplace (n', vlist, form', vdecls) dvars
  in (n'', vlist', Quantification q vdecls' form'' range)
 Junction j sens r -> let
   (n', vlist', sens') = foldl (\(x, vs, osens) s -> 
                           let
                            (x', vs', s') = mkDistVarsAux x vs s
                           in (x', vs', s':osens)) (n, vlist, []) sens
  in (n', vlist', Junction j (reverse sens') r)
 Relation sen1 rel sen2 r -> let
   (n1, vlist1, sen1') = mkDistVarsAux n  vlist  sen1
   (n2, vlist2, sen2') = mkDistVarsAux n1 vlist1 sen2
  in (n2, vlist2, Relation sen1' rel sen2' r)
 Negation sen' r -> let 
   (n', vlist', sen'') = mkDistVarsAux n vlist sen' 
  in (n', vlist', Negation sen'' r)
 _ -> (n, vlist, sen)
       
computePNF :: CASLFORMULA -> CASLFORMULA
computePNF sen = case sen of 
 Negation nsen _ -> let 
   nsen' = computePNF nsen
   in case nsen' of 
       Quantification q vdecls qsen _ -> 
         Quantification (dualQuant q) vdecls 
                        (computePNF $ Negation qsen nullRange) nullRange
       _ -> Negation nsen' nullRange
 Relation sen1 Implication sen2 _ -> let 
   sen1' = computePNF sen1
   sen2' = computePNF sen2
   in case sen1' of 
      Quantification q vdecls qsen _ -> 
        Quantification (dualQuant q) vdecls (computePNF $ Relation qsen Implication sen2 nullRange) nullRange
      _ -> case sen2' of 
        Quantification q vdecls qsen _ -> 
          Quantification q vdecls 
            (computePNF $ Relation sen1' Implication qsen nullRange) nullRange 
          -- recursive call to catch multiple quantifiers for sen2'
        _ -> -- no quantifications
          Relation sen1' Implication sen2' nullRange
 -- During parsing, "f2 if f1" is saved as "Relation f1 RevImpl f2 _"
 Relation sen1 RevImpl sen2 _ -> 
  computePNF $ Relation sen1 Implication sen2 nullRange
 Quantification q vdecls qsen _ -> 
  Quantification q vdecls (computePNF qsen) nullRange
 Junction j sens _ -> let
   sens' = map computePNF sens
   collectQuants s = case s of 
                       Quantification q vd qs _ -> let (vs, qs') = collectQuants qs in ((q,vd):vs, qs')
                       _ -> ([], s)
   (vdecls, sens'') = foldl (\(vs, ss) s -> case s of 
                                           Quantification q vd qs _ -> let (vs', qs') = collectQuants qs
                                                                          in (vs' ++ (q,vd):vs, qs':ss)
                                           _ -> (vs, s:ss)) 
                    ([], []) sens'
   qsen = Junction j (reverse sens'') nullRange
   rsen = foldl (\s (q, vd) -> Quantification q vd s nullRange) qsen vdecls 
  in rsen
 _ -> sen 

mapSentence :: CASLSign -> CASLFORMULA -> CASLFORMULA
mapSentence _ =
 computePNF . mkDistVars . preprocessSen

mapTheory :: (CASLSign, [Named CASLFORMULA]) ->
          Result (CASLSign, [Named CASLFORMULA])
mapTheory (sig, nsens) = do
 let nsens' = map (\nsen -> nsen{
                             sentence = mapSentence sig $ sentence nsen
                             }) 
              nsens
 return (sig, nsens')
