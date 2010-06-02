{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  VSE refinement as comorphism
Copyright   :  (c) M. Codescu, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Mihai.Codescu@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to VSE.
-}

module Comorphisms.CASL2VSERefine (CASL2VSERefine(..)
 ) where

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Quantification

import VSE.Logic_VSE
import VSE.As
import VSE.Ana

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import Common.Result
import Common.Utils (number)
import Common.Lib.State

import qualified Data.Set as Set
import qualified Data.Map as Map

-- | The identity of the comorphism
data CASL2VSERefine = CASL2VSERefine deriving (Show)

instance Language CASL2VSERefine -- default definition is okay

instance Comorphism CASL2VSERefine
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol ProofTree
               VSE ()
               VSEBasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol () where
    sourceLogic CASL2VSERefine = CASL
    sourceSublogic CASL2VSERefine = SL.cFol
    targetLogic CASL2VSERefine = VSE
    mapSublogic CASL2VSERefine _ = Just ()
    map_theory CASL2VSERefine = mapCASLTheory
    map_morphism CASL2VSERefine = return . mapMor
    map_sentence CASL2VSERefine _ = error "map sen nyi" --return. mapCASSen
    map_symbol CASL2VSERefine = error "map symbol nyi"
    has_model_expansion CASL2VSERefine = True
        --check these 3, but should be fine
    is_weakly_amalgamable CASL2VSERefine = True
    isInclusionComorphism CASL2VSERefine = False

mapCASLTheory :: (CASLSign, [Named CASLFORMULA]) ->
                 Result (VSESign, [Named Sentence])
mapCASLTheory (sig, n_sens) =
  let (tsig, genAx) = mapSig sig
      tsens = map mapNamedSen n_sens
      allSens = tsens ++ genAx
  in if null $ checkCases tsig allSens then return (tsig, allSens) else
     fail "case error in signature"

mapSig :: CASLSign -> (VSESign, [Named Sentence])
mapSig sign =
 let wrapSort (procsym, axs) s = let
        restrName = gnRestrName s
        eqName = gnEqName s
        sProcs = [(restrName, Profile [Procparam In s] Nothing),
                   (eqName,
                     Profile [Procparam In s, Procparam In s]
                             (Just uBoolean))]
        varx = Qual_var (genToken "x") s nullRange
        vary = Qual_var (genToken "y") s nullRange
        varz = Qual_var (genToken "z") s nullRange
        varb = Qual_var (genToken "b")
                        uBoolean nullRange
        varb1 = Qual_var (genToken "b1")
                        uBoolean nullRange
        varb2 = Qual_var (genToken "b2")
                        uBoolean nullRange
        sSens = [ makeNamed ("ga_termination_eq_" ++ show s) $
                  Quantification Universal [Var_decl [genToken "x",
                                                      genToken "y"] s nullRange
                                           , Var_decl [genToken "b"]
                                              uBoolean nullRange]
                  (Implication
                  (Conjunction [
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                         (Pred_type [s] nullRange) nullRange)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                         (Pred_type [s] nullRange) nullRange)
                            [vary] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange
                   ] nullRange)
                  (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                         (Assign (genToken "b")
                          (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [varx, vary] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange)
                  True nullRange) nullRange ,
                  makeNamed ("ga_refl_eq_" ++ show s) $
                  Quantification Universal [Var_decl [genToken "x"] s nullRange
                                           ,Var_decl [genToken "b"]
                                              uBoolean nullRange]
                  (Implication
                  (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                          (Pred_type [s] nullRange ) nullRange)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange)

                     (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Assign (genToken "b")
                          (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [varx, varx] nullRange))
                        nullRange)
                      (Strong_equation
                         varb
                         (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                          [] nullRange) nullRange
                      )) nullRange)
                  True nullRange) nullRange
                 , makeNamed ("ga_sym_eq_" ++ show s) $
                  Quantification Universal [Var_decl [genToken "x",
                                                      genToken "y"] s nullRange
                                           ,Var_decl [genToken "b1",
                                                      genToken "b2"]
                                              uBoolean nullRange]
                  (Implication
                   (Conjunction [
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                         (Pred_type [s] nullRange) nullRange)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                         (Pred_type [s] nullRange) nullRange)
                            [vary] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                    ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Assign (genToken "b1")
                          (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [varx, vary] nullRange))
                          nullRange)
                      (Strong_equation varb1 aTrue nullRange
                      )) nullRange
                   ] nullRange)


                     (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Assign (genToken "b2")
                          (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [vary, varx] nullRange))
                          nullRange)
                      (Strong_equation
                         varb2 aTrue nullRange
                      )) nullRange)
                  True nullRange) nullRange
                  , makeNamed ("ga_trans_eq_" ++ show s) $
                  Quantification Universal [Var_decl [genToken "x",
                                                      genToken "y",
                                                      genToken "z"] s nullRange
                                           ,Var_decl [genToken "b1",
                                                      genToken "b2",
                                                      genToken "b"]
                                              uBoolean nullRange]
                  (Implication
                   (Conjunction [
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                        (Pred_type [s] nullRange)  nullRange)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                        (Pred_type [s] nullRange ) nullRange)
                            [vary] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name restrName
                                        (Pred_type [s] nullRange ) nullRange)
                            [varz] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                    ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Assign (genToken "b1")
                          (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [varx, vary] nullRange))
                          nullRange)
                      (Strong_equation
                         varb1 aTrue nullRange
                      )) nullRange,
                    ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Assign (genToken "b2")
                          (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [vary, varz] nullRange))
                          nullRange)
                      (Strong_equation
                         varb2 aTrue nullRange
                      )) nullRange
                   ] nullRange)


                     (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Assign (genToken "b")
                          (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [varx, varz] nullRange))
                          nullRange)
                      (Strong_equation
                         varb aTrue nullRange
                      )) nullRange)
                  True nullRange) nullRange ]
                                          in
        (sProcs ++ procsym,  sSens ++ axs)
     (sortProcs, sortSens) = foldl wrapSort ([],[]) $
                                        Set.toList $ sortSet sign
     wrapOp (procsym, axs) (i, opTypeSet) = let
       funName = mkGenName i
       opTypes = Set.toList opTypeSet
       fProcs = map (\profile ->
                       (funName,
                        Profile
                           (map (Procparam In) $ opArgs profile)
                           (Just $ opRes profile))) opTypes
       opTypeSens (OpType _ w s) = let
          xtokens = map (\(_,ii) -> genNumVar "x" ii) $
                    number w
          xvars = map (
                  \(si, ii) ->
                  Qual_var (genNumVar "x" ii )
                  si nullRange ) $
                   number w
          yvars = map (
                  \(si, ii) ->
                  Qual_var (genNumVar "y" ii )
                  si nullRange ) $
                   number w
          ytokens = map (\(_,ii) -> genNumVar "y" ii) $
                    number w
          btokens = map (\(_,ii) -> genNumVar "b" ii) $
                    number w
          xtoken = genToken "x"
          ytoken = genToken "y"
          btoken = genToken "b"
          xvar = Qual_var (genToken "x")
                  s nullRange
          yvar = Qual_var (genToken "y")
                  s nullRange
          bvar = Qual_var (genToken "b")
                  uBoolean nullRange
          congrF = [makeNamed "" $
                  Quantification Universal ([Var_decl [xtoken, ytoken] s
                                            nullRange
                                           ,Var_decl (btoken:btokens)
                                              uBoolean nullRange
                                            ] ++ map
                                            (\((t1,t2),si) ->
                                             Var_decl [t1, t2] si
                                             nullRange)
                                             (zip (zip xtokens ytokens) w)
                                            )
               (Implication
                  (Conjunction
                   (concatMap (\(si,ii) -> let
                     xv = (Qual_var (genNumVar "x" ii)
                           si nullRange)
                     yv = (Qual_var (genNumVar "y" ii)
                           si nullRange)
                     varbi = genNumVar "b" ii
                     bi1 = (Qual_var (genNumVar "b" ii)
                           uBoolean nullRange)
                                          in
                     [ExtFORMULA $ Ranged ( Dlformula Diamond
                          (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name
                                    (gnRestrName si)
                                    (Pred_type [si] nullRange) nullRange )
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name
                                    (gnRestrName si)
                                    (Pred_type [si] nullRange) nullRange)
                                   [yv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ mkRanged $ Dlformula Diamond
                              (Ranged
                                (Assign varbi
                            (Application
                             (Qual_op_name
                               (gnEqName si)
                               (Op_type Partial [si,si] uBoolean nullRange)
                              nullRange)
                             [xv, yv] nullRange))
                                nullRange)
                              (Strong_equation
                                  bi1 aTrue nullRange)
                     ] ) $
                    number w )
                   nullRange )--hypothesis
                  (ExtFORMULA $ Ranged (
                     Dlformula Diamond

                      (Ranged
                        (Assign (genToken "x")
                            (Application
                             (Qual_op_name
                               (mkGenName i)
                               (Op_type Partial w s nullRange)
                              nullRange)
                             xvars nullRange))
                       nullRange)
                      (ExtFORMULA $ Ranged (
                         Dlformula Diamond
                      (Ranged
                         (Assign (genToken "y")
                            (Application
                             (Qual_op_name
                               (mkGenName i)
                               (Op_type Partial w s nullRange)
                              nullRange)
                             yvars nullRange))
                       nullRange)
                       (ExtFORMULA $
                        Ranged (
                          Dlformula Diamond
                          ( Ranged
                            (Assign (genToken "b")
                            (Application
                             (Qual_op_name
                               (gnEqName s)
                               (Op_type Partial [s,s] uBoolean nullRange)
                              nullRange)
                             [xvar, yvar] nullRange))
                          nullRange
                          )
                          (Strong_equation
                                  bvar aTrue nullRange)
                        ) nullRange)
                        ) nullRange)
                   ) nullRange) --conclusion
                  True nullRange )
               nullRange
              ]
          termF = if not $ null w then
                   [ makeNamed "" $ Quantification Universal
                     (Var_decl [xtoken] s nullRange
                      : map (\ (t1, si) -> Var_decl [t1] si nullRange)
                        (zip xtokens w))
                     (Implication
                        (Conjunction
                         (concatMap (\ (si, ii) -> let
                     xv = Qual_var (genNumVar "x" ii) si nullRange in
                     [ExtFORMULA $ Ranged ( Dlformula Diamond
                          (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name
                                    (gnRestrName si)
                                    (Pred_type (w ++ [s]) nullRange) nullRange)
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange
                     ] ) $
                    number w )
                         nullRange)
                        (ExtFORMULA $ Ranged
                       (
                       Dlformula Diamond
                       (Ranged
                         (Assign (genToken "x")
                            (Application
                             (Qual_op_name
                               (mkGenName i)
                               (Op_type Partial w s nullRange)
                              nullRange)
                             xvars nullRange))
                        nullRange)
                       (ExtFORMULA $
                         Ranged
                         (Dlformula Diamond (Ranged
                          (Call (Predication (Qual_pred_name
                                              (gnRestrName s)
                                    (Pred_type [s] nullRange) nullRange)
                              [xvar] nullRange))
                                             nullRange)
                          (True_atom nullRange)
                          )
                         nullRange)
                       ) nullRange)
                        True  nullRange)
                     nullRange
                   ]
                  else
                   [makeNamed "" $ Quantification Universal
                                   [Var_decl [xtoken] s nullRange]
                     (ExtFORMULA $ Ranged
                       (
                       Dlformula Diamond
                       (Ranged
                         (Assign (genToken "x")
                            (Application
                             (Qual_op_name
                               (mkGenName i)
                               (Op_type Partial [] s nullRange)
                              nullRange)
                             [] nullRange))
                        nullRange)
                       (ExtFORMULA $
                         Ranged
                         (Dlformula Diamond (Ranged
                          (Call (Predication (Qual_pred_name
                                              (gnRestrName s)
                                    (Pred_type [s] nullRange) nullRange)
                              [xvar] nullRange))
                                             nullRange)
                          (True_atom nullRange)
                          )
                         nullRange)
                       ) nullRange) nullRange]
                                   in
         if null w then termF else congrF ++ termF

       fSens = concatMap opTypeSens opTypes
                                            in
       (procsym ++ fProcs, axs ++ fSens)
     (opProcs, opSens) = foldl wrapOp ([],[]) $
                                        Map.toList $ opMap sign
     wrapPred (procsym, axs) (i, predTypeSet) = let
       predTypes = Set.toList predTypeSet
       procName = mkGenName i
       pProcs = map (\profile -> (procName,
                        Profile
                           (map (Procparam In) $ predArgs profile)
                           (Just uBoolean))) predTypes
       predTypeSens (PredType w) = let
          xtokens = map (\(_,ii) -> genNumVar "x" ii) $
                    number w
          xvars = map (
                  \(si, ii) ->
                  Qual_var (genNumVar "x" ii )
                  si nullRange ) $
                   number w
          ytokens = map (\(_,ii) -> genNumVar "y" ii) $
                    number w
          btokens = map (\(_,ii) -> genNumVar "b" ii) $
                    number w
          btoken = genToken "b"
          r1 = genToken "r1"
          r2 = genToken "r2"
          rvar1 = Qual_var (genToken "r1")
                  uBoolean nullRange
          rvar2 = Qual_var (genToken "r2")
                  uBoolean nullRange
          congrP = [makeNamed "" $ Quantification Universal
              (Var_decl (btoken : r1 : r2 : btokens) uBoolean nullRange
               : map (\ ((t1, t2), si) -> Var_decl [t1, t2] si nullRange)
                 (zip (zip xtokens ytokens) w))
               (Implication
                  (Conjunction
                   (concatMap (\(si,ii) -> let
                     xv = (Qual_var (genNumVar "x" ii)
                           si nullRange)
                     yv = (Qual_var (genNumVar "y" ii)
                           si nullRange)
                     bi1 = (Qual_var (genNumVar "b" ii)
                           uBoolean nullRange)
                                          in
                     [ExtFORMULA $ Ranged ( Dlformula Diamond
                          (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name
                                    (gnRestrName si)
                                    (Pred_type [si] nullRange) nullRange)
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name
                                    (gnRestrName si)
                                    (Pred_type [si] nullRange) nullRange)
                                   [yv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ mkRanged $ Dlformula Diamond
                              (Ranged
                                (Assign (genNumVar "b" ii)
                            (Application
                             (Qual_op_name
                               (gnEqName si)
                               (Op_type Partial [si,si] uBoolean nullRange)
                              nullRange)
                             [xv, yv] nullRange))
                               nullRange)
                              (Strong_equation
                                  bi1 aTrue nullRange)
                     ] ) $
                    number w )
                   nullRange )--hypothesis
                  (ExtFORMULA $ Ranged (
                     Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Qual_pred_name (mkGenName i)
                                    (Pred_type (w ++ [uBoolean]) nullRange)
                                    nullRange)
                                   (map (
                  \(si, ii) ->
                  Qual_var (genNumVar "x" ii )
                  si nullRange )
                   (number w) ++ [rvar1]) nullRange)) nullRange)
                      (ExtFORMULA $ Ranged (
                         Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Qual_pred_name (mkGenName i)
                                    (Pred_type (w ++ [uBoolean]) nullRange)
                                     nullRange)
                                   (map (
                  \(si, ii) ->
                  Qual_var (genNumVar "y" ii )
                  si nullRange )
                   (number w) ++ [rvar2]) nullRange)) nullRange)
                       (Strong_equation
                                  rvar1
                                  rvar2
                                  nullRange
                        )
                        ) nullRange)
                   ) nullRange) --conclusion
                  True nullRange )
               nullRange
              ]
          termP = [ makeNamed "" $ Quantification Universal
                                     (map
                                             (\(t1,si) ->
                                              Var_decl [t1] si
                                              nullRange)
                                              (zip xtokens w)
                                      ++ [Var_decl [r1]
                                              uBoolean nullRange])
                      (Implication
                         (Conjunction
                          (concatMap (\(si,ii) -> let
                      xv = (Qual_var (genNumVar "x" ii)
                            si nullRange)
                                           in
                      [ExtFORMULA $ Ranged ( Dlformula Diamond
                           (Ranged
                                 (Call
                                  (Predication
                                    (Qual_pred_name
                                     (gnRestrName si)
                                    (Pred_type [si] nullRange) nullRange)
                                    [xv] nullRange))
                                nullRange)
                           (True_atom nullRange) ) nullRange
                      ] ) $
                     number w )
                          nullRange)
                         (ExtFORMULA $ Ranged
                        (
                        Dlformula Diamond
                        (Ranged
                          (Call (Predication (Qual_pred_name (mkGenName i)
                                    (Pred_type (w ++ [uBoolean]) nullRange)
                                     nullRange)
                                 (xvars++[rvar1])
                           nullRange))
                         nullRange)
                        ( True_atom
                          nullRange)
                        ) nullRange)
                         True  nullRange)
                      nullRange
                    ]
                                   in congrP ++ termP
       pSens = concatMap predTypeSens predTypes
                                                in
      (procsym ++ pProcs, axs ++ pSens)
     (predProcs, predSens) = foldl wrapPred ([],[]) $
                                        Map.toList $ predMap sign
     procs = Procs $ Map.fromList (sortProcs ++ opProcs ++ predProcs)
     newPreds = procsToPredMap procs
     newOps = procsToOpMap procs
 in(sign { opMap = newOps,
           predMap = newPreds,
           extendedInfo = procs,
           sentences = [] }, sortSens ++ opSens ++ predSens)

mapNamedSen :: Named CASLFORMULA -> Named Sentence
mapNamedSen n_sen = let
 sen = sentence n_sen
 trans = mapCASLSen sen
                    in
 n_sen{sentence = trans}

mapMor :: CASLMor -> VSEMor
mapMor m = let
  (om, pm) = vseMorExt m
  in m
  { msource = fst $ mapSig $ msource m
  , mtarget = fst $ mapSig $ mtarget m
  , op_map = om
  , pred_map = pm
  , extended_map = emptyMorExt
  }

mapCASLSen :: CASLFORMULA -> Sentence
mapCASLSen f = let
 (sen, (_i, vars)) = runState (mapCASLSenAux f) (0, Set.empty)
               in
 case f of
  Sort_gen_ax _ _ -> sen
  _ -> addQuantifiers vars sen

addQuantifiers :: VarSet -> Sentence -> Sentence
addQuantifiers vars sen =
 Quantification Universal
  (map (\(v,s) -> Var_decl [v] s nullRange) $ Set.toList vars) sen nullRange

mapCASLSenAux :: CASLFORMULA -> State (Int, VarSet) Sentence
mapCASLSenAux f = case f of
  Sort_gen_ax constrs isFree -> do
   let
    (genSorts, _, _ ) = recover_Sort_gen_ax constrs
    toProcs (Op_name _, _) = error "must be qual names"
    toProcs (Qual_op_name op (Op_type _fkind args res _range) _, l) =
           ( Qual_op_name (mkGenName op)
                           (Op_type Partial args res nullRange) nullRange,
             l)
    opsToProcs (Constraint nSort syms oSort) =
                Constraint nSort (map toProcs syms) oSort
   return $ ExtFORMULA $ Ranged
             (RestrictedConstraint
                (map opsToProcs constrs)
                (Map.fromList $ map (\s -> (s, gnRestrName s)) genSorts)
              isFree)
            nullRange
  True_atom _ps -> return $ True_atom nullRange
  False_atom _ps -> return $ False_atom nullRange
  Strong_equation t1 t2 _ps -> do
     let sort1 = sortOfTerm t1
     n1 <- freshIndex sort1 -- (typeof t1)
     prg1 <- mapCASLTerm n1 t1
     n2 <- freshIndex sort1 -- (typeof t2)
     prg2 <- mapCASLTerm n2 t2
     n <- freshIndex uBoolean
     return $ ExtFORMULA $ Ranged
      (Dlformula Diamond
       (Ranged
           (Seq  (Ranged (Seq prg1 prg2) nullRange)
                 (Ranged
                 (Assign
                    (genNumVar "x" n)
                    (Application
                       (Qual_op_name
                         (gnEqName sort1)
                         (Op_type Partial [sort1,sort1] uBoolean nullRange)
                        nullRange)
                       [Qual_var (genNumVar "x" n1) sort1 nullRange,
                        Qual_var (genNumVar "x" n2) sort1 nullRange]
                       nullRange
                    )
                 ) nullRange)
           )
        nullRange)
       (Strong_equation (Qual_var (genNumVar "x" n) uBoolean nullRange)
                        aTrue nullRange)
      )
      nullRange
     -- here i have to return smth like
     --      <: xn1 := prg1;
     --         xn2 := prg2;
     --         xn := gn_eq_s(xn1,xn2) :> xn = True  "
  Predication pn as _qs -> do
     indexes <- mapM (freshIndex . sortOfTerm) as
     prgs <- mapM (\(ti, i) -> mapCASLTerm i ti) $ zip as indexes
     let xvars = map (\(ti,i) ->
                     Qual_var (genNumVar "x" i)
                              (sortOfTerm ti) nullRange ) $ zip as indexes
     n <- freshIndex uBoolean
     let asgn = if not $ null prgs then
                       foldr1 (\p1 p2 -> Ranged (Seq p1 p2) nullRange) prgs
                       else Ranged Skip nullRange
     case pn of
      Pred_name _ -> fail "must be qualified"
      Qual_pred_name pname (Pred_type ptype _)_ -> return $ ExtFORMULA $ Ranged
       (Dlformula Diamond
        (Ranged
          (Seq
             asgn
             (Ranged (Assign (genNumVar "x" n)
                       (Application
                         (Qual_op_name
                          (mkGenName pname)
                          (Op_type Partial ptype uBoolean nullRange) nullRange)
                          xvars nullRange))
              nullRange))
         nullRange)
        (Strong_equation
          (Qual_var (genNumVar "x" n) uBoolean nullRange)
                        aTrue nullRange))
       nullRange
     -- <: xi := prgi;
     --      x:= gn_p(x1,..,xn):> x = True
  Conjunction fs _r -> do
   mapFs <- mapM mapCASLSenAux fs
   return $ Conjunction mapFs nullRange
  Disjunction fs _r -> do
   mapFs <- mapM mapCASLSenAux fs
   return $ Disjunction mapFs nullRange
  Implication f1 f2 flag _r -> do
   trf1 <- mapCASLSenAux f1
   trf2 <- mapCASLSenAux f2
   return $ Implication trf1 trf2 flag nullRange
  Equivalence f1 f2 _r -> do
   trf1 <- mapCASLSenAux f1
   trf2 <- mapCASLSenAux f2
   return $ Equivalence trf1 trf2 nullRange
  Negation f1 _r -> do
   trf <- mapCASLSenAux f1
   return $ Negation trf nullRange
  Quantification q vars sen _ ->
   case q of
    Universal -> do
     trSen <- mapCASLSenAux sen
     let h = map (\ (Var_decl varS s _) -> let
           restrs = map (\v -> ExtFORMULA $ Ranged (
                                  Dlformula Diamond
                                  (Ranged
                                    (Call
                                      (Predication
                                         (Qual_pred_name
                                            (gnRestrName s)
                                            (Pred_type [s] nullRange)
                                            nullRange
                                         )
                                         [Qual_var v s nullRange]
                                         nullRange
                                      )
                                    )
                                   nullRange)
                                  (True_atom nullRange)) nullRange)
                 varS
                                         in
           Conjunction restrs  nullRange)
             vars
     let sen' = Implication
                 (foldr1 (\ sen1 sen2 -> Conjunction [sen1,sen2] nullRange) h)
                 trSen True nullRange
     return $ Quantification q vars sen' nullRange
    Existential -> do
     trSen <- mapCASLSenAux sen
     let h = map (\ (Var_decl varS s _) -> let
           restrs = map (\v -> ExtFORMULA $ Ranged (
                                  Dlformula Diamond
                                  (Ranged
                                    (Call
                                      (Predication
                                         (Qual_pred_name
                                            (gnRestrName s)
                                            (Pred_type [s] nullRange)
                                            nullRange
                                         )
                                         [Qual_var v s nullRange]
                                         nullRange
                                      )
                                    )
                                   nullRange)
                                  (True_atom nullRange)) nullRange)
                 varS
                                         in
           Conjunction restrs  nullRange)
             vars
     let sen' = Conjunction
                 [(foldr1 (\ sen1 sen2 -> Conjunction [sen1,sen2] nullRange) h),
                 trSen] nullRange
     return $ Quantification q vars sen' nullRange
    Unique_existential -> fail "nyi Unique_existential"
  _ -> fail "Comorphisms.CASL2VSERefine.mapCASLSenAux"


mapCASLTerm :: Int -> TERM () -> State (Int, VarSet) Program
mapCASLTerm n t = case t of
  Qual_var v s _ps -> return $
      Ranged (Assign (genNumVar "x" n)
               (Qual_var v s nullRange)) nullRange
  Application opsym as _qs  -> do
   indexes <- mapM (freshIndex . sortOfTerm) as
   let xvars = map (\(ti,i) ->
                     Qual_var (genNumVar "x" i)
                              (sortOfTerm ti) nullRange ) $ zip as indexes
   prgs <- mapM (\(ti, i) -> mapCASLTerm i ti) $ zip as indexes
   let asgn = if not $ null prgs then
                       foldr1 (\p1 p2 -> Ranged (Seq p1 p2) nullRange) prgs
                       else Ranged Skip nullRange
   case opsym of
    Op_name _ -> fail "must be qualified"
    Qual_op_name oName (Op_type _ args res _) _ ->
      case args of
       [] ->  return $ Ranged (Assign (genNumVar "x" n)
                       (Application
                        (Qual_op_name
                         (mkGenName oName)
                         (Op_type Partial args res nullRange)
                         nullRange
                        )
                       xvars nullRange))
                       nullRange
       _ -> return $ Ranged
               (Seq
                asgn
                (Ranged (Assign (genNumVar "x" n)
                       (Application
                        (Qual_op_name
                         (mkGenName oName)
                         (Op_type Partial args res nullRange)
                         nullRange
                        )
                       xvars nullRange))
                  nullRange))
                nullRange
  _ -> fail "nyi term"

freshIndex :: SORT -> State (Int, VarSet) Int
freshIndex ss = do
  (i, s) <- get
  let v = genNumVar "x" i
  put (i + 1, Set.insert (v,ss) s)
  return i
