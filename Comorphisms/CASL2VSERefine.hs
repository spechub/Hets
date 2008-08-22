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

import qualified Data.Set as Set
import qualified Data.Map as Map

import Logic.Logic
import Logic.Comorphism

import CASL.Logic_CASL
import CASL.Sublogic as SL
import CASL.Sign
import CASL.AS_Basic_CASL
import CASL.Morphism

import VSE.Logic_VSE
import VSE.As
import VSE.Ana

import Common.Result
import Common.Id
import Common.AS_Annotation

import Common.Lib.State
import CASL.Quantification
import CASL.CCC.FreeTypes

-- | The identity of the comorphism
data CASL2VSERefine = CASL2VSERefine deriving (Show)

instance Language CASL2VSERefine -- default definition is okay

instance Comorphism CASL2VSERefine
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               Symbol RawSymbol Q_ProofTree
               VSE ()
               VSEBasicSpec Sentence SYMB_ITEMS SYMB_MAP_ITEMS
               VSESign
               VSEMor
               Symbol RawSymbol () where
    sourceLogic CASL2VSERefine = CASL
    sourceSublogic CASL2VSERefine = SL.top
       -- here is not ok, because of partiality
    targetLogic CASL2VSERefine = VSE
    mapSublogic CASL2VSERefine _ = Just ()
    map_theory CASL2VSERefine = mapCASLTheory
    map_morphism CASL2VSERefine = return . mapMor
    map_sentence CASL2VSERefine _ = return. mapCASLSen
    map_symbol CASL2VSERefine = error "map symbol nyi"
    has_model_expansion CASL2VSERefine = True
        --check these 3, but should be fine
    is_weakly_amalgamable CASL2VSERefine = True
    isInclusionComorphism CASL2VSERefine = False

mapCASLTheory :: (CASLSign, [Named CASLFORMULA]) ->
                 Result (VSESign, [Named Sentence])
mapCASLTheory (sig, n_sens) = do
  let (tsig, genAx) =  mapSig sig
      tsens = concatMap mapNamedSen n_sens
  case not $ null $ checkCases tsig (tsens ++ genAx) of
   True -> fail "case error in signature"
   _ -> return (tsig, tsens ++ genAx)

mapSig :: CASLSign -> (VSESign, [Named Sentence])
mapSig sign =
 let wrapSort (procsym, axs) s = let
        restrName = stringToId $ genNamePrefix ++ "restr_"++show s
        uniformName = stringToId $ genNamePrefix ++ "uniform_"++show s
        eqName = stringToId $ genNamePrefix ++ "eq_"++show s
        sProcs = [(restrName, Profile [Procparam In s] Nothing),
                   (uniformName, Profile [Procparam In s] Nothing),
                   (eqName,
                     Profile [Procparam In s, Procparam In s]
                             (Just $ stringToId  "Boolean"))]
        varx = Qual_var (mkSimpleId $ genNamePrefix ++ "x") s nullRange
        vary = Qual_var (mkSimpleId $ genNamePrefix ++ "y") s nullRange
        varz = Qual_var (mkSimpleId $ genNamePrefix ++ "z") s nullRange
        varb = Qual_var (mkSimpleId $ genNamePrefix ++ "b")
                        uBoolean nullRange
        varb1 = Qual_var (mkSimpleId $ genNamePrefix ++ "b1")
                        uBoolean nullRange
        varb2 = Qual_var (mkSimpleId $ genNamePrefix ++ "b2")
                        uBoolean nullRange
        sSens = [ makeNamed ("ga_termination_eq_" ++ show s) $
                  Quantification Universal [Var_decl [genToken "x",
                                                      genToken "y"] s nullRange]
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
                        (Call
                          (Predication (Qual_pred_name eqName
                                          (Pred_type [s,s, uBoolean] nullRange)
                             nullRange )
                            [varx, vary,varb] nullRange))
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
                        (Call
                          (Predication (Qual_pred_name eqName
                                         (Pred_type [s,s,uBoolean] nullRange)
                                        nullRange)
                            [varx, varx, varb] nullRange))
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
                        (Call
                          (Predication (Qual_pred_name eqName
                                        (Pred_type [s,s,uBoolean] nullRange)
                                        nullRange)
                            [varx, vary, varb1] nullRange))
                          nullRange)
                      (Strong_equation
                         varb1
                         (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                          [] nullRange) nullRange
                      )) nullRange
                   ] nullRange)


                     (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name eqName
                                         (Pred_type [s,s,uBoolean] nullRange)
                                        nullRange)
                            [vary, varx, varb2] nullRange))
                          nullRange)
                      (Strong_equation
                         varb2
                         (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                          [] nullRange) nullRange
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
                        (Call
                          (Predication (Qual_pred_name eqName
                                        (Pred_type [s,s,uBoolean] nullRange)
                                        nullRange)
                            [varx, vary, varb1] nullRange))
                          nullRange)
                      (Strong_equation
                         varb1
                         (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                          [] nullRange) nullRange
                      )) nullRange,
                    ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name eqName
                                         (Pred_type [s,s,uBoolean] nullRange )
                                        nullRange)
                            [vary, varz, varb2] nullRange))
                          nullRange)
                      (Strong_equation
                         varb2
                         (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                          [] nullRange) nullRange
                      )) nullRange
                   ] nullRange)


                     (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Qual_pred_name eqName
                                         (Pred_type [s,s,uBoolean] nullRange )
                                        nullRange)
                            [varx, varz, varb] nullRange))
                          nullRange)
                      (Strong_equation
                         varb
                         (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                          [] nullRange) nullRange
                      )) nullRange)
                  True nullRange) nullRange ]
                                          in
        (sProcs ++ procsym,  sSens ++ axs)
     (sortProcs, sortSens) = foldl wrapSort ([],[]) $
                                        Set.toList $ sortSet sign
     wrapOp (procsym, axs) (i, opTypeSet) = let
       funName = stringToId $ genNamePrefix ++ show i
       opTypes = Set.toList opTypeSet
       fProcs = map (\profile ->
                       (funName,
                        Profile
                           (map (Procparam In) $ opArgs profile)
                           (Just $ opRes profile))) opTypes
       opTypeSens (OpType _ w s) = let
          xtokens = map (\(_,ii) -> genToken $ "x"++ show ii) $
                    zip w [1::Int ..]
          xvars = map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "x" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]
          yvars = map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "y" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]
          ytokens = map (\(_,ii) -> genToken $ "y"++ show ii) $
                    zip w [1::Int ..]
          btokens = map (\(_,ii) -> genToken $ "b"++ show ii) $
                    zip w [1::Int ..]
          xtoken = genToken "x"
          ytoken = genToken "y"
          btoken = genToken "b"
          xvar = Qual_var (mkSimpleId $ genNamePrefix ++ "x")
                  s nullRange
          yvar = Qual_var (mkSimpleId $ genNamePrefix ++ "y")
                  s nullRange
          bvar = Qual_var (mkSimpleId $ genNamePrefix ++ "b")
                  uBoolean nullRange
          congrF = [makeNamed "" $
                  Quantification Universal ([Var_decl [xtoken, ytoken] s
                                            nullRange
                                           ,Var_decl (btoken:btokens)
                                              uBoolean nullRange
                                            ] ++  (map
                                            (\((t1,t2),si) ->
                                             Var_decl [t1, t2] si
                                             nullRange) $
                                             zip (zip xtokens ytokens) w)
                                            )
               (Implication
                  (Conjunction
                   (concatMap (\(si,ii) -> let
                     xv = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "x" ++ show ii)
                           si nullRange)
                     yv = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "y" ++ show ii)
                           si nullRange)
                     bi = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "b" ++ show ii)
                           uBoolean nullRange)
                     bi1 = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "b" ++ show ii)
                           uBoolean nullRange)
                                          in
                     [ExtFORMULA $ Ranged ( Dlformula Diamond
                          (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                    (Pred_type [si] nullRange) nullRange )
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                    (Pred_type [si] nullRange) nullRange)
                                   [yv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "eq_" ++ show si)
                                    (Pred_type [si,si,uBoolean] nullRange)
                                    nullRange)
                                   [xv, yv, bi] nullRange))
                               nullRange)
                              (Strong_equation
                                  bi1
                                  (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)
                                                nullRange)
                                  [] nullRange) nullRange) )nullRange
                     ] ) $
                    zip w [1::Int ..] )
                   nullRange )--hypothesis
                  (ExtFORMULA $ Ranged (
                     Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ show i)
                                    (Pred_type (w ++ [s]) nullRange) nullRange)
                                   (xvars ++ [xvar]) nullRange)) nullRange)
                      (ExtFORMULA $ Ranged (
                         Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ show i)
                                    (Pred_type (w ++ [s]) nullRange) nullRange)
                                   (yvars ++ [yvar]) nullRange)) nullRange)
                       (ExtFORMULA $
                        Ranged (
                          Dlformula Diamond
                          ( Ranged
                        (Call
                          (Predication (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "eq_"++show s)
                                    (Pred_type [s,s,uBoolean] nullRange)
                                     nullRange)
                            [xvar, yvar, bvar] nullRange))
                          nullRange
                          )
                          (Strong_equation
                                  bvar
                                  (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)
                                                nullRange)
                                  [] nullRange) nullRange)
                        ) nullRange)
                        ) nullRange)
                   ) nullRange) --conclusion
                  True nullRange )
               nullRange
              ]
          termF = if not $ null w then
                   [ makeNamed "" $ Quantification Universal
                                    ([Var_decl [xtoken] s nullRange] ++ (map
                                            (\(t1,si) ->
                                             Var_decl [t1] si
                                             nullRange) $
                                             zip xtokens w))
                     (Implication
                        (Conjunction
                         (concatMap (\(si,ii) -> let
                     xv = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "x" ++ show ii)
                           si nullRange)
                                          in
                     [ExtFORMULA $ Ranged ( Dlformula Diamond
                          (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                    (Pred_type (w++[s]) nullRange) nullRange)
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange
                     ] ) $
                    zip w [1::Int ..] )
                         nullRange)
                        (ExtFORMULA $
                     (Ranged
                       (
                       Dlformula Diamond
                       (Ranged
                         (Call (Predication (Qual_pred_name (stringToId $
                                     genNamePrefix ++ show i)
                                    (Pred_type (w ++ [s]) nullRange) nullRange)
                          (xvars ++ [xvar])
                          nullRange))
                        nullRange)
                       (ExtFORMULA $
                         Ranged
                         (Dlformula Diamond (Ranged
                          (Call (Predication (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show s)
                                    (Pred_type [s] nullRange) nullRange)
                              [xvar] nullRange))
                                             nullRange)
                          (True_atom nullRange)
                          )
                         nullRange)
                       ) nullRange))
                        True  nullRange)
                     nullRange
                   ]
                  else
                   [makeNamed "" $ Quantification Universal
                                   [Var_decl [xtoken] s nullRange]
                     (ExtFORMULA $
                     (Ranged
                       (
                       Dlformula Diamond
                       (Ranged
                         (Call (Predication (Qual_pred_name (stringToId $
                                     genNamePrefix ++ show i)
                                    (Pred_type [s] nullRange) nullRange)
                              [xvar] nullRange))
                        nullRange)
                       (ExtFORMULA $
                         Ranged
                         (Dlformula Diamond (Ranged
                          (Call (Predication (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show s)
                                    (Pred_type [s] nullRange) nullRange)
                              [xvar] nullRange))
                                             nullRange)
                          (True_atom nullRange)
                          )
                         nullRange)
                       ) nullRange)) nullRange]
                                   in
         if not $ null w then congrF ++ termF
         else termF

       fSens = concatMap opTypeSens opTypes
                                            in
       (procsym ++ fProcs, axs ++ fSens)
     (opProcs, opSens) = foldl wrapOp ([],[]) $
                                        Map.toList $ opMap sign
     wrapPred (procsym, axs) (i, predTypeSet) = let
       predTypes = Set.toList predTypeSet
       procName = stringToId $ genNamePrefix ++ show i
       pProcs = map (\profile -> (procName,
                        Profile
                           (map (Procparam In) $ predArgs profile)
                           (Just $ uBoolean))) predTypes
       predTypeSens (PredType w) = let
          xtokens = map (\(_,ii) -> genToken $ "x"++ show ii) $
                    zip w [1::Int ..]
          xvars = map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "x" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]
          ytokens = map (\(_,ii) -> genToken $ "y"++ show ii) $
                    zip w [1::Int ..]
          btokens = map (\(_,ii) -> genToken $ "b"++ show ii) $
                    zip w [1::Int ..]
          btoken = genToken "b"
          r1 = genToken "r1"
          r2 = genToken "r2"
          rvar1 = Qual_var (mkSimpleId $ genNamePrefix ++ "r1")
                  uBoolean nullRange
          rvar2 = Qual_var (mkSimpleId $ genNamePrefix ++ "r2")
                  uBoolean nullRange
          congrP = [makeNamed "" $
                  Quantification Universal ([Var_decl (btoken:r1:r2:btokens)
                                              uBoolean nullRange
                                            ] ++  (map
                                            (\((t1,t2),si) ->
                                             Var_decl [t1, t2] si
                                             nullRange) $
                                             zip (zip xtokens ytokens) w)
                                            )
               (Implication
                  (Conjunction
                   (concatMap (\(si,ii) -> let
                     xv = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "x" ++ show ii)
                           si nullRange)
                     yv = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "y" ++ show ii)
                           si nullRange)
                     bi = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "b" ++ show ii)
                           uBoolean nullRange)
                     bi1 = (Qual_var (mkSimpleId $
                                     genNamePrefix ++ "b" ++ show ii)
                           uBoolean nullRange)
                                          in
                     [ExtFORMULA $ Ranged ( Dlformula Diamond
                          (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                    (Pred_type [si] nullRange) nullRange)
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                    (Pred_type [si] nullRange) nullRange)
                                   [yv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "eq_" ++ show si)
                                    (Pred_type [si,si,uBoolean] nullRange)
                                    nullRange)
                                   [xv, yv, bi] nullRange))
                               nullRange)
                              (Strong_equation
                                  bi1
                                  (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)
                                                nullRange)
                                  [] nullRange) nullRange) )nullRange
                     ] ) $
                    zip w [1::Int ..] )
                   nullRange )--hypothesis
                  (ExtFORMULA $ Ranged (
                     Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ show i)
                                    (Pred_type (w ++ [uBoolean]) nullRange)
                                    nullRange)
                                   ((map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "x" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]) ++ [rvar1]) nullRange)) nullRange)
                      (ExtFORMULA $ Ranged (
                         Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Qual_pred_name (stringToId $
                                     genNamePrefix ++ show i)
                                    (Pred_type (w ++ [uBoolean]) nullRange)
                                     nullRange)
                                   ((map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "y" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]) ++ [rvar2]) nullRange)) nullRange)
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
                                     ((map
                                             (\(t1,si) ->
                                              Var_decl [t1] si
                                              nullRange) $
                                              zip xtokens w)++[Var_decl [r1]
                                              uBoolean nullRange])
                      (Implication
                         (Conjunction
                          (concatMap (\(si,ii) -> let
                      xv = (Qual_var (mkSimpleId $
                                      genNamePrefix ++ "x" ++ show ii)
                            si nullRange)
                                           in
                      [ExtFORMULA $ Ranged ( Dlformula Diamond
                           (Ranged
                                 (Call
                                  (Predication
                                    (Qual_pred_name (stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                    (Pred_type [si] nullRange) nullRange)
                                    [xv] nullRange))
                                nullRange)
                           (True_atom nullRange) ) nullRange
                      ] ) $
                     zip w [1::Int ..] )
                          nullRange)
                         (ExtFORMULA $
                      (Ranged
                        (
                        Dlformula Diamond
                        (Ranged
                          (Call (Predication (Qual_pred_name (stringToId $
                                     genNamePrefix ++ show i)
                                    (Pred_type (w ++ [uBoolean]) nullRange)
                                     nullRange)
                                 (xvars++[rvar1])
                           nullRange))
                         nullRange)
                        ( True_atom
                          nullRange)
                        ) nullRange))
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

mapNamedSen :: Named CASLFORMULA -> [Named Sentence]
mapNamedSen n_sen = let
 sen = sentence n_sen
 trans = mapCASLSen sen
                    in
 case sen of
  Sort_gen_ax constrs _isFree -> let
    (genSorts, _genOps, _maps) = recover_Sort_gen_ax constrs
    uniformGoals = map ( \s -> Quantification
      Universal [Var_decl [genToken "x"] s nullRange]
      (Implication
       ( ExtFORMULA $ Ranged
          (Dlformula Diamond ( Ranged
            (Call $ Predication
              (Qual_pred_name (stringToId $ genNamePrefix ++ "restr_"++ show s)
                (Pred_type [s] nullRange) nullRange)
               [Qual_var (genToken "x") s nullRange] nullRange) nullRange)
            (True_atom nullRange))
          nullRange)
       ( ExtFORMULA $ Ranged
          (Dlformula Diamond (Ranged
            (Call $ Predication
              (Qual_pred_name (stringToId $ genNamePrefix ++
                                            "uniform_" ++ show s)
                (Pred_type [s] nullRange) nullRange)
               [Qual_var (genToken "x") s nullRange] nullRange) nullRange)
            (True_atom nullRange))
          nullRange) True nullRange) nullRange) genSorts
                                 in
     map (\ (gSort, gSen) ->
             makeNamed ("ga_generatedness_" ++ show gSort) gSen) $
     zip genSorts uniformGoals
  _ -> [n_sen{sentence = trans}]

mapMor :: CASLMor -> VSEMor
mapMor m = let
 renSorts = Map.keys $ sort_map m
 eqOps = Map.fromList $ map
         (\s -> ((stringToId $ genNamePrefix ++ "eq_"++ show s,
                OpType Partial [s,s] uBoolean) ,
                (stringToId $ genNamePrefix ++ "eq_"++
                                  (show $ (sort_map m) Map.!s ),
                Partial )
         ))
         renSorts
 restrPreds = Map.fromList $ concatMap
           (\s -> [(
               (stringToId $ genNamePrefix ++ "restr_"++ show s,
                PredType [s,s]),
               stringToId $ genNamePrefix ++ "restr_"++
                                  show ((sort_map m) Map.!s)),
               (
               (stringToId $ genNamePrefix ++ "uniform_"++ show s,
                PredType [s,s]),
               stringToId $ genNamePrefix ++ "uniform_"++
                                  show ((sort_map m) Map.!s))
                ]
           )
           renSorts
 renOps = Map.keys $ fun_map m
 opsProcs = Map.fromList $
            map (\ (idN, oT@(OpType _ w s)) -> let
                   (idN', _) = (fun_map m) Map.! (idN, oT)
                                               in
                  ((stringToId $ genNamePrefix ++ show idN,
                    OpType Partial w s)  ,
                   (stringToId $ genNamePrefix ++ show idN',
                    Partial)
                  )
                )
            renOps
 renPreds = Map.keys $ pred_map m
 predProcs = Map.fromList $
            map (\ (idN, pT@(PredType w)) -> let
                   idN' = (pred_map m) Map.! (idN, pT)
                                               in
                  ((stringToId $ genNamePrefix ++ show idN,
                    PredType w)  ,
                   stringToId $ genNamePrefix ++ show idN'
                  )
                )
            renPreds
 (sig1,_) = mapSig $ msource m
 (sig2,_) = mapSig $ mtarget m
           in
  m
  { msource = sig1
  , mtarget = sig2
  , fun_map = Map.union eqOps opsProcs
  , pred_map = Map.union restrPreds predProcs
  }

mapCASLSen :: CASLFORMULA -> Sentence
mapCASLSen f =
 let
  (sen, (_i, vars)) = runState (mapCASLSenAux f) (0, Set.empty)
 in addQuantifiers vars sen
  -- here i have to return an universal quantification

addQuantifiers :: VarSet -> Sentence -> Sentence
addQuantifiers vars sen =
 Quantification Universal
  (map (\(v,s) -> Var_decl [v] s nullRange) $ Set.toList vars) sen nullRange

mapCASLSenAux :: CASLFORMULA -> State (Int, VarSet) Sentence
mapCASLSenAux f = case f of
  True_atom _ps -> return $ True_atom nullRange
  False_atom _ps -> return $ False_atom nullRange
  Strong_equation t1 t2 _ps -> do
     let sort1 = sortTerm t1
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
                    (genToken $ "x" ++ show n)
                    (Application
                       (Qual_op_name
                         (stringToId $ genNamePrefix ++ "eq_" ++ show sort1)
                         (Op_type Partial [sort1,sort1] uBoolean nullRange)
                        nullRange)
                       [Qual_var (genToken $ "x" ++ show n1) sort1 nullRange,
                        Qual_var (genToken $ "x" ++ show n2) sort1 nullRange]
                       nullRange
                    )
                 ) nullRange)
           )
        nullRange)
       (Strong_equation (Qual_var (genToken $ "x" ++ show n) uBoolean nullRange)
                        (Application
                                 (Qual_op_name (stringToId  "True")
                                  (Op_type Total []
                                    uBoolean nullRange)
                                  nullRange)
                                 [] nullRange) nullRange)
      )
      nullRange
     -- here i have to return smth like
     --      <: xn1 := prg1;
     --         xn2 := prg2;
     --         xn := gn_eq_s(xn1,xn2) :> xn = True  "
  Predication pn as _qs -> do
     indexes <- mapM (\ argi -> freshIndex $ sortTerm argi) as
     prgs <- mapM (\(ti, i) -> mapCASLTerm i ti) $ zip as indexes
     let xvars = map (\(ti,i) ->
                     Qual_var (genToken $ "x" ++ show i)
                              (sortTerm ti) nullRange ) $ zip as indexes
     n <- freshIndex $ stringToId "Boolean"
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
             (Ranged (Assign (genToken $ "x" ++ show n)
                       (Application
                         (Qual_op_name
                          (stringToId $ genNamePrefix ++ show pname)
                          (Op_type Partial ptype uBoolean nullRange) nullRange)
                          xvars nullRange))
              nullRange))
         nullRange)
        (Strong_equation
          (Qual_var (genToken $ "x" ++ show n) uBoolean nullRange)
                        (Application
                                 (Qual_op_name (stringToId  "True")
                                  (Op_type Total []
                                    uBoolean nullRange)
                                  nullRange)
                                 [] nullRange) nullRange))
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
                                            (stringToId $
                                              genNamePrefix ++ "restr_"
                                              ++ show s)
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
                                            (stringToId $
                                              genNamePrefix ++ "restr_"
                                              ++ show s)
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
    _ -> fail "nyi"

  _ -> fail "nyi"


mapCASLTerm :: Int -> TERM () -> State (Int, VarSet) Program
mapCASLTerm n t = case t of
  Qual_var v s _ps -> do
     return $
      Ranged (Assign (genToken $ "x" ++ show n)
               (Qual_var v s nullRange)) nullRange
  Application opsym as _qs  -> do
   indexes <- mapM (\ argi -> freshIndex $ sortTerm argi) as
   let xvars = map (\(ti,i) ->
                     Qual_var (genToken $ "x" ++ show i)
                              (sortTerm ti) nullRange ) $ zip as indexes
   prgs <- mapM (\(ti, i) -> mapCASLTerm i ti) $ zip as indexes
   let asgn = if not $ null prgs then
                       foldr1 (\p1 p2 -> Ranged (Seq p1 p2) nullRange) prgs
                       else Ranged Skip nullRange
   case opsym of
    Op_name _ -> fail "must be qualified"
    Qual_op_name oName (Op_type _ args res _) _ ->
      case args of
       [] ->  return $ Ranged (Assign (genToken $ "x" ++ show n)
                       (Application
                        (Qual_op_name
                         (stringToId $
                           genNamePrefix ++ show oName)
                         (Op_type Partial args res nullRange)
                         nullRange
                        )
                       xvars nullRange))
                       nullRange
       _ -> return $ Ranged
               (Seq
                asgn
                (Ranged (Assign (genToken $ "x" ++ show n)
                       (Application
                        (Qual_op_name
                         (stringToId $
                           genNamePrefix ++ show oName)
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
  let v = genToken $ "x"++ show i
  put $ (i + 1, Set.insert (v,ss) s)
  return i


