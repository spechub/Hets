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
import Data.List(sortBy)

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
    map_sentence CASL2VSERefine _ = return. mapSen
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
                          (Predication (Pred_name restrName)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name restrName)
                            [vary] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange
                   ] nullRange)
                  (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name eqName)
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
                          (Predication (Pred_name restrName)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange)

                     (ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name eqName)
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
                          (Predication (Pred_name restrName)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name restrName)
                            [vary] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                    ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name eqName)
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
                          (Predication (Pred_name eqName)
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
                          (Predication (Pred_name restrName)
                            [varx] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name restrName)
                            [vary] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                   ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name restrName)
                            [varz] nullRange))
                          nullRange)
                      (True_atom nullRange) ) nullRange,
                    ExtFORMULA $ Ranged
                     (Dlformula Diamond
                      (Ranged
                        (Call
                          (Predication (Pred_name eqName)
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
                          (Predication (Pred_name eqName)
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
                          (Predication (Pred_name eqName)
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
                                   (Pred_name $  stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Pred_name $  stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                   [yv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Pred_name $ stringToId $
                                     genNamePrefix ++ "eq_" ++ show si)
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
                   nullRange )--ipoteza
                  (ExtFORMULA $ Ranged (
                     Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Pred_name $ stringToId $
                                       genNamePrefix ++ show i)
                                   ((map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "x" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]) ++ [xvar]) nullRange)) nullRange)
                      (ExtFORMULA $ Ranged (
                         Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Pred_name $ stringToId $
                                     genNamePrefix ++ show i)
                                   ((map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "y" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]) ++ [yvar]) nullRange)) nullRange)
                       (ExtFORMULA $
                        Ranged (
                          Dlformula Diamond
                          ( Ranged
                        (Call
                          (Predication (Pred_name $ stringToId $
                              genNamePrefix ++ "eq_" ++ show s )
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
                   ) nullRange) --concluzia
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
                                   (Pred_name $  stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
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
                         (Call (Predication (Pred_name $ stringToId $
                                             genNamePrefix ++ show i)
                          (xvars ++[xvar])
                          nullRange))
                        nullRange)
                       (ExtFORMULA $
                         Ranged
                         (Dlformula Diamond (Ranged
                          (Call (Predication (Pred_name $ stringToId $
                              genNamePrefix ++ "restr_" ++ show s )
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
                         (Call (Predication (Pred_name $ stringToId $
                                              genNamePrefix ++ show i)
                              [xvar] nullRange))
                        nullRange)
                       (ExtFORMULA $
                         Ranged
                         (Dlformula Diamond (Ranged
                          (Call (Predication (Pred_name $ stringToId $
                              genNamePrefix ++ "restr_" ++ show s )
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
                                   (Pred_name $  stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                   [xv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Pred_name $  stringToId $
                                     genNamePrefix ++ "restr_" ++ show si)
                                   [yv] nullRange))
                               nullRange)
                          (True_atom nullRange) ) nullRange ,
                       ExtFORMULA $ Ranged ( Dlformula Diamond
                              (Ranged
                                (Call
                                 (Predication
                                   (Pred_name $ stringToId $
                                     genNamePrefix ++ "eq_" ++ show si)
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
                   nullRange )--ipoteza
                  (ExtFORMULA $ Ranged (
                     Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Pred_name $ stringToId $
                                                genNamePrefix ++ show i)
                                   ((map (
                  \(si, ii) ->
                  Qual_var (mkSimpleId $ genNamePrefix ++ "x" ++ show ii )
                  si nullRange ) $
                   zip w [1::Int ..]) ++ [rvar1]) nullRange)) nullRange)
                      (ExtFORMULA $ Ranged (
                         Dlformula Diamond
                      (Ranged (Call (Predication
                                   (Pred_name $ stringToId $
                                                genNamePrefix ++ show i)
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
                   ) nullRange) --concluzia
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
                                    (Pred_name $  stringToId $
                                      genNamePrefix ++ "restr_" ++ show si)
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
                          (Call (Predication (Pred_name $ stringToId $
                                               genNamePrefix ++ show i)
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
 trans = mapSen sen
                    in
 case sen of
  Sort_gen_ax constrs _isFree -> let
    (genSorts, genOps, _maps) = recover_Sort_gen_ax constrs
    genUniform sorts ops s = let
      hasResSort sn (Qual_op_name _ opType _) = (res_OP_TYPE opType) == sn
      ctors = sortBy (\ (Qual_op_name _ (Op_type _ args1 _ _) _)
                        (Qual_op_name _ (Op_type _ args2 _ _) _) ->
                        if length args1 < length args2 then LT else GT) $
              filter (hasResSort s) ops
      genCodeForCtor (Qual_op_name
                                     ctor
                                     (Op_type _ args sn _)
                                  _) prg = let
        decls = map (\(_, i) -> genToken $ "x" ++ show i) $
                zip args [1::Int ..]
        recCalls = map (\(x,i) ->
                         Ranged (Call (Predication
                                        (Qual_pred_name (stringToId $
                                                 genNamePrefix ++ "uniform_"
                                                 ++ show x)
                                         (Pred_type [x] nullRange) nullRange)
                                        [Qual_var
                                          (genToken $ "x" ++ show i)
                                          x nullRange] nullRange
                                      )) nullRange) $
                   filter (\(x,_) -> x `elem` sorts) $
                   zip args [1::Int ..]
        recCallsSeq = if not $ null recCalls then
                      foldr1 (\p1 p2 -> Ranged (Seq p1 p2) nullRange) recCalls
                      else Ranged Skip nullRange
                                          in Ranged (
       Block ([Var_decl [genToken "y"] s nullRange] ++
              (map (\ (a,i) -> Var_decl [genToken $ "x" ++ show i] a nullRange)
              $ zip args [1::Int ..]))
       (Ranged
         (Seq
           (Ranged
            (Assign
             (genToken "y")
             (Qual_var (genToken "x") sn nullRange)
            )
           nullRange)
           (Ranged
             (Seq recCallsSeq
              (Ranged (Seq
                        ((Ranged
                                   (Assign
                                     (genToken  "y")
                                     (Application
                                      (Op_name ctor)
                                      (map  (\(v,ss) ->
                                              Qual_var v ss nullRange) $
                                       zip decls args)
                                      nullRange))
                                   nullRange)
                        )
                        (Ranged (If (Strong_equation
                               (Application
                                 (
                                  Qual_op_name
                                   (stringToId $ genNamePrefix ++ "eq_"++
                                                 show s)
                                   (Op_type Partial [s,s]
                                    uBoolean nullRange)
                                  nullRange
                                 ) [Qual_var
                                      (genToken "x")
                                      s nullRange,
                                     Qual_var
                                      (genToken "y")
                                      s nullRange
                                    ] nullRange)
                               (Application
                                 (Qual_op_name (stringToId  "True")
                                  (Op_type Total []
                                    uBoolean nullRange)
                                  nullRange)
                                 [] nullRange)
                             nullRange)
                          (Ranged Skip nullRange)
                          prg)nullRange))
               nullRange
              )
             )
           nullRange
           )
         )
       nullRange) ) nullRange
                             in
     ExtFORMULA $
     Ranged (Defprocs  [
      Defproc Proc (stringToId $ genNamePrefix ++ "uniform_"++show s)
              [mkSimpleId $ genNamePrefix ++ "x"]
      (Ranged (
        Block [] ( foldr genCodeForCtor (Ranged Abort nullRange)
                   ctors)
              ) nullRange
      )
      nullRange])
     nullRange
    procDefs = map (genUniform genSorts genOps) genSorts
                                 in
     map (makeNamed "") (trans:procDefs)
  _ -> [n_sen{sentence = trans}]

mapSen :: CASLFORMULA -> Sentence
mapSen f = case f of
    Quantification q vs frm ps ->
        Quantification q vs (mapSen frm) ps
    Conjunction fs ps ->
        Conjunction (map mapSen fs) ps
    Disjunction fs ps ->
        Disjunction (map mapSen fs) ps
    Implication f1 f2 b ps ->
        Implication (mapSen f1) (mapSen f2) b ps
    Equivalence f1 f2 ps ->
        Equivalence (mapSen f1) (mapSen f2) ps
    Negation frm ps -> Negation (mapSen frm) ps
    True_atom ps -> True_atom ps
    False_atom ps -> False_atom ps
    Existl_equation t1 t2 ps ->
        Existl_equation (mapTERM t1) (mapTERM t2) ps
    Strong_equation t1 t2 ps ->
        Strong_equation (mapTERM t1) (mapTERM t2) ps
    Predication pn as qs ->
        Predication pn (map mapTERM as) qs
    Definedness t ps -> Definedness (mapTERM t) ps
    Membership t ty ps -> Membership (mapTERM t) ty ps
    Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
    _ -> error "CASL2VSEImport.mapSen"

mapTERM :: TERM () -> TERM Dlformula
mapTERM t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs  -> Application opsym (map mapTERM as) qs
    Sorted_term trm ty ps -> Sorted_term (mapTERM trm) ty ps
    Cast trm ty ps -> Cast (mapTERM trm) ty ps
    Conditional t1 f t2 ps ->
       Conditional (mapTERM t1) (mapSen f) (mapTERM t2) ps
    _ -> error "CASL2VSEImport.mapTERM"

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
