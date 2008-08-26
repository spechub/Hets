{- |
Module      :  $Header$
Description :  embedding from CASL to VSE, plus wrapping procedures
               with default implementations
Copyright   :  (c) M.Codescu, DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Mihai.Codescu@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to VSE.
-}

module Comorphisms.CASL2VSEImport (CASL2VSEImport(..)
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

-- | The identity of the comorphism
data CASL2VSEImport = CASL2VSEImport deriving (Show)

instance Language CASL2VSEImport -- default definition is okay

instance Comorphism CASL2VSEImport
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
    sourceLogic CASL2VSEImport = CASL
    sourceSublogic CASL2VSEImport = SL.top
    targetLogic CASL2VSEImport = VSE
    mapSublogic CASL2VSEImport _ = Just ()
    map_theory CASL2VSEImport = mapCASLTheory
    map_morphism CASL2VSEImport = return . mapMor
    map_sentence CASL2VSEImport _ = return . mapSen
    map_symbol CASL2VSEImport = error "nyi"
      -- check these 3, but should be fine
    has_model_expansion CASL2VSEImport = True
    is_weakly_amalgamable CASL2VSEImport = True
    isInclusionComorphism CASL2VSEImport = True


mapCASLTheory :: (CASLSign, [Named CASLFORMULA]) ->
                 Result (VSESign, [Named Sentence])
mapCASLTheory (sig, n_sens) = do
  let (tsig, genAx) =  mapSig sig
      tsens = map mapNamedSen n_sens
  case not $ null $ checkCases tsig (tsens ++ genAx) of
   True -> fail "case error in signature"
   _ -> return (tsig, tsens ++ genAx)

mapSig :: CASLSign -> (VSESign, [Named Sentence])
mapSig sign =
 let wrapSort (procsym, axs) s = let
        restrName = stringToId $ genNamePrefix ++ "restr_"++show s
        --uniformName = stringToId $ genNamePrefix ++ "uniform_"++show s
        eqName = stringToId $ genNamePrefix ++ "eq_"++show s
        sProcs = [(restrName, Profile [Procparam In s] Nothing),
                   --(uniformName, Profile [Procparam In s] Nothing),
                   (eqName,
                     Profile [Procparam In s, Procparam In s]
                             (Just uBoolean))]
        sSens = [makeNamed ("ga_restriction_" ++ show s) $ ExtFORMULA $
                 Ranged
                  (Defprocs
                   [Defproc Proc restrName [mkSimpleId $ genNamePrefix ++ "x"]
                   (Ranged (Block [] (Ranged Skip nullRange)) nullRange)
                           nullRange])
                  nullRange,
                 makeNamed ("ga_equality_"++ show s) $ ExtFORMULA $
                 Ranged
                  (Defprocs
                   [Defproc Func eqName (map mkSimpleId ["x","y"])
                   (Ranged (Block [] (Ranged
                                       (If (Strong_equation
                        (Qual_var (mkSimpleId "x") s nullRange)
                        (Qual_var (mkSimpleId "y") s nullRange)
                        nullRange)
                                         (Ranged (Return
                            (Application (Qual_op_name uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                                         [] nullRange)
                                         ) nullRange)
                                         (Ranged (Return
                            (Application (Qual_op_name uFalse
                                            (Op_type Total []
                                               uBoolean
                                           nullRange)nullRange)
                                         [] nullRange) )
                                         nullRange))
                                        nullRange)) nullRange)
                           nullRange])
                  nullRange
                ]
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
       fSens = map (\ (OpType fKind w s) -> let
                      vars = map (\(t,n) -> (genToken ("x"++ (show n)), t)) $
                             zip w [1::Int ..]
                                      in
                   makeNamed "" $ ExtFORMULA $ Ranged
                     (Defprocs
                       [Defproc
                         Func funName (map fst vars)
                         ( Ranged (Block []
                         (Ranged
                            (Block
                              [Var_decl [genToken "y"] s nullRange]
                              (Ranged
                                (Seq

                                 (Ranged
                                   (Assign
                                     (genToken "y")
                                     (Application
                                      (Qual_op_name i
                                        (Op_type fKind w s nullRange)
                                       nullRange )
                                      (map  (\(v,ss) ->
                                              Qual_var v ss nullRange) vars)
                                      nullRange))
                                   nullRange)

                                 (Ranged
                                   (Return
                                    (Qual_var (genToken "y") s nullRange))
                                   nullRange)

                                )--end seq
                               nullRange)
                              )--end block
                            nullRange)-- end procedure body
                            ) nullRange)
                         nullRange]
                     )
                     nullRange
                   ) opTypes
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
       pSens = map (\ (PredType w) -> let
                      vars = map (\(t,n) -> (genToken ("x"++ (show n)), t)) $
                             zip w [1::Int ..]
                                      in
                   makeNamed "" $ ExtFORMULA $ Ranged
                     (Defprocs
                       [Defproc
                         Func procName (map fst vars)
                         (Ranged (Block [](Ranged
                            ( If
                               (Predication
                                        (Qual_pred_name
                                          i
                                         (Pred_type
                                           (map snd vars)
                                           nullRange)
                                        nullRange)
                                        (map (\(v,ss) ->
                                               Qual_var v ss nullRange) vars)
                                       nullRange)
                                (Ranged
                                 (Return
                                   (Application (Qual_op_name
                                          uTrue
                                          (Op_type Total []
                                            uBoolean
                                           nullRange) nullRange)
                                         [] nullRange))
                                  nullRange)
                                (Ranged
                                (Return
                                (Application (Qual_op_name uFalse
                                          (Op_type Total []
                                            uBoolean
                                           nullRange)nullRange)
                                         [] nullRange)
                                )  nullRange)) nullRange)
                              )--block
                            nullRange)
                          nullRange]
                     )
                     nullRange
                   ) predTypes
                                                in
      (procsym ++ pProcs, axs ++ pSens)
     (predProcs, predSens) = foldl wrapPred ([],[]) $
                                        Map.toList $ predMap sign
     procs = Procs $ Map.fromList (sortProcs ++ opProcs ++ predProcs)
     newPreds = procsToPredMap procs
     newOps = procsToOpMap procs
 in(sign { opMap = addOpMapSet (opMap sign) newOps,
           predMap = addMapSet (predMap sign) newPreds,
           extendedInfo = procs,
           sentences = [] }, sortSens ++ opSens ++ predSens)

mapNamedSen :: Named CASLFORMULA -> Named Sentence
mapNamedSen n_sen = let
 sen = sentence n_sen
                    in
 n_sen{sentence = mapSen sen}

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
                OpType Partial [s,s] (uBoolean)) ,
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
  , fun_map = Map.union (Map.union eqOps opsProcs) $ fun_map m
  , pred_map = Map.union (Map.union restrPreds predProcs) $ pred_map m
  }
