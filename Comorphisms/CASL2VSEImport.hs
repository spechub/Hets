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
    map_morphism CASL2VSEImport = error "nyi"
    map_sentence CASL2VSEImport _ = return . mapSen
    map_symbol CASL2VSEImport = error "nyi"
      -- check these 3, but should be fine
    has_model_expansion CASL2VSEImport = True
    is_weakly_amalgamable CASL2VSEImport = True
    isInclusionComorphism CASL2VSEImport = False


mapCASLTheory :: (CASLSign, [Named CASLFORMULA]) ->
                 Result (VSESign, [Named Sentence])
mapCASLTheory (sig, n_sens) = do
  let (tsig, genAx) =  mapSig sig
      tsens = concatMap mapNamedSen n_sens
  return (tsig, tsens ++ genAx)

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
                            (Application (Qual_op_name (stringToId "True")
                                          (Op_type Total []
                                            (stringToId "Boolean")
                                           nullRange)nullRange)
                                         [] nullRange)
                                         ) nullRange)
                                         (Ranged (Return
                            (Application (Qual_op_name (stringToId "False")
                                            (Op_type Total []
                                               (stringToId "Boolean")
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
                           (Just $ stringToId "Boolean"))) predTypes
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
                                          (stringToId "True")
                                          (Op_type Total []
                                            (stringToId "Boolean")
                                           nullRange) nullRange)
                                         [] nullRange))
                                  nullRange)
                                (Ranged
                                (Return
                                (Application (Qual_op_name (stringToId "False")
                                          (Op_type Total []
                                            (stringToId "Boolean")
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
                                     (Op_type fK args sn _)
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
                                      (Qual_op_name ctor
                                        (Op_type fK args sn nullRange)
                                        nullRange)
                                      (map  (\(v,ss) ->
                                              Qual_var v ss nullRange) $
                                       zip decls args)
                                      nullRange))
                                   nullRange)
                        )
                        (Ranged (If (Strong_equation
                               (Qual_var
                                  (genToken "y")
                                  sn nullRange)
                               (Qual_var
                                 (genToken  "x")
                                 sn nullRange)
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
