{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables #-}
{- |
Module      :  ./Comorphisms/SuleCFOL2TPTP.hs
Description :  Coding of a CASL subset into TPTP
Copyright   :  (c) Eugen Kuksa and Till Mossakowksi
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  kuksa@iks.cs.ovgu.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from a CASL subset to TPTP.
-}

module Comorphisms.SuleCFOL2TPTP
  ( suleCFOL2TPTP
  ) where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.AS_Annotation hiding (sentence)
import qualified Common.AS_Annotation as AS_Annotation (sentence)
import Common.Id
import Common.Result
import Common.ProofTree
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.List as List hiding (sort)
import Data.Char
import Numeric (showHex)

import CASL.Logic_CASL
import CASL.AS_Basic_CASL as CAS
import CASL.Sublogic as SL
import CASL.Sign as CSign hiding (sentences)
import CASL.Morphism
import CASL.Overload
import CASL.Utils
import CASL.ToDoc

import TPTP.AS as TAS hiding (name)
import TPTP.Morphism as TMorphism
import TPTP.Sign as TSign
import TPTP.Logic_TPTP
import TPTP.Sublogic

import qualified Comorphisms.SuleCFOL2SoftFOL as CASL2SoftFOL

import Debug.Trace

data TPTP_FOF = TPTP_FOF

instance Show TPTP_FOF where
  show TPTP_FOF = "TPTP_FOF"

-- | The identity of the comorphisms
data GenSuleCFOL2TPTP = GenSuleCFOL2TPTP deriving Show

suleCFOL2TPTP :: GenSuleCFOL2TPTP
suleCFOL2TPTP = GenSuleCFOL2TPTP

-- | TPTP theories
type TPTPTheory = (TSign.Sign, [Named Sentence])

instance Language GenSuleCFOL2TPTP where
  language_name GenSuleCFOL2TPTP = "CASL2TPTP_FOF"

instance Comorphism GenSuleCFOL2TPTP
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               CSign.Symbol RawSymbol ProofTree
               TPTP.Logic_TPTP.TPTP Sublogic TAS.BASIC_SPEC Sentence () ()
               TSign.Sign TMorphism.Morphism TSign.Symbol () ProofTree where
    sourceLogic GenSuleCFOL2TPTP = CASL
    sourceSublogic GenSuleCFOL2TPTP = SL.cFol
                       { sub_features = LocFilSub
                      , cons_features = emptyMapConsFeature
                       , has_empty_sorts = True }
    sourceSublogicLossy GenSuleCFOL2TPTP = SL.fol
                      { sub_features = LocFilSub
                      , has_empty_sorts = True }
    targetLogic GenSuleCFOL2TPTP = TPTP.Logic_TPTP.TPTP
    mapSublogic _ _ = Just FOF
    map_theory GenSuleCFOL2TPTP = transTheory
    has_model_expansion GenSuleCFOL2TPTP = True
    extractModel GenSuleCFOL2TPTP s pt = trace ("pt:"++show pt) $  CASL2SoftFOL.extractCASLModel s pt

transTheory :: (FormExtension f, Eq f)
            => (CSign.Sign f e, [Named (FORMULA f)])
            -> Result TPTPTheory
transTheory (sign, sens) = do
  let signWithRenamings@(preparedSign, _, _) = prepareSign sign
  let preparedSens = map prepareNamedFormula sens
  (tptpSign, signSentences) <- translateSign preparedSign
  translatedSentences <- mapM (translateNamedFormula signWithRenamings) preparedSens
  return (tptpSign, signSentences ++ translatedSentences)

prepareNamedFormula :: (FormExtension f, Eq f)
                    => Named (FORMULA f) -> Named (FORMULA f)
prepareNamedFormula formula =
  let expandedFormula =
        codeOutConditionalF id $ -- Expand conditionals
        codeOutUniqueExtF id id $ -- Expand "exists!" quantification
        AS_Annotation.sentence formula
  in  formula { AS_Annotation.sentence = expandedFormula }

translateNamedFormula :: (FormExtension f, Eq f)
                      => SignWithRenamings f e
                      -> Named (FORMULA f) -> Result (Named TSign.Sentence)
translateNamedFormula signWithRenamings x = do
  let nameS = "ax_" ++ toAlphaNum (map toLower $ senAttr x)
  translated <-
    translateFormula signWithRenamings nameS (isAxiom x) $
      AS_Annotation.sentence x
  return $ x { AS_Annotation.sentence = translated
             }

translateFormula :: forall e f . (FormExtension f, Eq f)
                 => SignWithRenamings f e -> String -> Bool -> FORMULA f
                 -> Result TSign.Sentence
translateFormula signWithRenamings nameS isAxiom' formula = do
  let name = NameString $ mkSimpleId nameS
  fofFormula <- toUnitaryFormula formula
  return $ if isAxiom'
           then fofUnitaryFormulaToAxiom name fofFormula
           else fofUnitaryFormulaToConjecture name fofFormula
  where
    toUnitaryFormula :: (FormExtension f, Eq f)
                         => FORMULA f
                         -> Result FOF_unitary_formula
    toUnitaryFormula x = case x of
      Quantification q vars f _ -> do
        let fofVars = translateVarDecls vars
        let variableList = map fst fofVars
        let variableDeclaration =
              unitaryFormulaAnd $ map (uncurry sortOfX) fofVars
        fofF <- toUnitaryFormula f
        case q of
          Universal ->
            let implication =
                  FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                  FOF_binary_nonassoc TAS.Implication variableDeclaration fofF
            in  return $ FOFUF_quantified $
                         FOF_quantified_formula ForAll variableList implication
          Existential ->
            let conjunction = unitaryFormulaAnd [variableDeclaration, fofF]
            in  return $ FOFUF_quantified $
                         FOF_quantified_formula Exists variableList conjunction
          -- Has been resolved/removed by prepareNamedFormula:
          Unique_existential ->
            fail "SuleCFOL2TPTP: Unique_existential occurred where it cannot occur. This is a bug in Hets."
      Junction Con fs _ -> do
        fofs <- mapM toUnitaryFormula fs
        return $ unitaryFormulaAnd fofs
      Junction Dis fs _ -> do
        fofs <- mapM toUnitaryFormula fs
        return $ unitaryFormulaOr fofs
      Relation f1 CAS.Implication f2 _ -> do
        fof1 <- toUnitaryFormula f1
        fof2 <- toUnitaryFormula f2
        return $ FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                 FOF_binary_nonassoc TAS.Implication fof1 fof2
      -- For some reason, "f2 if f1" is saved as "Relation f1 RevImpl f2 _"
      Relation f1 RevImpl f2 _ -> do
        fof1 <- toUnitaryFormula f1
        fof2 <- toUnitaryFormula f2
        -- Flip the formulae:
        return $ FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                 FOF_binary_nonassoc ReverseImplication fof2 fof1
      Relation f1 CAS.Equivalence f2 _ -> do
        fof1 <- toUnitaryFormula f1
        fof2 <- toUnitaryFormula f2
        return $ FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                 FOF_binary_nonassoc TAS.Equivalence fof1 fof2
      Negation f _ -> do
        fofF <- toUnitaryFormula f
        return $ FOFUF_unary $ FOFUF_connective NOT fofF
      Atom True _ ->
        return $ FOFUF_atomic $ FOFAT_defined $ FOFDAF_plain $
                 FOFDPF_proposition $ TPTP_true
      Atom False _ ->
        return $ FOFUF_atomic $ FOFAT_defined $ FOFDAF_plain $
                 FOFDPF_proposition $ TPTP_false
      Predication predSymb terms _ -> do
        predName <- case predSymb of
              Pred_name _ ->
                fail "SuleCFOL2TPTP: An unqualified predicate has been detected. This is a bug in Hets."
              Qual_pred_name predName (Pred_type args _) _ ->
                return $ lookupPredName signWithRenamings predName $
                  PredType { predArgs = args }
        let predicate = predicateOfPred predName
        args <- mapM (translateTerm signWithRenamings) terms
        case args of
          [] -> return $ FOFUF_atomic $ FOFAT_plain $ FOFPAF_proposition predicate
          _ -> return $ FOFUF_atomic $ FOFAT_plain $ FOFPAF_predicate predicate args
      -- There is no Equation t1 Existl t2 in SuleCFOL
      Equation t1 Strong t2 _ -> do
        fofTerm1 <- translateTerm signWithRenamings t1
        fofTerm2 <- translateTerm signWithRenamings t2
        return $ FOFUF_atomic $ FOFAT_defined $ FOFDAF_infix $
                 FOF_defined_infix_formula
                 Defined_infix_equality fofTerm1 fofTerm2
      Membership term sort _ -> do
        fofTerm <- translateTerm signWithRenamings term
        return $ FOFUF_atomic $ FOFAT_plain $
                 FOFPAF_predicate (predicateOfSort sort) [fofTerm]
      -- Sort_gen_ax cannot be translated. Fail:
      -- See https://github.com/spechub/Hets/issues/1706
      Sort_gen_ax _ _ ->
        justWarn (FOFUF_atomic $ FOFAT_defined $ FOFDAF_plain $
                  FOFDPF_proposition $ TPTP_true)
                 "SuleCFOL2TPTP: Sort generation axioms are not yet supported."
      -- There is no Definedness in SuleCFOL
      -- There is no Mixfix_formula - it only occurs during parsing
      -- There is no Unparsed_formula
      -- There is no QuantOp in SuleCFOL
      -- There is no QuantPred in SuleCFOL
      -- There is no ExtFORMULA in SuleCFOL
      _ -> fail "SuleCFOL2TPTP: A formula that should not occur has occurred."

    translateVarDecls :: [VAR_DECL] -> [(TAS.Variable, SORT)]
    translateVarDecls = concatMap translateVarDecl

    translateVarDecl :: VAR_DECL -> [(TAS.Variable, SORT)]
    translateVarDecl x = case x of
      Var_decl vars sort _ -> zip (map variableOfVar vars) $ repeat sort

unitaryFormulaAnd :: FOF_and_formula -> FOF_unitary_formula
unitaryFormulaAnd = FOFUF_logic . FOFLF_binary . FOFBF_assoc . FOFBA_and

unitaryFormulaOr :: FOF_or_formula -> FOF_unitary_formula
unitaryFormulaOr = FOFUF_logic . FOFLF_binary . FOFBF_assoc . FOFBA_or


translateTerm :: (FormExtension f, Eq f)
              => SignWithRenamings f e
              -> TERM f
              -> Result TAS.FOF_term
translateTerm signWithRenamings x = case x of
  Qual_var var _ _ -> return $ FOFT_variable $ variableOfVar var
  Application opSymb terms _ -> do
    opName <- case opSymb of
          Op_name _ ->
            fail "SuleCFOL2TPTP: An unqualified operation has been detected. This is a bug in Hets."
          Qual_op_name opName (Op_type kind args res _) _ ->
            return $ lookupOpName signWithRenamings opName $
              OpType { opKind = kind, opArgs = args, opRes = res }
    let function = functionOfOp opName
    args <- mapM (translateTerm signWithRenamings) terms
    case args of
      [] -> return $ FOFT_function $ FOFFT_plain $ FOFPT_constant $ function
      _ -> return $ FOFT_function $ FOFFT_plain $ FOFPT_functor function args
  -- The sort can be ignored:
  Sorted_term term _ _ -> translateTerm signWithRenamings term
  -- Conditional has been resolved/removed in prepareNamedFormula
  -- There is no Cast in SuleCFOL
  -- Everything else cannot occur
  _ -> fail "SuleCFOL2TPTP: A term that should not occur has occurred."


fofUnitaryFormulaToAxiom :: TAS.Name -> FOF_unitary_formula -> TSign.Sentence
fofUnitaryFormulaToAxiom name f =
  let formula = FOFF_logic $ FOFLF_unitary f
  in  AF_FOF_Annotated $ FOF_annotated name Axiom formula (Annotations Nothing)

fofUnitaryFormulaToConjecture :: TAS.Name -> FOF_unitary_formula
                              -> TSign.Sentence
fofUnitaryFormulaToConjecture name f =
  let formula = FOFF_logic $ FOFLF_unitary f
  in  AF_FOF_Annotated $
        FOF_annotated name Conjecture formula (Annotations Nothing)

lookupOpName :: (FormExtension f, Eq f)
             => SignWithRenamings f e -> OP_NAME -> OpType -> OP_NAME
lookupOpName (_, renamedOps, _) opName opType =
  Map.findWithDefault opName (opName, opType) renamedOps

lookupPredName :: (FormExtension f, Eq f)
             => SignWithRenamings f e -> PRED_NAME -> PredType -> PRED_NAME
lookupPredName (_, _, renamedPreds) predName predType =
  Map.findWithDefault predName (predName, predType) renamedPreds

-- Ops and Preds in the overloading relation must be renamed.
-- This type contains the Sign with renaming applied and the information what
-- each original op+type or pred+type was renamed to.
type SignWithRenamings f e = (CSign.Sign f e,
                              Map.Map (OP_NAME, OpType) OP_NAME,
                              Map.Map (PRED_NAME, PredType) PRED_NAME)

-- finds ops and preds that have the same name but operate on different connected components. Renames these ops and preds.
prepareSign :: (FormExtension f, Eq f)
            => CSign.Sign f e -> SignWithRenamings f e
prepareSign sign =
  let connectedComponents = gatherConnectedComponents sign
      connectedComponentMap = connectedComponentsToMap connectedComponents
      renamedOps =
        Map.foldrWithKey (addOpIfConflicting connectedComponentMap) Map.empty $
          MapSet.toMap $ opMap sign
      renamedPreds =
        Map.foldrWithKey (addPredIfConflicting connectedComponentMap) Map.empty $
          MapSet.toMap $ predMap sign
      renamedOpMap =
        MapSet.foldWithKey (modifyOpMap renamedOps) (opMap sign) $ opMap sign
      renamedPredMap =
        MapSet.foldWithKey (modifyPredMap renamedPreds) (predMap sign) $ predMap sign
  in  (sign { opMap = renamedOpMap, predMap = renamedPredMap},
       renamedOps,
       renamedPreds)
  where
    gatherConnectedComponents :: (FormExtension f, Eq f)
                              => CSign.Sign f e -> [Set.Set SORT]
    gatherConnectedComponents sign' =
      let topSortsL = Set.toList $ Rel.mostRight $ sortRel sign'
          revReflTransClosureSortRel =
            Rel.transpose $ Rel.reflexive $ Rel.transClosure $ sortRel sign'
      in  map (\ topSort -> Set.insert topSort $
            Rel.succs revReflTransClosureSortRel topSort) topSortsL

    -- Maps a SORT to the index of the connected Component
    connectedComponentsToMap :: [Set.Set SORT] -> Map.Map SORT Int
    connectedComponentsToMap connectedComponents =
      let indexedCCs = zip connectedComponents [1..]
      in  foldr (\ (cc, i) ccMap ->
                  Set.foldr (\ sort ccMap' ->
                              Map.insert sort i ccMap'
                            ) ccMap cc
                ) Map.empty indexedCCs

    addOpIfConflicting :: Map.Map SORT Int -> OP_NAME -> Set.Set OpType
                       -> Map.Map (OP_NAME, OpType) OP_NAME
                       -> Map.Map (OP_NAME, OpType) OP_NAME
    addOpIfConflicting connectedComponentMap opName opTypes conflicts =
      let opTypesL = Set.toList opTypes
          opTypeCombinations = [(x,y) | x <- opTypesL, y <- opTypesL, x < y]
      in  foldr addIfConflicting conflicts opTypeCombinations
      where
        addIfConflicting :: (OpType, OpType)
                         -> Map.Map (OP_NAME, OpType) OP_NAME
                         -> Map.Map (OP_NAME, OpType) OP_NAME
        addIfConflicting (t1, t2) conflicts' =
          if isConflicting t1 t2
          then Map.insert (opName, t1) (renameCurrentOp t1) $
                 Map.insert (opName, t2) (renameCurrentOp t2) conflicts'
          else if hasAllArgsInSameCC t1 t2
               then let greaterOpType = if leqOpType t1 t2 then t2 else t1 in
                    Map.insert (opName, t1) (renameCurrentOp greaterOpType) $
                      Map.insert (opName, t2) (renameCurrentOp greaterOpType) conflicts'
               else conflicts'

        leqOpType :: OpType -> OpType -> Bool
        leqOpType t1 t2 = all (uncurry $ leqSort sign) $
          zip (opArgs t1 ++ [opRes t1]) (opArgs t2 ++ [opRes t2])

        isConflicting :: OpType -> OpType -> Bool
        isConflicting t1 t2 =
          hasAllArgsInSameCC t1 t2 && not (leqF sign t1 t2 || leqF sign t2 t1)

        hasAllArgsInSameCC :: OpType -> OpType -> Bool
        hasAllArgsInSameCC t1 t2 =
          let sameNumberOfArgs = length (opArgs t1) == length (opArgs t2)
              allArgsInSameCC =
                all (isInSameCC connectedComponentMap) $
                  zip (opArgs t1) (opArgs t2)
          in sameNumberOfArgs && allArgsInSameCC

        renameCurrentOp :: OpType -> OP_NAME
        renameCurrentOp opType =
          let argsS =
                intercalate "_" $ map (toAlphaNum . show) $ opArgs opType
              resultS = toAlphaNum $ show $ opRes opType
              newOpNameS =
                toAlphaNum (show opName) ++ "_" ++ argsS ++ "_" ++ resultS
          in  opName { getTokens = [mkSimpleId newOpNameS] }

    addPredIfConflicting :: Map.Map SORT Int -> PRED_NAME -> Set.Set PredType
                         -> Map.Map (PRED_NAME, PredType) PRED_NAME
                         -> Map.Map (PRED_NAME, PredType) PRED_NAME
    addPredIfConflicting connectedComponentMap predName predTypes conflicts =
      let predTypesL = Set.toList predTypes
          predTypeCombinations =
            [(x,y) | x <- predTypesL, y <- predTypesL, x < y]
      in  foldr addIfConflicting conflicts predTypeCombinations
      where
        addIfConflicting :: (PredType, PredType)
                         -> Map.Map (PRED_NAME, PredType) PRED_NAME
                         -> Map.Map (PRED_NAME, PredType) PRED_NAME
        addIfConflicting (t1, t2) conflicts' =
          if isConflicting t1 t2
          then Map.insert (predName, t1) (renameCurrentPred t1) $
                 Map.insert (predName, t2) (renameCurrentPred t2) conflicts'
          else if hasAllArgsInSameCC t1 t2
               then let greaterPredType = if leqPredType t1 t2 then t2 else t1 in
                    Map.insert (predName, t1) (renameCurrentPred greaterPredType) $
                      Map.insert (predName, t2) (renameCurrentPred greaterPredType) conflicts'
               else conflicts'

        isConflicting :: PredType -> PredType -> Bool
        isConflicting t1 t2 =
          hasAllArgsInSameCC t1 t2 && not (leqP sign t1 t2 || leqP sign t2 t1)

        leqPredType :: PredType -> PredType -> Bool
        leqPredType t1 t2 = all (uncurry $ leqSort sign) $
          zip (predArgs t1) (predArgs t2)

        hasAllArgsInSameCC :: PredType -> PredType -> Bool
        hasAllArgsInSameCC t1 t2 =
          let sameNumberOfArgs = length (predArgs t1) == length (predArgs t2)
              allArgsInSameCC =
                all (isInSameCC connectedComponentMap) $
                  zip (predArgs t1) (predArgs t2)
          in sameNumberOfArgs && allArgsInSameCC

        renameCurrentPred :: PredType -> PRED_NAME
        renameCurrentPred predType =
          let argsS =
                intercalate "_" $ map (toAlphaNum . show) $ predArgs predType
              newPredNameS = toAlphaNum (show predName) ++ "_" ++ argsS
          in  predName { getTokens = [mkSimpleId newPredNameS] }

    isInSameCC :: Map.Map SORT Int -> (SORT, SORT) -> Bool
    isInSameCC connectedComponentMap (s1, s2) =
      let cc1 = Map.lookup s1 connectedComponentMap
          cc2 = Map.lookup s2 connectedComponentMap
      in  cc1 == cc2 && cc1 /= Nothing -- Nothing can not occur

    modifyOpMap :: Map.Map (OP_NAME, OpType) OP_NAME
                -> OP_NAME -> OpType -> OpMap -> OpMap
    modifyOpMap renamedOps opName opType opMap' =
      case Map.lookup (opName, opType) renamedOps of
        Nothing -> opMap'
        Just newOpName -> MapSet.insert newOpName opType $
                            MapSet.delete opName opType opMap'

    modifyPredMap :: Map.Map (PRED_NAME, PredType) PRED_NAME
                  -> PRED_NAME -> PredType -> PredMap -> PredMap
    modifyPredMap renamedPreds predName predType predMap' =
      case Map.lookup (predName, predType) renamedPreds of
        Nothing -> predMap'
        Just newPredName -> MapSet.insert newPredName predType $
                              MapSet.delete predName predType predMap'


translateSign :: (FormExtension f, Eq f)
              => CSign.Sign f e -> Result (TSign.Sign, [Named TSign.Sentence])
translateSign caslSign =
  return (tptpSign, sentencesOfSorts ++ sentencesOfOps)
  where
    tptpSign :: TSign.Sign
    tptpSign =
      let predicatesOfSorts =
            Set.foldr (\ sort predicates' ->
                        Map.insertWith
                          Set.union
                          (predicateOfSort sort)
                          (Set.singleton 1)
                          predicates'
                      ) Map.empty $ Rel.nodes $ sortRel caslSign
          constants =
            MapSet.foldWithKey (\ opName opType constants' ->
                                 if null $ opArgs opType
                                 then Set.insert
                                        (functionOfOp opName)
                                        constants'
                                 else constants'
                               ) Set.empty $ opMap caslSign
          -- numbers cannot be generated due to prefix "function_"
          propositions =
            MapSet.foldWithKey (\ predName predType propositions' ->
                                 if null $ predArgs predType
                                 then Set.insert
                                        (predicateOfPred predName)
                                        propositions'
                                 else propositions'
                               ) Set.empty $ predMap caslSign
          predicatesWithoutSorts =
            MapSet.foldWithKey (\ predName predType predicates' ->
                                 if not $ null $ predArgs predType
                                 then Map.insertWith
                                       Set.union
                                       (predicateOfPred predName)
                                       (Set.singleton $ length $
                                         predArgs predType)
                                       predicates'
                                 else predicates'
                               ) Map.empty $ predMap caslSign
          predicates =
            Map.unionWith Set.union predicatesOfSorts predicatesWithoutSorts
          functors =
            MapSet.foldWithKey (\ opName opType functors' ->
                                 if not $ null $ opArgs opType
                                 then Map.insertWith
                                        Set.union
                                        (functionOfOp opName)
                                        (Set.singleton $ length $ opArgs opType)
                                        functors'
                                 else functors'
                               ) Map.empty $ opMap caslSign
      in  TSign.emptySign { constantSet = constants
                          , propositionSet = propositions
                          , fofPredicateMap = predicates
                          , fofFunctorMap = functors
                          }

    sentencesOfSorts :: [Named TSign.Sentence]
    sentencesOfSorts =
      let sortMap = Rel.toMap $ sortRel caslSign
          emptySorts = emptySortSet caslSign
          topSorts = Rel.mostRight $ sortRel caslSign
          subsortSentences =
            Map.foldrWithKey (createSubsortSentences emptySorts) [] sortMap
          topSortSentences =
            Set.foldr (createTopSortSentences topSorts) [] topSorts
      in  subsortSentences ++ topSortSentences

    createSubsortSentences :: Set.Set SORT -> SORT -> Set.Set SORT
                           -> [Named TSign.Sentence] -> [Named TSign.Sentence]
    createSubsortSentences emptySorts sort supersorts sentences =
      let subsortSentences = Set.foldr
            (\ supersort sens -> createSubsortSentence supersort sort : sens)
            [] supersorts
          nonEmptySortsSentence =
            if Set.member sort emptySorts
            then []
            else [createNonEmptySortSentence sort]
      in  subsortSentences ++ nonEmptySortsSentence ++ sentences

    -- creates:
    -- fof(sort_SUBSORT_subsort_of_SORT, axiom, ! [X]: (SUBSORT(X) => SORT(X))).
    createSubsortSentence :: SORT -> SORT -> Named TSign.Sentence
    createSubsortSentence sort subsort =
      let varX = variableOfVar $ mkSimpleId "X"
          nameString =
            "sign_" ++ toAlphaNum (show subsort) ++
            "_subsort_of_" ++ toAlphaNum (show sort)
          name = NameString $ mkSimpleId nameString
          formula = FOFUF_quantified $
            FOF_quantified_formula ForAll [varX] $
            FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
            FOF_binary_nonassoc
              TAS.Implication (sortOfX varX subsort) (sortOfX varX sort)
          sentence = fofUnitaryFormulaToAxiom name formula
      in  makeNamed nameString sentence

    -- creates:
    -- fof(sign_non_empty_sort_SORTNAME, axiom, ? [X]: (SORT(X))).
    createNonEmptySortSentence :: SORT -> Named TSign.Sentence
    createNonEmptySortSentence sort =
      let varX = variableOfVar $ mkSimpleId "X"
          nameString = "sign_non_empty_sort_" ++ toAlphaNum (show sort)
          name = NameString $ mkSimpleId nameString
          formula = FOFUF_quantified $
            FOF_quantified_formula Exists [varX] $
            FOFUF_logic $ FOFLF_unitary $ sortOfX varX sort
          sentence = fofUnitaryFormulaToAxiom name formula
      in  makeNamed nameString sentence

    createTopSortSentences :: Set.Set SORT -> SORT
                           -> [Named TSign.Sentence] -> [Named TSign.Sentence]
    createTopSortSentences topSorts sort sentences =
      let otherTopSorts = Set.delete sort topSorts
      in  if Set.null otherTopSorts
          then []
          else createTopSortSentence otherTopSorts sort : sentences
      where
        -- creates:
        -- fof(sign_topsort_SORT, axiom,
        --   ! [X]: (SORT(X) => ~ OTHER_SORT1(X) & ... & ~ OTHER_SORTn(X)).
        createTopSortSentence :: Set.Set SORT -> SORT -> Named TSign.Sentence
        createTopSortSentence otherTopSorts sort' =
          let varX = variableOfVar $ mkSimpleId "X"
              nameString = "sign_topsort_" ++ toAlphaNum (show sort')
              name = NameString $ mkSimpleId nameString

              formula = FOFUF_quantified $
                FOF_quantified_formula ForAll [varX] $
                FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                FOF_binary_nonassoc
                  TAS.Implication
                  (sortOfX varX sort') $
                  unitaryFormulaAnd $
                  Set.toList $
                  Set.map (negateUnitaryFormula . sortOfX varX) otherTopSorts

              sentence = fofUnitaryFormulaToAxiom name formula
          in  makeNamed nameString sentence

    negateUnitaryFormula :: FOF_unitary_formula -> FOF_unitary_formula
    negateUnitaryFormula f = FOFUF_unary $ FOFUF_connective NOT f

    sentencesOfOps :: [Named TSign.Sentence]
    sentencesOfOps =
      Map.foldrWithKey createSentencesOfOp [] $ MapSet.toMap $ opMap caslSign
      where
        createSentencesOfOp :: OP_NAME -> Set.Set OpType
                            -> [Named TSign.Sentence] -> [Named TSign.Sentence]
        createSentencesOfOp opName opTypes sentences =
          -- Assign a new sentence name to each type of the op by adding a suffix
          let useNameSuffix = Set.size opTypes > 1
              (sentencesOfThisOp, _) = Set.foldr
                (\ opType (sens, i) ->
                  (createSentenceOfOp
                    (if useNameSuffix then "_" ++ show (i :: Int) else "")
                    opName opType : sens, i + 1))
                ([], 1) opTypes
          in  sentencesOfThisOp ++ sentences

        -- creates either:
        -- fof(sign_op_OPNAME, axiom, S(op)).
        -- or:
        -- fof(sign_op_OPNAME, axiom,
        --      ! [X1, ..., Xn]: S1(X1) & ... & Sn(Xn) => S(op(X1, ..., Xn))).
        createSentenceOfOp :: String -> OP_NAME -> OpType
                           -> Named TSign.Sentence
        createSentenceOfOp nameSuffix opName opType =
          let nameString =
                "sign_op" ++ nameSuffix ++ "_" ++ toAlphaNum (show opName)
              name = NameString $ mkSimpleId nameString

              predicateResult = predicateOfSort $ opRes opType
              predicates = map predicateOfSort $ opArgs opType
              variables =
                map (\ i -> variableOfVar $ mkSimpleId $ "X" ++ show i)
                  [1 .. length (opArgs opType)]
              function = functionOfOp opName

              functionAntecedent = unitaryFormulaAnd $
                map (\ (v, p) ->
                      FOFUF_atomic $ FOFAT_plain $ FOFPAF_predicate p
                      [FOFT_function $ FOFFT_plain $ FOFPT_constant $ v]) $
                  zip variables predicates
              functionConsequent = FOFUF_atomic $ FOFAT_plain $
                FOFPAF_predicate predicateResult
                [FOFT_function $ FOFFT_plain $ FOFPT_functor function $
                  map FOFT_variable variables]

              unitaryFormulaConstant = FOFUF_atomic $ FOFAT_plain $
                FOFPAF_predicate predicateResult
                [FOFT_function $ FOFFT_plain $ FOFPT_constant $ function]

              unitaryFormulaFunction = FOFUF_quantified $
                FOF_quantified_formula ForAll variables $
                FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                FOF_binary_nonassoc
                  TAS.Implication functionAntecedent functionConsequent

              formula =
                if null variables
                then unitaryFormulaConstant
                else unitaryFormulaFunction
              sentenceTptp = fofUnitaryFormulaToAxiom name formula
          in  makeNamed nameString sentenceTptp

sortOfX :: TAS.Variable -> SORT -> FOF_unitary_formula
sortOfX var s = FOFUF_atomic $ FOFAT_plain $
  FOFPAF_predicate (predicateOfSort s) [FOFT_variable var]

functionOfOp :: OP_NAME -> TAS.TPTP_functor
functionOfOp opName =
  let functionName = "op_" ++ toAlphaNum (show opName)
  in  mkSimpleId functionName

predicateOfPred :: PRED_NAME -> TAS.Predicate
predicateOfPred predName =
  let predicateName = "pred_" ++ toAlphaNum (show predName)
  in  mkSimpleId predicateName

predicateOfSort :: SORT -> TAS.Predicate
predicateOfSort s =
  let predicateName = "sort_" ++ toAlphaNum (show s)
  in  mkSimpleId predicateName

variableOfVar :: VAR -> TAS.Variable
variableOfVar var =
  let varName = "VAR_" ++ toAlphaNum (show var)
  in  mkSimpleId varName

toAlphaNum :: String -> String
toAlphaNum = concatMap toAlphaNumC
  where
    toAlphaNumC :: Char -> String
    toAlphaNumC c = case c of
      '+' -> "PLUS"
      '-' -> "MINUS"
      '/' -> "SLASH"
      '\\' -> "BACKSLASH"
      '%' -> "PERCENT"
      '<' -> "OPEN"
      '>' -> "CLOSE"
      '~' -> "TILDE"
      '=' -> "EQ"
      '*' -> "STAR"
      '\'' -> "PRIME"
      '\"' -> "QUOTE"
      ' ' -> "_"
      '_' -> "_"
      _ -> if isAlphaNum c then [c] else 'U' : showHex (ord c) ""
