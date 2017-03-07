{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/SuleCFOL2TPTP.hs
Description :  Coding of a CASL subset into TPTP
Copyright   :  (c) Eugen Kuksa and Till Mossakowksi
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  kuksa@iks.cs.ovgu.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from a CASL subset to TPTP.

Reflections on the theory of this comorphism:
- sorts are represented as predicates (TPTP is unsorted) => DONE
- we are in the Sule sublogic of CASL, hence each sort is subsort of
  one top-sorts (top-sort = maximum sort of its connected component) => DONE
- the top-sorts are represented as disjoint predicates => DONE
- subsorting is represented as predicate containment => DONE
- the model expansion property only holds up to isomorphism
  (which does not matter, because satisfaction is isomorphism invariant)
  Namely, for a CASL model, take an isomorphic model where the carriers
  of top-sorts are made disjoint => DONE
- a function f:s1 x ... x sn -> s is represented by a function f
  plus axiom forall x1,...,xn . s1(x1) /\ ... /\ sn(xn) => s(f(x1,...xn)) => DONE
- a predicate p:s1 x ... x sn is represented by a predicate p
  (no axiom needed) => DONE
- we must ensure that this is compatible with overloading.
  Therefore, if f:s1 x ... x sn -> s and f:t1 x ... x tn -> t and
  for all i=1..n, ui and si are in the same connected component, but
  f:s1 x ... x sn -> s and f:t1 x ... x tn -> t are not in the CASL overloading
  relation, they must be disambiguated with their type.
  Similarly for predicates.
  (As a first step, we could just raise an error in the case, since
  this will only occur in very seldom cases.)
- sentence translation is done by omitting types of function and predicate
  symbols and by relativising quantifiers with the predicate corresponding
  to the sort of the quantified variable
- model reduction translates a TPTP model to a CASL model with
  - carriers = extensions of corresponding predicates
  - functions = restrictions of functions to the appropriate carriers.
    The above axioms ensure that this gives a total function
  - predicates = restrictions of functions to the appropriate carriers.


Implementation notes:
- Only FORMULA is needed (CASL/AS_Basic_CASL.hs).
- Definedness is already removed by other comorphisms.
- Equation is already reduced to simple equality (=).
- Membership is simply a predicate.
- Mixfix is only used during parsing. It cannot occur.
- Unparsed_formula cannot occur.
- Sort_gen_ax can occur, but we can't translate it. Fail at this point.
- QuantOp cannot occur.
- QuantPred cannot occur.
- ExtFORMULA cannot occur.
-
- Sorted_term: Only use the TERM, ignore the SORT
- Cast cannot occur.
- Conditional: Replace the TERMs by the Formulas in which they occur
- Everything below cannot occur.

- Sign.hs (use the type CASLSign)
- SortRel: Retrieve the sorts, and their relations to each other.
- emptySortSet: For every sort that are not in this set, add an axiom that the sort is not empty.
- opMap: Add an axiom (sorts) for every OpType in the OpMap.
- predMap: Same thing, but only for the arguments
- The remainder is only a cache - Don't use it.
-}

module Comorphisms.SuleCFOL2TPTP
  ( suleCFOL2TPTP
  ) where

import Control.Exception (assert)
import Control.Monad (foldM)

import Logic.Logic as Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.DocUtils
import Common.ProofTree
import Common.Utils
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.List as List
import Data.Maybe
import Data.Char
import Data.Function

import CASL.Logic_CASL
import CASL.AS_Basic_CASL as CAS
import CASL.Cycle
import CASL.Sublogic as SL
import CASL.Sign as CSign
import CASL.MapSentence
import CASL.Morphism
import CASL.Quantification
import CASL.Overload
import CASL.Utils
import CASL.Inject
--import CASL.Induction (generateInductionLemmas)
import CASL.Simplify
import CASL.ToDoc

import TPTP.AS as TAS
import TPTP.Sign as TSign
import TPTP.Logic
import TPTP.Sublogic
import TPTP.Translate

data PlainTPTP = PlainTPTP

instance Show PlainTPTP where
  show PlainTPTP = "TPTP"

-- | The identity of the comorphisms
data GenSuleCFOL2TPTP a = GenSuleCFOL2TPTP a deriving Show

suleCFOL2TPTP :: GenSuleCFOL2TPTP PlainTPTP
suleCFOL2TPTP = GenSuleCFOL2TPTP PlainTPTP


-- | TPTP theories
type TPTPTheory = (TSign.Sign, [Named Sentence])

data CType = CSort
           | CVar SORT
           | CPred CSign.PredType
           | COp CSign.OpType
             deriving (Eq, Ord, Show)

toCKType :: CType -> CKType
toCKType ct = case ct of
  CSort -> CKSort
  CVar _ -> CKVar
  CPred _ -> CKPred
  COp _ -> CKOp

-- Identifiers in TPTP
type TPTPId = Token

-- | CASL Ids with Types mapped to SPIdentifier
type IdTypeSPIdMap = Map.Map Id (Map.Map CType TPTPId)

-- | specialized lookup for IdTypeSPIdMap
lookupSPId :: Id -> CType -> IdTypeSPIdMap ->
          Maybe TPTPId
lookupSPId i t = maybe Nothing (Map.lookup t) . Map.lookup i

-- | specialized insert (with error) for IdTypeSPIdMap
insertSPId :: Id -> CType ->
              TPTPId ->
              IdTypeSPIdMap ->
              IdTypeSPIdMap
insertSPId i t spid m =
    assert (checkIdentifier (toCKType t) $ show spid) $
    Map.insertWith (Map.unionWith err) i (Map.insert t spid Map.empty) m
    where err = error ("SuleCFOL2TPTP: for Id \"" ++ show i ++
                       "\" the type \"" ++ show t ++
                       "\" can't be mapped to different TPTP identifiers")

deleteSPId :: Id -> CType ->
              IdTypeSPIdMap ->
              IdTypeSPIdMap
deleteSPId i t m =
    maybe m (\ m2 -> let m2' = Map.delete t m2
                     in if Map.null m2'
                           then Map.delete i m
                           else Map.insert i m2' m) $
          Map.lookup i m

-- | specialized elems into a set for IdTypeSPIdMap
elemsSPIdSet :: IdTypeSPIdMap -> Set.Set TPTPId
elemsSPIdSet = Map.fold (\ m res -> Set.union res
                                      (Set.fromList (Map.elems m)))
                         Set.empty

-- extended signature translation
type SignTranslator f e = CSign.Sign f e -> e -> TPTPTheory -> TPTPTheory

-- extended signature translation for CASL
sigTrCASL :: SignTranslator () ()
sigTrCASL _ _ = id

-- extended formula translation
type FormulaTranslator f e =
    CSign.Sign f e -> IdTypeSPIdMap -> f -> Sentence

-- extended formula translation for CASL
formTrCASL :: FormulaTranslator () ()
formTrCASL _ _ = error "SuleCFOL2TPTP: No extended formulas allowed in CASL"

instance Show a => Language (GenSuleCFOL2TPTP a) where
  language_name (GenSuleCFOL2TPTP a) = "CASL2" ++ show a

instance Show a => Comorphism (GenSuleCFOL2TPTP a)
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign
               CASLMor
               CSign.Symbol RawSymbol ProofTree
               TPTP.Logic.TPTP Sublogic TAS.BASIC_SPEC Sentence () ()
               TSign.Sign TSign.Morphism TSign.Symbol () ProofTree where
    sourceLogic (GenSuleCFOL2TPTP _) = CASL
    sourceSublogic (GenSuleCFOL2TPTP a) = SL.cFol
                      { sub_features = LocFilSub
                      , cons_features = emptyMapConsFeature
                      , has_empty_sorts = show a == show PlainTPTP }
    targetLogic (GenSuleCFOL2TPTP _) = TPTP.Logic.TPTP
    mapSublogic cid sl = Just FOF
    map_theory (GenSuleCFOL2TPTP a) = transTheory sigTrCASL formTrCASL
    has_model_expansion (GenSuleCFOL2TPTP _) = True

transTheory :: (FormExtension f, Eq f) =>
               SignTranslator f e
            -> FormulaTranslator f e
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result TPTPTheory
transTheory trSig trForm (sign, sens) = do
  (tptpSign, signSentences) <- translateSign sign
  translatedSentences <- mapM translateNamedFormula sens
  return (tptpSign, signSentences ++ translatedSentences)

translateNamedFormula :: Named (FORMULA f) -> Result (Named TSign.Sentence)
translateNamedFormula x = do
  translated <- translateFormula $ sentence x
  return $ makeNamed (senAttr x) translated

translateFormula :: FORMULA f -> Result TSign.Sentence
translateFormula x = case x of
    Quantification q vars f range -> undefined
    Junction Con fs range -> undefined
    Junction Dis fs range -> undefined
    Relation f1 CAS.Implication f2 range -> undefined
    Relation f1 RevImpl f2 range -> undefined
    Relation f1 CAS.Equivalence f2 range -> undefined
    Negation f range -> undefined
    Atom True range -> undefined
    Atom False range -> undefined
    Predication p terms range -> undefined
    -- There is no Definedness in SuleCFOL
    Equation t1 Strong t2 range -> undefined
    -- There is no Equation t1 Existl t2 in SuleCFOL
    Membership t s range -> undefined
    -- There is no Mixfix_formula - it only occurs during parsing
    -- There is no Unparsed_formula
    -- Sort_gen_ax cannot be translated. Fail:
    Sort_gen_ax _ _ -> fail "Sort generation axioms are not yet supported."
    -- There is no QuantOp in SuleCFOL
    -- There is no QuantPred in SuleCFOL
    -- There is no ExtFORMULA in SuleCFOL
    _ -> fail "A formula that should not occur has occurred."

translateTerm :: TERM f -> Result TSign.Sentence
translateTerm x = case x of
  Qual_var var s range -> undefined
  Application op terms range -> undefined
  -- The sort can be ignored:
  Sorted_term t _ range -> undefined
  -- There is no Cast in SuleCFOL
  Conditional t_if condition t_else range -> undefined
  -- Everything else cannot occur
  _ -> fail "A term that should not occur has occurred."

translateSign :: (FormExtension f, Eq f)
              => CSign.Sign f e -> Result (TSign.Sign, [Named TSign.Sentence])
translateSign caslSign =
  return (tptpSign, sentencesOfSorts ++ sentencesOfOps ++ undefined)
  where
    tptpSign :: TSign.Sign
    tptpSign = undefined

    sentencesOfSorts :: [Named TSign.Sentence]
    sentencesOfSorts =
      let sortMap = Rel.toMap $ sortRel caslSign
          allSorts = Rel.nodes $ sortRel caslSign
          emptySorts = emptySortSet caslSign
          topSorts = Rel.mostRight $ sortRel caslSign
          subsortSentences =
            Map.foldWithKey (createSubsortSentences emptySorts) [] sortMap
          topSortSentences =
            Set.foldr (createTopSortSentences topSorts) [] topSorts
      in  subsortSentences ++ topSortSentences

    createSubsortSentences :: Set.Set SORT -> SORT -> Set.Set SORT
                         -> [Named TSign.Sentence] -> [Named TSign.Sentence]
    createSubsortSentences emptySorts sort subsorts sentences =
      let subsortSentences = Set.foldr
            (\ subsort sens -> createSubsortSentence sort subsort : sens)
            [] subsorts
          nonEmptySortsSentence =
            if Set.member sort emptySorts
            then []
            else [createNonEmptySortSentence sort]
          -- TODO do we need a sentence for the sort itself?
      in  subsortSentences ++ nonEmptySortsSentence ++ sentences

    -- creates:
    -- fof(sort_SUBSORT_subsort_of_SORT, axiom, ! [X]: (SUBSORT(X) => SORT(X))).
    createSubsortSentence :: SORT -> SORT -> Named TSign.Sentence
    createSubsortSentence sort subsort =
      let varX = mkSimpleId "X"
          nameString = "sign_" ++ show subsort ++ "_subsort_of_" ++ show sort
          name = NameString $ mkSimpleId nameString
          formula = FOFF_logic $ FOFLF_unitary $ FOFUF_quantified $
            FOF_quantified_formula ForAll [varX] $
            FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
            FOF_binary_nonassoc
              TAS.Implication (sortOfX varX subsort) (sortOfX varX sort)
          sentence = AF_FOF_Annotated $
            FOF_annotated name Axiom formula (Annotations Nothing)
      in  makeNamed nameString sentence

    -- creates:
    -- fof(sign_non_empty_sort_SORTNAME, axiom, ? [X]: (SORT(X))).
    createNonEmptySortSentence :: SORT -> Named TSign.Sentence
    createNonEmptySortSentence sort =
      let varX = mkSimpleId "X"
          nameString = "sign_non_empty_sort_" ++ show sort
          name = NameString $ mkSimpleId nameString
          formula = FOFF_logic $ FOFLF_unitary $ FOFUF_quantified $
            FOF_quantified_formula Exists [varX] $
            FOFUF_logic $ FOFLF_unitary $ sortOfX varX sort
          sentence = AF_FOF_Annotated $
            FOF_annotated name Axiom formula (Annotations Nothing)
      in  makeNamed nameString sentence

    createTopSortSentences :: Set.Set SORT -> SORT
                           -> [Named TSign.Sentence] -> [Named TSign.Sentence]
    createTopSortSentences topSorts sort sentences =
      createTopSortSentence (Set.delete sort topSorts) sort : sentences
      where
        -- creates:
        -- fof(sign_topsort_SORT, axiom,
        --   ! [X]: (SORT(X) => ~ OTHER_SORT1(X) & ... & ~ OTHER_SORTn(X)).
        createTopSortSentence :: Set.Set SORT -> SORT -> Named TSign.Sentence
        createTopSortSentence otherTopSorts sort =
          let varX = mkSimpleId "X"
              nameString = "sign_topsort_" ++ show sort
              name = NameString $ mkSimpleId nameString

              formula = FOFF_logic $ FOFLF_unitary $ FOFUF_quantified $
                FOF_quantified_formula ForAll [varX] $
                FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                FOF_binary_nonassoc
                  TAS.Implication
                  (sortOfX varX sort) $
                  FOFUF_logic $ FOFLF_binary $ FOFBF_assoc $ FOFBA_and $
                  Set.toList $
                  Set.map (negateUnitaryFormula . sortOfX varX) otherTopSorts

              sentence = AF_FOF_Annotated $
                FOF_annotated name Axiom formula (Annotations Nothing)
          in  makeNamed nameString sentence

    negateUnitaryFormula :: FOF_unitary_formula -> FOF_unitary_formula
    negateUnitaryFormula f = FOFUF_unary $ FOFUF_connective NOT f

    sentencesOfOps :: [Named TSign.Sentence]
    sentencesOfOps =
      -- TODO is assocOps already included in opMap or are these two disjunct?
      Map.foldrWithKey createSentencesOfOp [] $ MapSet.toMap $
        assocOps caslSign `MapSet.union` opMap caslSign
      where
        createSentencesOfOp :: OP_NAME -> Set.Set OpType
                            -> [Named TSign.Sentence] -> [Named TSign.Sentence]
        createSentencesOfOp opName opTypes sentences =
          -- Assign a new sentence name to each type of the op by adding a suffix
          let useNameSuffix = Set.size opTypes > 1
              (sentencesOfThisOp, _) = Set.foldr
                (\ opType (sens, i) ->
                  (createSentenceOfOp
                    (if useNameSuffix then "_" ++ show i else "")
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
          let nameString = "sign_op" ++ nameSuffix ++ "_" ++ show opName
              name = NameString $ mkSimpleId nameString

              predicateResult = predicateOfSort $ opRes opType
              predicates = map predicateOfSort $ opArgs opType
              variables = map (\ i -> mkSimpleId $ "X" ++ show i)
                            [1 .. length (opArgs opType)]
              -- TODO should different OpTypes yield differently named functions?
              function = functionOfOp opName

              functionAntecedent =
                FOFUF_logic $ FOFLF_binary $ FOFBF_assoc $ FOFBA_and $
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

              formula = FOFF_logic $ FOFLF_unitary $
                if null variables
                then unitaryFormulaConstant
                else unitaryFormulaFunction
              sentence = AF_FOF_Annotated $
                FOF_annotated name Axiom formula (Annotations Nothing)
          in  makeNamed nameString sentence


    sortOfX :: Variable -> SORT -> FOF_unitary_formula
    sortOfX var sort = FOFUF_atomic $ FOFAT_plain $
      FOFPAF_predicate (predicateOfSort sort) [FOFT_variable var]

functionOfOp :: OP_NAME -> TAS.Predicate
functionOfOp opName =
  let functionName = "function_" ++ show opName
  in  mkSimpleId functionName

predicateOfSort :: SORT -> TAS.Predicate
predicateOfSort sort =
  let predicateName = "sort_" ++ show sort
  in  mkSimpleId predicateName

{-
-- -------------------------- Signature -----------------------------

transFuncMap :: IdTypeSPIdMap ->
                CSign.Sign e f ->
                (TSign.FunctorSet, IdTypeSPIdMap, [Named Sentence])
transFuncMap idMap sign = Map.foldWithKey toSPOpType (Set.empty, idMap,[])
  . MapSet.toMap $ CSign.opMap sign
    where toSPOpType iden typeSet (fm, im) =
              foldr insOIdSet (fm, im)
                $ Rel.partSet (leqF sign) typeSet
              where insOIdSet tset (fm', im') =
                        let sid' = sid fm' (Set.findMax tset)
                        in (Map.insert sid' (Set.map transOpType tset) fm',
                            Set.fold (\ x -> insertSPId iden (COp x) sid')
                                     im' tset)
                    sid fma t = disSPOId CKOp (transId CKOp iden)
                                       (uType (transOpType t))
                                       (Set.union (Map.keysSet fma)
                                           (elemsSPIdSet idMap))
                    uType t = fst t ++ [snd t]


transPredMap :: IdTypeSPIdMap -> CSign.Sign e f
  -> (TSign.PredicateSet, IdTypeSPIdMap)
transPredMap idMap sign =
    Map.foldWithKey toSPPredType (Map.empty, idMap) . MapSet.toMap
      $ CSign.predMap sign
    where toSPPredType iden typeSet (fm, im) =
              if isSingleton typeSet then
                let pType = Set.findMin typeSet
                    sid' = sid fm pType
                in (Map.insert sid' (Set.singleton (transPredType pType)) fm
                   , insertSPId iden (CPred pType) sid' im)
              else case -- genPredImplicationDisjunctions sign $
                        Rel.partSet (leqP sign) typeSet of
                     splitTySet -> foldr insOIdSet (fm, im) splitTySet
              where insOIdSet tset (fm', im') =
                        let sid' = sid fm' (Set.findMax tset)
                        in (Map.insert sid' (Set.map transPredType tset) fm',
                            Set.fold (\ x -> insertSPId iden (CPred x) sid')
                                     im' tset)
                    sid fma t = disSPOId CKPred (transId CKPred iden)
                                       (transPredType t)
                                       (Set.union (Map.keysSet fma)
                                           (elemsSPIdSet idMap))



transOpType :: CSign.OpType -> ([TPTPId], TPTPId)
transOpType ot = (map transIdSort (CSign.opArgs ot),
                  transIdSort (CSign.opRes ot))

transPredType :: CSign.PredType -> [TPTPId]
transPredType = map transIdSort . CSign.predArgs

-- | translate every Id as Sort
transIdSort :: Id -> TPTPId
transIdSort = transId CKSort

integrateGenerated :: IdTypeSPIdMap -> [Named (FORMULA f)] ->
                      TSign.Sign ->
                      Result (IdTypeSPIdMap, TSign.Sign, [Named Sentence])
integrateGenerated idMap genSens sign
    | null genSens = return (idMap, sign, [])
    | otherwise =
      case partition isAxiom genSens of
      (genAxs, genGoals) ->
        case makeGenGoals sign idMap genGoals of
        (newPredsMap, idMap', goalsAndSentences) ->
          -- makeGens must not invent new sorts
          case makeGens sign idMap' genAxs of
          Result dias mv ->
            maybe (Result dias Nothing)
                  (\ (spSortMap_makeGens, newOpsMap, idMap'', exhaustSens) ->
                      let spSortMap' =
                            Map.union spSortMap_makeGens (TSign.sortMap sign)
                      in assert (Map.size spSortMap' ==
                                    Map.size (TSign.sortMap sign))
                             (Result dias
                                     (Just (idMap'',
                                            sign { sortMap = spSortMap'
                                                 , funcMap =
                                                     Map.union (funcMap sign)
                                                               newOpsMap
                                                 , TSign.predMap =
                                                     Map.union
                                                     (TSign.predMap sign)
                                                               newPredsMap},
                                            mkInjSentences idMap' newOpsMap ++
                                            goalsAndSentences ++
                                            exhaustSens))))
                  mv

makeGenGoals :: TSign.Sign -> IdTypeSPIdMap -> [Named (FORMULA f)]
             -> (TSign.PredMap, IdTypeSPIdMap, [Named Sentence])
makeGenGoals sign idMap fs =
  let Result _ res = makeGens sign idMap fs
  in case res of
   Nothing -> (Map.empty, idMap, [])
   Just (_, _, idMap', fs') ->
     let fs'' = map (\ s -> s {isAxiom = False}) fs'
     in (Map.empty, idMap', fs'')
 {- Sort_gen_ax as goals only implemented through a hack."
sketch of full implementation :
   - invent new predicate P that is supposed to hold on
     every x in the (freely) generated sort.
   - generate formulas with this predicate for each constructor.
   - recursive constructors hold if the predicate holds on the variables
   - prove forall x . P(x)

  implementation is postponed as this translation does not produce
only one goal, but additional symbols, axioms and a goal
 -}

makeGens :: TSign.Sign -> IdTypeSPIdMap -> [Named (FORMULA f)]
         -> Result (SortMap, FuncMap, IdTypeSPIdMap, [Named Sentence])
            {- ^ The list of TPTP sentences gives exhaustiveness for
            generated sorts with only constant constructors
            and\/or subsort injections, by simply translating
            such sort generation constraints to disjunctions -}
makeGens sign idMap fs =
    case foldl (makeGen sign) (return (Map.empty, idMap, [], [])) fs of
    Result ds mv ->
        maybe (Result ds Nothing)
              (\ (opM, idMap', pairs, exhaustSens) ->
                   Result ds
                      (Just (foldr (uncurry Map.insert)
                                   Map.empty pairs,
                             opM, idMap', exhaustSens)))
              mv

makeGen :: TSign.Sign
        -> Result (FuncMap, IdTypeSPIdMap,
                   [(TPTPId, Maybe Generated)], [Named Sentence])
        -> Named (FORMULA f)
        -> Result (FuncMap, IdTypeSPIdMap,
                   [(TPTPId, Maybe Generated)], [Named Sentence])
makeGen sign r@(Result ods omv) nf =
    maybe (Result ods Nothing) process omv where
 process (oMap, iMap, rList, eSens) = case sentence nf of
  Sort_gen_ax constrs free ->
      if null mp then (case mapAccumL makeGenP (oMap, iMap, []) srts of
                       ((oMap', iMap', eSens'), genPairs) ->
                          Result ods (Just (oMap', iMap',
                                            rList ++ genPairs,
                                            eSens ++ eSens')))
                 else mkError ("Sort generation constraints with " ++
                               "non-injective sort mappings cannot " ++
                               "be translated to TPTP") mp
      where -- compute standard form of sort generation constraints
            (srts, ops, mp) = recover_Sort_gen_ax constrs
            -- test whether a constructor belongs to a specific sort
            hasTheSort s (Qual_op_name _ ot _) = s == res_OP_TYPE ot
            hasTheSort _ _ = error "SuleCFOL2TPTP.hasTheSort"
            mkGen = Just . Generated free . map fst
            -- translate constraint for one sort
            makeGenP (opM, idMap, exSens) s = ((newOpMap, newIdMap,
                                                exSens ++ eSen ops_of_s s),
                                        (s', mkGen cons))
                where ((newOpMap, newIdMap), cons) =
                          mapAccumL mkInjOp (opM, idMap) ops_of_s
                      ops_of_s = List.filter (hasTheSort s) ops
                      s' = fromMaybe (error $ "SuleCFOL2TPTP.makeGen: "
                                        ++ "No mapping found for '"
                                        ++ shows s "'")
                                 (lookupSPId s CSort idMap)
            {- is an operation a constant or an injection ?
            (we currently can translate only these) -}
            isConstorInj o =
              nullArgs o || isInjName (opSymbName o)
            -- generate sentences for one sort
            eSen os s = [ makeNamed (newName s) (SPQuantTerm SPForall
                            [typedVarTerm var1
                             $ fromMaybe (error "lookup failed")
                             (lookupSPId s CSort iMap)] (disj var1 os))
                        | all isConstorInj os ]
            -- generate sentences: compute one disjunct (for one alternative)
            mkDisjunct v o@(Qual_op_name _ (Op_type _ args res _) _) =
              -- a constant? then just compare with it
              case args of
                [] -> mkEq (varTerm v) $ varTerm $ transOPSYMB iMap o
                {- an injection? then quantify existentially
                (for the injection's argument)
                since injections are identities, we can leave them out -}
                [arg] -> let ta = transIdSort arg in SPQuantTerm SPExists
                  [ typedVarTerm var2 ta ]
                   $ mkEq (varTerm v)
                   $ if Rel.member ta (transIdSort res)
                        $ TSign.sortRel sign
                     then varTerm var2
                     else compTerm (spSym $ transOPSYMB iMap o) [varTerm var2]
                _ -> error "cannot handle ordinary constructors"
            mkDisjunct _ _ = error "unqualified operation symbol"
            -- make disjunction out of all the alternatives
            disj v os = case map (mkDisjunct v) os of
                        [] -> error "SuleCFOL2TPTP: no constructors found"
                        [x] -> x
                        xs -> foldl1 mkDisj xs
            -- generate enough variables
            var = fromJust (find (\ x ->
                      not (Set.member (mkSimpleId x) usedIds))
                            ("X" : ['X' : show i | i <- [(1 :: Int) ..]]))
            var1 = mkSimpleId var
            var2 = mkSimpleId $ var ++ "a"
            varTerm = simpTerm . spSym
            newName s = "ga_exhaustive_generated_sort_" ++ show (pretty s)
            usedIds = elemsSPIdSet iMap
            nullArgs o = case o of
                         Qual_op_name _ (Op_type _ args _ _) _ -> null args
                         _ -> error "SuleCFOL2TPTP: wrong constructor"
  _ -> r

mkInjOp :: (FuncMap, IdTypeSPIdMap)
        -> OP_SYMB
        -> ((FuncMap, IdTypeSPIdMap),
            (TPTPId, ([TPTPId], TPTPId)))
mkInjOp (opM, idMap) qo@(Qual_op_name i ot _) =
    if isInjName i && isNothing lsid
       then ((Map.insert i' (Set.singleton (transOpType ot')) opM,
              insertSPId i (COp ot') i' idMap),
             (i', transOpType ot'))
       else ((opM, idMap),
             (fromMaybe err lsid,
              transOpType ot'))
    where i' = disSPOId CKOp (transId CKOp i)
                        (utype (transOpType ot')) usedNames
          ot' = CSign.toOpType ot
          lsid = lookupSPId i (COp ot') idMap
          usedNames = Map.keysSet opM
          err = error ("SuleCFOL2TPTP.mkInjOp: Cannot find SPId for '"
                       ++ show qo ++ "'")
          utype t = fst t ++ [snd t]
mkInjOp _ _ = error "SuleCFOL2TPTP.mkInjOp: Wrong constructor!!"

mkInjSentences :: IdTypeSPIdMap
               -> FuncMap
               -> [Named Sentence]
mkInjSentences idMap = Map.foldWithKey genInjs []
    where genInjs k tset fs = Set.fold (genInj k) fs tset
          genInj k (args, res) =
              assert (length args == 1)
                     . (makeNamed (newName (show k) (show $ head args)
                                 $ show res)
                       (SPQuantTerm SPForall
                              [typedVarTerm var $ head args]
                             (compTerm SPEqual
                                       [compTerm (spSym k)
                                                 [simpTerm (spSym var)],
                                        simpTerm (spSym var)])) :)
          var = mkSimpleId $
            fromJust (find (\ x -> not (Set.member (mkSimpleId x) usedIds))
                          ("Y" : [ 'Y' : show i | i <- [(1 :: Int) ..]]))
          newName o a r = "ga_" ++ o ++ '_' : a ++ '_' : r ++ "_id"
          usedIds = elemsSPIdSet idMap

{- |
  Translate a CASL signature into TPTP signature 'TPTP.Sign.Sign'.
  Before translating, eqPredicate symbols where removed from signature.
-}
transSign :: CSign.Sign f e -> (TSign.Sign, IdTypeSPIdMap)
transSign sign = (TSign.emptySign { TSign.sortRel =
                                 Rel.map transIdSort (CSign.sortRel sign)
                           , sortMap = spSortMap
                           , funcMap = fMap
                           , TSign.predMap = pMap
                           , singleSorted = isSingleSorted sign
                           }
                 , idMap'')
    where (spSortMap, idMap) =
            Set.fold (\ i (sm, im) ->
                          let sid = disSPOId CKSort (transIdSort i)
                                       [mkSimpleId $ take 20 (cycle "So")]
                                       (Map.keysSet sm)
                          in (Map.insert sid Nothing sm,
                              insertSPId i CSort sid im))
                                        (Map.empty, Map.empty)
                                        (CSign.sortSet sign)
          (fMap, idMap') = transFuncMap idMap sign
          (pMap, idMap'') = transPredMap idMap' sign

nonEmptySortSens :: CSign.Sign f e -> IdTypeSPIdMap -> SortMap -> [Named Sentence]
nonEmptySortSens sig idMap sm =
  let es = Set.difference (sortSet sig) $ emptySortSet sig
  in [ extSen s | nes <- Set.toList es
     , let s = fromMaybe (transIdSort nes) $ lookupSPId nes CSort idMap
     , Set.member s $ Map.keysSet sm ]
    where extSen s = makeNamed ("ga_non_empty_sort_" ++ show s) $ SPQuantTerm
                     SPExists [varTerm] $ compTerm (spSym s) [varTerm]
              where varTerm = simpTerm $ spSym $ mkSimpleId $ newVar s
          newVar s = fromJust $ find (/= show s)
                          $ "Y" : ['Y' : show i | i <- [(1 :: Int) ..]]

disjointTopSorts :: CSign.Sign f e -> IdTypeSPIdMap -> [Named Sentence]
disjointTopSorts sign idMap = let
    s = CSign.sortSet sign
    sl = Rel.partSet (haveCommonSupersorts True sign) s
    l = map (\ p -> case keepMinimals1 False sign id $ Set.toList p of
                       [e] -> e
                       _ -> error "disjointTopSorts") sl
    pairs ls = case ls of
      s1 : r -> map (\ s2 -> (s1, s2)) r ++ pairs r
      _ -> []
    v1 = simpTerm $ spSym $ mkSimpleId "Y1"
    v2 = simpTerm $ spSym $ mkSimpleId "Y2"
    in map (\ (t1, t2) ->
         makeNamed ("disjoint_sorts_" ++ shows t1 "_" ++ show t2) $
           SPQuantTerm SPForall
               [ compTerm (spSym t1) [v1]
               , compTerm (spSym t2) [v2]]
              $ compTerm SPNot [mkEq v1 v2]) $ pairs $
                map (\ t -> fromMaybe (transIdSort t)
                     $ lookupSPId t CSort idMap) l

transTheory :: (FormExtension f, Eq f) =>
               SignTranslator f e
            -> FormulaTranslator f e
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result TPTPTheory
transTheory trSig trForm (sign, sens) =
  let (nsig, sm) = removeSortCycles sign
  in transTheoryAux trSig trForm (nsig
     , map (mapNamed $ mapMorphForm (return id)
                 ((embedMorphism () sign nsig) { sort_map = sm })) sens)

transTheoryAux :: (FormExtension f, Eq f) =>
               SignTranslator f e
            -> FormulaTranslator f e
            -> (CSign.Sign f e, [Named (FORMULA f)])
            -> Result TPTPTheory
transTheoryAux trSig trForm (sign, sens) =
  fmap (trSig sign (CSign.extendedInfo sign))
    (case transSign (filterPreds $ foldl insInjOps sign genAxs) of
     (tSign, idMap) ->
        do (idMap', tSign', sentencesAndGoals) <-
               integrateGenerated idMap genSens tSign
           let tSignElim = if TSign.singleSortNotGen tSign'
                             then tSign' {sortMap = Map.empty} else tSign'
           return (tSignElim,
                    disjointTopSorts sign idMap' ++
                    sentencesAndGoals ++
                    nonEmptySortSens sign idMap' (sortMap tSignElim) ++
                    map (mapNamed (transFORM (singleSortNotGen tSign') eqPreds
                                     sign idMap' trForm))
                        realSens'))

  where (genSens, realSens) =
            partition (\ s -> case sentence s of
                              Sort_gen_ax _ _ -> True
                              _ -> False) sens
        (eqPreds, realSens') = foldl findEqPredicates (Set.empty, []) realSens
        genAxs = filter isAxiom genSens
        insInjOps sig s =
              case sentence s of
              (Sort_gen_ax constrs _) ->
                 case recover_Sort_gen_ax constrs of
                 (_, ops, mp) -> assert (null mp) (insertInjOps sig ops)
              _ -> error "SuleCFOL2TPTP.transTheory.insInjOps"
        filterPreds sig =
              sig { CSign.predMap = MapSet.difference
                (CSign.predMap sig)
                (Set.fold (\ pl -> case pl of
                      Pred_name pn -> MapSet.insert pn (PredType [])
                      Qual_pred_name pn pt _ ->
                        MapSet.insert pn $ CSign.toPredType pt)
                    MapSet.empty eqPreds) }

{- |
 Finds definitions (Equivalences) where one side is a binary predicate
 and the other side is a built-in equality application (Strong_equation).
 The given Named (FORMULA f) is checked for this and if so, will be put
 into the set of such predicates.
-}
findEqPredicates :: (Eq f) => (Set.Set PRED_SYMB, [Named (FORMULA f)])
                    -- ^ previous list of found predicates and valid sentences
                 -> Named (FORMULA f)
                    -- ^ sentence to check
                 -> (Set.Set PRED_SYMB, [Named (FORMULA f)])
findEqPredicates (eqPreds, sens) sen =
    case sentence sen of
      Quantification Universal var_decl quantFormula _ ->
        isEquiv (foldl (\ vList (Var_decl v s _) ->
                          vList ++ map (\ vl -> (vl, s)) v)
                       [] var_decl)
                quantFormula
      _ -> validSens

  where
    validSens = (eqPreds, sens ++ [sen])
    isEquiv vars qf =
      {- Exact two variables are checked if they have the same Sort.
      If more than two variables should be compared, use foldl. -}
      if (length vars == 2) && (snd (head vars) == snd (vars !! 1))
       then case qf of
          Relation f1 Equivalence f2 _ -> isStrong_eq vars f1 f2
          _ -> validSens
        else validSens
    isStrong_eq vars f1 f2 =
      let f1n = case f1 of
                  Equation _ Strong _ _ -> f1
                  _ -> f2
          f2n = case f1 of
                  Equation _ Strong _ _ -> f2
                  _ -> f1
      in case f1n of
            Equation eq_t1 Strong eq_t2 _ -> case f2n of
              Predication eq_pred_symb pterms _ ->
                if Map.toList (Map.fromList $ sortedVarTermList pterms)
                     == Map.toList (Map.fromList vars)
                 && Map.toList
                         (Map.fromList $ sortedVarTermList [eq_t1, eq_t2])
                     == Map.toList (Map.fromList vars)
                  then (Set.insert eq_pred_symb eqPreds, sens)
                  else validSens
              _ -> validSens
            _ -> validSens

{- |
  Creates a list of (VAR, SORT) out of a list of TERMs. Only Qual_var TERMs
  are inserted which will be checked using
  'Comorphisms.SuleCFOL2TPTP.hasSortedVarTerm'.
-}
sortedVarTermList :: [TERM f] -> [(VAR, SORT)]
sortedVarTermList = mapMaybe hasSortedVarTerm

{- |
  Finds a 'CASL.AS_Basic_CASL.Qual_var' term recursively if super term(s) is
  'CASL.AS_Basic_CASL.Sorted_term' or 'CASL.AS_Basic_CASL.Cast'.
-}
hasSortedVarTerm :: TERM f -> Maybe (VAR, SORT)
hasSortedVarTerm t = case t of
    Qual_var v s _ -> Just (v, s)
    Sorted_term tx _ _ -> hasSortedVarTerm tx
    Cast tx _ _ -> hasSortedVarTerm tx
    _ -> Nothing


-- ---------------------------- Formulas ------------------------------

transOPSYMB :: IdTypeSPIdMap -> OP_SYMB -> TPTPId
transOPSYMB idMap ~qo@(Qual_op_name op ot _) =
    fromMaybe (error $ "SuleCFOL2TPTP.transOPSYMB: unknown op: " ++ show qo)
        (lookupSPId op (COp (CSign.toOpType ot)) idMap)

transPREDSYMB :: IdTypeSPIdMap -> PRED_SYMB -> TPTPId
transPREDSYMB idMap ~qp@(Qual_pred_name p pt _) = fromMaybe
    (error $ "SuleCFOL2TPTP.transPREDSYMB: unknown pred: " ++ show qp)
          (lookupSPId p (CPred (CSign.toPredType pt)) idMap)

-- | Translate the quantifier
quantify :: QUANTIFIER -> SPQuantSym
quantify q = case q of
    Universal -> SPForall
    Existential -> SPExists
    Unique_existential ->
      error "SuleCFOL2TPTP: no translation for existential quantification."

transVarTup :: (Set.Set TPTPId, IdTypeSPIdMap) ->
               (VAR, SORT) ->
               ((Set.Set TPTPId, IdTypeSPIdMap),
                (TPTPId, TPTPId))
                {- ^ ((new set of used Ids, new map of Ids to original Ids),
                (var as sp_Id, sort as sp_Id)) -}
transVarTup (usedIds, idMap) (v, s) =
    ((Set.insert sid usedIds,
      insertSPId vi (CVar s) sid $ deleteSPId vi (CVar s) idMap)
    , (sid, spSort))
    where spSort = fromMaybe
            (error $ "SuleCFOL2TPTP: translation of sort \"" ++
             showDoc s "\" not found")
            (lookupSPId s CSort idMap)
          vi = simpleIdToId v
          sid = disSPOId CKVar (transId CKVar vi)
                    [mkSimpleId $ "_Va_" ++ showDoc s "_Va"]
                    usedIds

transFORM :: (Eq f, FormExtension f) => Bool -- ^ single sorted flag
          -> Set.Set PRED_SYMB -- ^ list of predicates to substitute
          -> CSign.Sign f e
          -> IdTypeSPIdMap -> FormulaTranslator f e
          -> FORMULA f -> Sentence
transFORM siSo eqPreds sign i tr phi = transFORMULA siSo sign i tr phi'
    where phi' = codeOutConditionalF id
                     (codeOutUniqueExtF id id
                          (substEqPreds eqPreds id phi))


transFORMULA :: FormExtension f => Bool -> CSign.Sign f e -> IdTypeSPIdMap
             -> FormulaTranslator f e -> FORMULA f -> Sentence
transFORMULA siSo sign idMap tr frm = case frm of
  Quantification qu vdecl phi _ ->
    SPQuantTerm (quantify qu)
                    vList
                    (transFORMULA siSo sign idMap' tr phi)
    where ((_, idMap'), vList) =
              mapAccumL (\ acc e ->
                  let (acc', e') = transVarTup acc e
                  in (acc', (if siSo then simpTerm . spSym . fst
                                     else uncurry typedVarTerm)
                            e'))
                        (sidSet, idMap) (flatVAR_DECLs vdecl)
          sidSet = elemsSPIdSet idMap
  Junction j phis _ -> let
    (n, op) = if j == Dis then (SPFalse, mkDisj) else (SPTrue, mkConj)
    in if null phis then simpTerm n else
    foldl1 op (map (transFORMULA siSo sign idMap tr) phis)
  Relation phi1 c phi2 _ -> compTerm
    (if c == Equivalence then SPEquiv else SPImplies)
    [transFORMULA siSo sign idMap tr phi1, transFORMULA siSo sign idMap tr phi2]
  Negation phi _ -> compTerm SPNot [transFORMULA siSo sign idMap tr phi]
  Atom b _ -> simpTerm $ if b then SPTrue else SPFalse
  Predication psymb args _ -> compTerm (spSym (transPREDSYMB idMap psymb))
           (map (transTERM siSo sign idMap tr) args)
  Equation t1 _ t2 _ -> -- sortOfTerm t1 == sortOfTerm t2
       mkEq (transTERM siSo sign idMap tr t1) (transTERM siSo sign idMap tr t2)
  ExtFORMULA phi -> tr sign idMap phi
  Definedness _ _ -> simpTerm SPTrue -- assume totality
  Membership t s _ -> if siSo then simpTerm SPTrue else
    maybe (error ("SuleCFOL2TPTP.tF: no TPTP Id found for \"" ++
                  showDoc s "\""))
          (\ si -> compTerm (spSym si) [transTERM siSo sign idMap tr t])
          (lookupSPId s CSort idMap)
  _ -> error
    $ "SuleCFOL2TPTP.transFORMULA: unknown FORMULA '" ++ showDoc frm "'"

transTERM :: FormExtension f => Bool -> CSign.Sign f e -> IdTypeSPIdMap
          -> FormulaTranslator f e -> TERM f -> Sentence
transTERM siSo sign idMap tr term = case term of
  Qual_var v s _ -> maybe
    (error
         ("SuleCFOL2TPTP.tT: no TPTP Id found for \"" ++ showDoc v "\""))
        (simpTerm . spSym) (lookupSPId (simpleIdToId v) (CVar s) idMap)
  Application opsymb args _ ->
    compTerm (spSym (transOPSYMB idMap opsymb))
             (map (transTERM siSo sign idMap tr) args)
  Conditional _t1 _phi _t2 _ ->
    error "SuleCFOL2TPTP.transTERM: Conditional terms must be coded out."
  Sorted_term t _s _ -> -- sortOfTerm t isSubsortOf s
    transTERM siSo sign idMap tr t
  Cast t _s _ -> -- s isSubsortOf sortOfTerm t
    transTERM siSo sign idMap tr t
  _ -> error ("SuleCFOL2TPTP.transTERM: unknown TERM '" ++ showDoc term "'")

isSingleSorted :: CSign.Sign f e -> Bool
isSingleSorted sign =
  Set.size (CSign.sortSet sign) == 1
  && Set.null (emptySortSet sign) -- empty sorts need relativization


-}
