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
  of top-sorts are made disjoint => TODO (axiom for disjoint top sorts is DONE)
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
  this will only occur in very seldom cases.) => DONE with renaming
- sentence translation is done by omitting types of function and predicate
  symbols and by relativising quantifiers with the predicate corresponding
  to the sort of the quantified variable => DONE
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
import Control.Monad (liftM)

import qualified Data.Map as Map
import qualified Data.Set as Set

import Data.List as List
import Data.Maybe
import Data.Char
import Data.Function
import Numeric (showHex)

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

data TPTP_FOF = TPTP_FOF

instance Show TPTP_FOF where
  show TPTP_FOF = "TPTP_FOF"

-- | The identity of the comorphisms
data GenSuleCFOL2TPTP a = GenSuleCFOL2TPTP a deriving Show

suleCFOL2TPTP :: GenSuleCFOL2TPTP TPTP_FOF
suleCFOL2TPTP = GenSuleCFOL2TPTP TPTP_FOF

-- | TPTP theories
type TPTPTheory = (TSign.Sign, [Named Sentence])

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
                      , has_empty_sorts = show a == show TPTP_FOF }
    targetLogic (GenSuleCFOL2TPTP _) = TPTP.Logic.TPTP
    mapSublogic cid sl = Just FOF
    map_theory (GenSuleCFOL2TPTP a) = transTheory
    has_model_expansion (GenSuleCFOL2TPTP _) = True

transTheory :: (FormExtension f, Eq f)
            => (CSign.Sign f e, [Named (FORMULA f)])
            -> Result TPTPTheory
transTheory (sign, sens) = do
  let signWithRenamings@(preparedSign, _, _) = prepareSign sign
  let preparedSens = concatMap prepareNamedFormula sens
  (tptpSign, signSentences) <- translateSign preparedSign
  translatedSentences <- mapM (translateNamedFormula signWithRenamings) preparedSens
  return (tptpSign, signSentences ++ translatedSentences)

prepareNamedFormula :: (FormExtension f, Eq f)
                    => Named (FORMULA f) -> [Named (FORMULA f)]
prepareNamedFormula formula =
  let resolvedFormulae =
        resolveConditionals $
        resolveUniqueExistentialQuantifier $
        sentence formula
      nameS = senAttr formula
  in  case resolvedFormulae of
        [_] -> map (\ f -> makeNamed nameS f) resolvedFormulae
        _ -> map (\ (f, i) ->
                   makeNamed (nameS ++ "_resolved_conditional_" ++ show i) f
                 ) $ zip resolvedFormulae [1..]
  where
    -- Resolves/removes Conditional terms recursively. For instance, from
    -- P(T11 when C1 else T12, T21 when C2 else T22)
    -- it creates this list of formulae:
    -- C1 & C2 => P(T11, T21)
    -- C1 & ~C2 => P(T11, T22)
    -- ~C1 & C2 => P(T12, T21)
    -- ~C1 & ~C2 => P(T12, T22)
    --
    -- If C1 itself contain conditionals, then the resolved formula list of C1
    -- is joined to one formula by conjunction.
    resolveConditionals :: (FormExtension f, Eq f) => FORMULA f -> [FORMULA f]
    resolveConditionals x = case x of
      Quantification q vars f r ->
        map (\ f' -> Quantification q vars f' r) $ resolveConditionals f
      Junction j fs r ->
        map (\ fs' -> Junction j fs' r) $
        List.transpose $ map resolveConditionals fs
      Relation f1 rel f2 r ->
        let resolvedFormulae1 = resolveConditionals f1
            resolvedFormulae2 = resolveConditionals f2
        in  map (\ (f1', f2') -> Relation f1' rel f2' r)
              [(x,y) | x <- resolvedFormulae1, y <- resolvedFormulae2]
      Negation f r -> map (\ f' -> Negation f' r) $ resolveConditionals f
      Predication p ts r -> resolveTerms ts (\ ts' -> Predication p ts' r)
      Definedness t r -> resolveTerms [t] (\ [t'] -> Definedness t' r)
      Equation t1 e t2 r ->
        resolveTerms [t1, t2] (\ [t1', t2'] -> Equation t1' e t2' r)
      Membership t sort r -> resolveTerms [t] (\ [t'] -> Membership t' sort r)
      -- the others cannot occur in SuleCFOL
      _ -> [x]

      where
        resolveTerms :: (FormExtension f, Eq f)
                     => [TERM f] -> ([TERM f] -> FORMULA f) -> [FORMULA f]
        resolveTerms ts toFormula =
          map resolveTermsForConditionalValue boolPermutations
          where
            boolPermutations :: [[Bool]]
            boolPermutations = getBoolPermutations $ Map.size conditionalTermMap

            -- GHC complains about the type variable f, and needs to infer the
            -- type itself in these functions:

            -- termMap :: (FormExtension f, Eq f) => Map.Map Int (TERM f)
            termMap = Map.fromList $ zip [0..] ts

            -- conditionalTermMap :: (FormExtension f, Eq f)
            --                    => Map.Map Int (TERM f)
            conditionalTermMap = findConditionals ts

            -- This overwrites the termMap with entries from conditionalTermMap.
            -- completeTermMap :: (FormExtension f, Eq f)
            --                 => Map.Map Int (TERM f)
            completeTermMap = conditionalTermMap `Map.union` termMap

            -- combinations :: (FormExtension f, Eq f)
            --              => Map.Map (Bool, Int) (FORMULA f, TERM f)
            combinations = conditionalCombinations conditionalTermMap

            -- resolveTermsForConditionalValue :: (FormExtension f, Eq f)
            --                                 => [Bool] -> FORMULA f
            resolveTermsForConditionalValue permutation =
              let permutationWithIndexes =
                   zip permutation $
                   Set.toAscList $ Map.keysSet conditionalTermMap
                  currentCombinations =
                    Map.filterWithKey
                      (\ key _ -> key `elem` permutationWithIndexes)
                      combinations
                  currentConditions =
                    Map.foldrWithKey
                      (\ (_, i) (c, _) acc -> Map.insert i c acc)
                      Map.empty
                      currentCombinations
                  currentTerms =
                    Map.foldrWithKey
                      (\ (_, i) (_, t) acc -> Map.insert i t acc)
                      Map.empty
                      currentCombinations
                  condition = conjunction $ Map.elems currentConditions
                  replacedTerms =
                    map snd $ Map.toAscList $ currentTerms `Map.union` termMap
              in  if Map.null combinations
                  then toFormula ts
                  else implication condition $ toFormula replacedTerms

    -- Transforms the conditionalMap:
    -- The numbers in the indexes stay the same, but the keys are added a Bool
    -- where True maps to the positive conditional formula and the term that is
    -- supposed to be used in that case. False maps to the negated conditional
    -- formula and the term that is supposed to be used in case this negation
    -- holds.
    conditionalCombinations :: (FormExtension f, Eq f)
                            => Map.Map Int (TERM f)
                            -> Map.Map (Bool, Int) (FORMULA f, TERM f)
    conditionalCombinations conditionalTermMap =
      -- The inner list and concat is needed for the list comprehension to work.
      Map.fromList $ concat [ [ ((True, i), (condition t, thenTerm t))
                              , ((False, i), (negCondition t, elseTerm t))
                              ]
                            | (i, t) <- Map.toList $ conditionalTermMap
                            ]
      where
        errorMessage = "Non-Condition found where only Condition can occur. " ++
                       "This is a Bug in Hets."
        condition :: (FormExtension f, Eq f) => TERM f -> FORMULA f
        condition x = case x of
          Conditional _ c _ _ ->
            case resolveConditionals c of
              [singleResolved] -> singleResolved
              manyResolved -> conjunction manyResolved
          _ -> error errorMessage

        negCondition :: (FormExtension f, Eq f) => TERM f -> FORMULA f
        negCondition x = Negation (condition x) nullRange

        thenTerm :: (FormExtension f, Eq f) => TERM f -> TERM f
        thenTerm x = case x of
          Conditional t _ _ _ -> t
          _ -> error errorMessage

        elseTerm :: (FormExtension f, Eq f) => TERM f -> TERM f
        elseTerm x = case x of
          Conditional _ _ t _ -> t
          _ -> error errorMessage

    conjunction :: (FormExtension f, Eq f) => [FORMULA f] -> FORMULA f
    conjunction fs = Junction Con fs nullRange

    implication :: (FormExtension f, Eq f) => FORMULA f -> FORMULA f -> FORMULA f
    implication antecedent consequent =
      Relation antecedent CAS.Implication consequent nullRange

    -- Filters TERMs with the Conditional constructor and indexes them
    -- starting at 0. Indexing happens before filtering, so the indexes may
    -- "contain holes".
    findConditionals :: (FormExtension f, Eq f)
                     => [TERM f] -> Map.Map Int (TERM f)
    findConditionals ts =
      Map.fromList $ filter (isConditional . snd) $ zip [0..] ts
      where
        isConditional :: (FormExtension f, Eq f) => TERM f -> Bool
        isConditional x = case x of
          Conditional _ _ _ _ -> True
          _ -> False

    getBoolPermutations :: Int -> [[Bool]]
    getBoolPermutations k = permute $ replicate k [True,False]
      where
        permute :: [[a]] -> [[a]]
        permute [] = [[]]
        permute [x] = map (\y -> [y]) x
        permute (x:l) =
          concat (map (distribute (permute l)) x)
          where
          distribute perms y = map ((:) y) perms
    resolveUniqueExistentialQuantifier :: (FormExtension f, Eq f)
                                       => FORMULA f -> FORMULA f
    resolveUniqueExistentialQuantifier =
      resolveUniqueExistentialQuantifier' Set.empty
      where
        -- creates:
        -- exists (x1: s1, ... xn: sn) .
        --   (f(x1, ..., xn) & forall (y1: s1, ..., yn: sn) .
        --     f(y1, ..., yn) => x1 = y1 & ... & xn = yn)
        resolveUniqueExistentialQuantifier' :: (FormExtension f, Eq f)
                                            => Set.Set VAR
                                            -> FORMULA f
                                            -> FORMULA f
        resolveUniqueExistentialQuantifier' usedVars x = case x of
          Quantification Unique_existential varDecls f r ->
            let usedVars' = Set.unions $ collectVars usedVars f :
                  map (collectVarsDecl usedVars) varDecls
                boundVars = concatMap (\ (Var_decl vars _ _) -> vars) varDecls
                varMap = mapToFreshVariables usedVars' boundVars
                varSortMap = mapToSort varDecls varMap

                -- creates:
                -- f(y1, ..., yn)
                replacedVarsF = replaceVars varMap f

                -- creates:
                -- x1 = y1 & ... & xn = yn
                equalityF =
                  Junction Con
                    (map (\ (x, y) ->
                          Equation
                            (Qual_var x (fromJust $ Map.lookup y varSortMap) nullRange)
                            Strong
                            (Qual_var y (fromJust $ Map.lookup y varSortMap) nullRange)
                            nullRange
                         ) $ Map.toList varMap)
                    nullRange

                -- creates:
                -- f(y1, ..., yn) => (x1 = y1 & ... & xn = yn)
                implyingEquality =
                  Relation replacedVarsF CAS.Implication equalityF nullRange

                -- creates:
                --   forall (y1: s1, ..., yn: sn) .
                --     f(y1, ..., yn) => x1 = y1 & ... & xn = yn)
                uniquenessF =
                  Quantification Universal
                    (map (\ (Var_decl vars sort r) ->
                           Var_decl (map (\ var ->
                                           Map.findWithDefault var var varMap
                                         ) vars) sort r
                         ) varDecls)
                    implyingEquality
                    nullRange

                f' = Junction Con [f, uniquenessF] nullRange
            in  Quantification Existential varDecls f' r
          Quantification q varDecls f r ->
            let usedVars' = Set.unions $ collectVars usedVars f :
                  map (collectVarsDecl usedVars) varDecls
                f' = resolveUniqueExistentialQuantifier' usedVars' f
            in  Quantification q varDecls f' r
          Junction j fs r ->
            let usedVars' = Set.unions $ map (collectVars usedVars) fs
                fs' = map (resolveUniqueExistentialQuantifier' usedVars') fs
            in  Junction j fs' r
          Relation f1 rel f2 r ->
            let usedVars' = Set.unions $ map (collectVars usedVars) [f1, f2]
                f1' = resolveUniqueExistentialQuantifier' usedVars' f1
                f2' = resolveUniqueExistentialQuantifier' usedVars' f2
            in  Relation f1' rel f2' r
          Negation f r ->
            Negation (resolveUniqueExistentialQuantifier' usedVars f) r
          Predication p ts r ->
            let usedVars' = Set.unions $ map (collectVarsT usedVars) ts
                ts' = map (resolveUniqueExistentialQuantifierT usedVars') ts
            in  Predication p ts' r
          Definedness t r ->
            let usedVars' = collectVarsT usedVars t
                t' = resolveUniqueExistentialQuantifierT usedVars' t
            in  Definedness t' r
          Equation t1 e t2 r ->
            let usedVars' = Set.unions $ map (collectVarsT usedVars) [t1, t2]
                t1' = resolveUniqueExistentialQuantifierT usedVars' t1
                t2' = resolveUniqueExistentialQuantifierT usedVars' t2
            in  Equation t1' e t2' r
          Membership t s r ->
            let usedVars' = collectVarsT usedVars t
                t' = resolveUniqueExistentialQuantifierT usedVars' t
            in  Membership t' s r
          _ -> x

        resolveUniqueExistentialQuantifierT :: (FormExtension f, Eq f)
                                            => Set.Set VAR -> TERM f -> TERM f
        resolveUniqueExistentialQuantifierT usedVars x = case x of
          Conditional t1 f t2 r ->
            let usedVars' = Set.unions $ map (collectVarsT usedVars) [t1, t2]
                t1' = resolveUniqueExistentialQuantifierT usedVars' t1
                t2' = resolveUniqueExistentialQuantifierT usedVars' t2
                f' = resolveUniqueExistentialQuantifier' usedVars' f
            in  Conditional t1' f' t2' r
          _ -> x


        collectVars :: (FormExtension f, Eq f)
                    => Set.Set VAR -> FORMULA f -> Set.Set VAR
        collectVars usedVars x = case x of
          Quantification _ decls f _ ->
            let varsF = collectVars usedVars f
                varsDeclsL = map (collectVarsDecl usedVars) decls
            in  Set.unions $ varsF : varsDeclsL
          Junction _ fs _ -> Set.unions $ map (collectVars usedVars) fs
          Relation f1 _ f2 _ ->
            let f1Vars = collectVars usedVars f1
                f2Vars = collectVars usedVars f2
            in  Set.union f1Vars f2Vars
          Negation f _ -> collectVars usedVars f
          Predication _ ts _ -> Set.unions $ map (collectVarsT usedVars) ts
          Definedness t _ -> collectVarsT usedVars t
          Equation t1 _ t2 _ ->
            let t1Vars = collectVarsT usedVars t1
                t2Vars = collectVarsT usedVars t2
            in  Set.union t1Vars t2Vars
          Membership t _ _ -> collectVarsT usedVars t
          _ -> Set.empty

        collectVarsT :: (FormExtension f, Eq f)
                     => Set.Set VAR -> TERM f -> Set.Set VAR
        collectVarsT usedVars x = case x of
          Qual_var v _ _ -> Set.singleton v
          Application _ ts _ -> Set.unions $ map (collectVarsT usedVars) ts
          Sorted_term t _ _ -> collectVarsT usedVars t
          Conditional t1 f t2 _ ->
            let t1Vars = collectVarsT usedVars t1
                t2Vars = collectVarsT usedVars t2
                fVars = collectVars usedVars f
            in  Set.unions [t1Vars, t2Vars, fVars]
          -- The other cannot occur in SuleCFOL
          _ -> Set.empty

        collectVarsDecl :: Set.Set VAR -> VAR_DECL -> Set.Set VAR
        collectVarsDecl usedVars x = case x of
          Var_decl vars _ _ -> Set.fromList vars `Set.union` usedVars

        replaceVars :: (FormExtension f, Eq f)
                    => Map.Map VAR VAR -> FORMULA f -> FORMULA f
        replaceVars varMap x = case x of
          Quantification q decls f r ->
            Quantification q decls (replaceVars varMap f) r
          Junction j fs r -> Junction j (map (replaceVars varMap) fs) r
          Relation f1 rel f2 r ->
            let f1' = replaceVars varMap f1
                f2' = replaceVars varMap f2
            in  Relation f1' rel f2' r
          Negation f r -> Negation (replaceVars varMap f) r
          Predication p ts r -> Predication p (map (replaceVarsT varMap) ts) r
          Definedness t r -> Definedness (replaceVarsT varMap t) r
          Equation t1 e t2 r ->
            let t1' = replaceVarsT varMap t1
                t2' = replaceVarsT varMap t2
            in  Equation t1' e t2' r
          Membership t s r -> Membership (replaceVarsT varMap t) s r
          _ -> x

        replaceVarsT :: (FormExtension f, Eq f)
                     => Map.Map VAR VAR -> TERM f -> TERM f
        replaceVarsT varMap x = case x of
          Qual_var v s r -> Qual_var (Map.findWithDefault v v varMap) s r
          Application o ts r -> Application o (map (replaceVarsT varMap) ts) r
          Sorted_term t s r -> Sorted_term (replaceVarsT varMap t) s r
          Conditional t1 f t2 r ->
            let t1' = replaceVarsT varMap t1
                t2' = replaceVarsT varMap t2
            in  Conditional t1' f t2' r
          -- The other cannot occur in SuleCFOL
          _ -> x

        mapToFreshVariables :: Set.Set VAR -> [VAR] -> Map.Map VAR VAR
        mapToFreshVariables usedVars =
          snd . foldr (\ var (usedVars', varMap) ->
                        let freshVar = freshVariable usedVars' var
                        in  (Set.insert freshVar usedVars',
                            Map.insert var freshVar varMap)
                      ) (usedVars, Map.empty)

        mapToSort :: [VAR_DECL] -> Map.Map VAR VAR -> Map.Map VAR SORT
        mapToSort varDecls varMap=
          foldr (\ (Var_decl vars sort _) sortMap ->
                  foldr (\ var sortMap' ->
                          let replacedVar = Map.findWithDefault var var varMap
                          in  Map.insert replacedVar sort sortMap'
                        ) sortMap vars
                ) Map.empty varDecls


        freshVariable :: Set.Set VAR -> VAR ->  VAR
        freshVariable usedVars var = freshVariable' 0
          where
            freshVariable' :: Int -> VAR
            freshVariable' i =
              let freshVar = mkSimpleId $ varName i
              in  if Set.member freshVar usedVars
                  then freshVariable' $ i + 1
                  else freshVar

            varName :: Int -> String
            varName i =
              show var ++ "_other" ++ if i == 0 then "" else "_" ++ show i


translateNamedFormula :: (FormExtension f, Eq f)
                      => SignWithRenamings f e
                      -> Named (FORMULA f) -> Result (Named TSign.Sentence)
translateNamedFormula signWithRenamings x = do
  let nameS = "sentence_" ++ (map toLower $ senAttr x)
  translated <- translateFormula signWithRenamings nameS $ sentence x
  return $ makeNamed nameS translated

translateFormula :: (FormExtension f, Eq f)
                 => SignWithRenamings f e -> String -> FORMULA f
                 -> Result TSign.Sentence
translateFormula signWithRenamings nameS f = do
  let name = NameString $ mkSimpleId nameS
  fofFormula <- toUnitaryFormula f
  return $ fofUnitaryFormulaToAxiom name fofFormula
  where
    -- GHC complains about the type variable f, and needs to infer the type
    -- itself at this point.
    -- toUnitaryFormula :: (FormExtension f, Eq f)
    --                  => FORMULA f
    --                  -> Result FOF_unitary_formula
    toUnitaryFormula x = case x of
      Quantification q vars f _ -> do
        let fofVars = translateVarDecls vars
        let variableList = map fst fofVars
        let variableDeclaration =
              FOFUF_logic $ FOFLF_binary $ FOFBF_assoc $ FOFBA_and $
              map (uncurry sortOfX) fofVars
        fofF <- toUnitaryFormula f
        case q of
          Universal ->
            let implication =
                  FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                  FOF_binary_nonassoc TAS.Implication variableDeclaration fofF
            in  return $ FOFUF_quantified $
                         FOF_quantified_formula ForAll variableList implication
          Existential ->
            let conjunction =
                  FOFUF_logic $ FOFLF_binary $ FOFBF_assoc $
                  FOFBA_and [variableDeclaration, fofF]
            in  return $ FOFUF_quantified $
                         FOF_quantified_formula Exists variableList conjunction
          -- Has been resolved/removed by prepareNamedFormula:
          Unique_existential ->
            fail "Unique_existential occurred where it cannot occur. This is a bug in Hets."
      Junction Con fs _ -> do
        fofs <- mapM toUnitaryFormula fs
        return $ FOFUF_logic $ FOFLF_binary $ FOFBF_assoc $ FOFBA_and fofs
      Junction Dis fs _ -> do
        fofs <- mapM toUnitaryFormula fs
        return $ FOFUF_logic $ FOFLF_binary $ FOFBF_assoc $ FOFBA_or fofs
      Relation f1 CAS.Implication f2 _ -> do
        fof1 <- toUnitaryFormula f1
        fof2 <- toUnitaryFormula f2
        return $ FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                 FOF_binary_nonassoc TAS.Implication fof1 fof2
      Relation f1 RevImpl f2 _ -> do
        fof1 <- toUnitaryFormula f1
        fof2 <- toUnitaryFormula f2
        return $ FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                 FOF_binary_nonassoc ReverseImplication fof1 fof2
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
                 FOFDPF_proposition $ TPTP_true
      Predication predSymb terms _ -> do
        predName <- case predSymb of
              Pred_name _ ->
                fail "An unqualified predicate has been detected. This is a bug in Hets."
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
      Sort_gen_ax _ _ -> fail "Sort generation axioms are not yet supported."
      -- There is no Definedness in SuleCFOL
      -- There is no Mixfix_formula - it only occurs during parsing
      -- There is no Unparsed_formula
      -- There is no QuantOp in SuleCFOL
      -- There is no QuantPred in SuleCFOL
      -- There is no ExtFORMULA in SuleCFOL
      _ -> fail "A formula that should not occur has occurred."

    translateVarDecls :: [VAR_DECL] -> [(TAS.Variable, SORT)]
    translateVarDecls = concatMap translateVarDecl

    translateVarDecl :: VAR_DECL -> [(TAS.Variable, SORT)]
    translateVarDecl x = case x of
      Var_decl vars sort _ -> zip (map variableOfVar vars) $ repeat sort


translateTerm :: (FormExtension f, Eq f)
              => SignWithRenamings f e
              -> TERM f
              -> Result TAS.FOF_term
translateTerm signWithRenamings x = case x of
  Qual_var var _ _ -> return $ FOFT_variable $ variableOfVar var
  Application opSymb terms _ -> do
    opName <- case opSymb of
          Op_name _ ->
            fail "An unqualified operation has been detected. This is a bug in Hets."
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
  _ -> fail "A term that should not occur has occurred."


fofUnitaryFormulaToAxiom :: TAS.Name -> FOF_unitary_formula -> TSign.Sentence
fofUnitaryFormulaToAxiom name f =
  let formula = FOFF_logic $ FOFLF_unitary f
  in  AF_FOF_Annotated $ FOF_annotated name Axiom formula (Annotations Nothing)

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
    gatherConnectedComponents sign =
      let topSortsL = Set.toList $ Rel.mostRight $ sortRel sign
          revReflTransClosureSortRel =
            Rel.transpose $ Rel.reflexive $ Rel.transClosure $ sortRel sign
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
        addIfConflicting (t1, t2) conflicts =
          if isConflicting t1 t2
          then Map.insert (opName, t1) (renameCurrentOp t1) $
                 Map.insert (opName, t2) (renameCurrentOp t2) conflicts
          else conflicts

        isConflicting :: OpType -> OpType -> Bool
        isConflicting t1 t2 =
          let sameNumberOfArgs = length (opArgs t1) == length (opArgs t2)
              allArgsInSameCC =
                all (isInSameCC connectedComponentMap) $
                  zip (opArgs t1) (opArgs t2)
          in  sameNumberOfArgs &&
                not (leqF sign t1 t2 || leqF sign t2 t1) &&
                allArgsInSameCC

        renameCurrentOp :: OpType -> OP_NAME
        renameCurrentOp opType =
          let argsS = intercalate "_" $ map show $ opArgs opType
              resultS = show $ opRes opType
              newOpNameS = show opName ++ "_" ++ argsS ++ "_" ++ resultS
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
        addIfConflicting (t1, t2) conflicts =
          if isConflicting t1 t2
          then Map.insert (predName, t1) (renameCurrentPred t1) $
                 Map.insert (predName, t2) (renameCurrentPred t2) conflicts
          else conflicts

        isConflicting :: PredType -> PredType -> Bool
        isConflicting t1 t2 =
          let sameNumberOfArgs = length (predArgs t1) == length (predArgs t2)
              allArgsInSameCC =
                all (isInSameCC connectedComponentMap) $
                  zip (predArgs t1) (predArgs t2)
          in  sameNumberOfArgs &&
                not (leqP sign t1 t2 || leqP sign t2 t1) &&
                allArgsInSameCC

        renameCurrentPred :: PredType -> PRED_NAME
        renameCurrentPred predType =
          let argsS = intercalate "_" $ map show $ predArgs predType
              newPredNameS = show predName ++ "_" ++ argsS
          in  predName { getTokens = [mkSimpleId newPredNameS] }

    isInSameCC :: Map.Map SORT Int -> (SORT, SORT) -> Bool
    isInSameCC connectedComponentMap (s1, s2) =
      let cc1 = Map.lookup s1 connectedComponentMap
          cc2 = Map.lookup s2 connectedComponentMap
      in  cc1 == cc2 && cc1 /= Nothing -- Nothing can not occur

    modifyOpMap :: Map.Map (OP_NAME, OpType) OP_NAME
                -> OP_NAME -> OpType -> OpMap -> OpMap
    modifyOpMap renamedOps opName opType opMap =
      case Map.lookup (opName, opType) renamedOps of
        Nothing -> opMap
        Just newOpName -> MapSet.insert newOpName opType $
                            MapSet.delete opName opType opMap

    modifyPredMap :: Map.Map (PRED_NAME, PredType) PRED_NAME
                  -> PRED_NAME -> PredType -> PredMap -> PredMap
    modifyPredMap renamedPreds predName predType predMap =
      case Map.lookup (predName, predType) renamedPreds of
        Nothing -> predMap
        Just newPredName -> MapSet.insert newPredName predType $
                              MapSet.delete predName predType predMap


translateSign :: (FormExtension f, Eq f)
              => CSign.Sign f e -> Result (TSign.Sign, [Named TSign.Sentence])
translateSign caslSign =
  return (tptpSign, sentencesOfSorts ++ sentencesOfOps)
  where
    tptpSign :: TSign.Sign
    tptpSign =
      let predicatesOfSorts =
            Set.foldr (\ sort predicates ->
                        Map.insertWith
                          Set.union
                          (predicateOfSort sort)
                          (Set.singleton 1)
                          predicates
                      ) Map.empty $ Rel.nodes $ sortRel caslSign
          constants =
            MapSet.foldWithKey (\ opName opType constants ->
                                 if null $ opArgs opType
                                 then Set.insert
                                        (functionOfOp opName)
                                        constants
                                 else constants
                               ) Set.empty $ opMap caslSign
          -- numbers cannot be generated due to prefix "function_"
          propositions =
            MapSet.foldWithKey (\ predName predType propositions ->
                                 if null $ predArgs predType
                                 then Set.insert
                                        (predicateOfPred predName)
                                        propositions
                                 else propositions
                               ) Set.empty $ predMap caslSign
          predicatesWithoutSorts =
            MapSet.foldWithKey (\ predName predType predicates ->
                                 if not $ null $ predArgs predType
                                 then Map.insertWith
                                       Set.union
                                       (predicateOfPred predName)
                                       (Set.singleton $ length $
                                         predArgs predType)
                                       predicates
                                 else predicates
                               ) Map.empty $ predMap caslSign
          predicates =
            Map.unionWith Set.union predicatesOfSorts predicatesWithoutSorts
          functors =
            MapSet.foldWithKey (\ opName opType functors ->
                                 if not $ null $ opArgs opType
                                 then Map.insertWith
                                        Set.union
                                        (functionOfOp opName)
                                        (Set.singleton $ length $ opArgs opType)
                                        functors
                                 else functors
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
      let varX = variableOfVar $ mkSimpleId "X"
          nameString = "sign_" ++ show subsort ++ "_subsort_of_" ++ show sort
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
          nameString = "sign_non_empty_sort_" ++ show sort
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
        createTopSortSentence otherTopSorts sort =
          let varX = variableOfVar $ mkSimpleId "X"
              nameString = "sign_topsort_" ++ show sort
              name = NameString $ mkSimpleId nameString

              formula = FOFUF_quantified $
                FOF_quantified_formula ForAll [varX] $
                FOFUF_logic $ FOFLF_binary $ FOFBF_nonassoc $
                FOF_binary_nonassoc
                  TAS.Implication
                  (sortOfX varX sort) $
                  FOFUF_logic $ FOFLF_binary $ FOFBF_assoc $ FOFBA_and $
                  Set.toList $
                  Set.map (negateUnitaryFormula . sortOfX varX) otherTopSorts

              sentence = fofUnitaryFormulaToAxiom name formula
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
                  map (FOFT_variable . variableOfVar) $ variables]

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
              sentence = fofUnitaryFormulaToAxiom name formula
          in  makeNamed nameString sentence

sortOfX :: TAS.Variable -> SORT -> FOF_unitary_formula
sortOfX var sort = FOFUF_atomic $ FOFAT_plain $
  FOFPAF_predicate (predicateOfSort sort) [FOFT_variable var]

functionOfOp :: OP_NAME -> TAS.TPTP_functor
functionOfOp opName =
  let functionName = "op_" ++ toAlphaNum (show opName)
  in  mkSimpleId functionName

predicateOfPred :: PRED_NAME -> TAS.Predicate
predicateOfPred predName =
  let predicateName = "pred_" ++ toAlphaNum (show predName)
  in  mkSimpleId predicateName

predicateOfSort :: SORT -> TAS.Predicate
predicateOfSort sort =
  let predicateName = "sort_" ++ toAlphaNum (show sort)
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
      '<' -> "OPENINGANGLE"
      '>' -> "CLOSINGANGLE"
      '_' -> "_"
      _ -> if isAlphaNum c then [c] else 'U' : showHex (ord c) ""


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
