{- |
Module      :  $Header$
Description :  Utilities for CspCASLProver related to the actual
               construction of Isabelle theories.
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
               Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Utilities for CspCASLProver related to the actual construction of
Isabelle theories.
-}

module CspCASLProver.Utils
    ( addAlphabetType
    , addAllBarTypes
    , addAllChooseFunctions
    , addAllCompareWithFun
    , addAllIntegrationTheorems
    , addAllGaAxiomsCollections
    , addEqFun
    , addEventDataType
    , addFlatTypes
    , addInstansanceOfEquiv
    , addJustificationTheorems
    , addPreAlphabet
    , addProcMap
    , addProcNameDatatype
    , addProjFlatFun
    , addProcTheorems
    ) where

import CASL.AS_Basic_CASL (SORT, OpKind (..), TERM (..))
import qualified CASL.Fold as CASL_Fold
import qualified CASL.Sign as CASLSign
import qualified CASL.Inject as CASLInject

import Common.Id (nullRange)
import Common.AS_Annotation (makeNamed, Named, SenAttr (..))
import qualified Common.Lib.Rel as Rel

import Comorphisms.CASL2PCFOL (mkEmbInjName, mkTransAxiomName, mkIdAxiomName)
import Comorphisms.CASL2SubCFOL (mkNotDefBotAxiomName, mkTotalityAxiomName)

import Comorphisms.CFOL2IsabelleHOL (IsaTheory)
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.AS_CspCASL_Process (PROCESS_NAME, PROCESS (..))
import CspCASL.SignCSP (CspCASLSign, ccSig2CASLSign, ChanNameMap, CspSign (..),
                        ProcProfile (..), CspCASLSen (..), isProcessEq)

import CspCASLProver.Consts
import CspCASLProver.CspProverConsts
import CspCASLProver.IsabelleUtils
import CspCASLProver.TransProcesses (transProcess, VarSource (..))

import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Isabelle.IsaConsts
import Isabelle.IsaSign
import Isabelle.Translate (transString)

-- -----------------------------------------------------------------------
-- Functions for adding the PreAlphabet datatype to an Isabelle theory --
-- -----------------------------------------------------------------------

-- | Add the PreAlphabet (built from a list of sorts) to an Isabelle
-- theory.
addPreAlphabet :: [SORT] -> IsaTheory -> IsaTheory
addPreAlphabet sortList isaTh =
   let preAlphabetDomainEntry = mkPreAlphabetDE sortList
       -- Add to the isabelle signature the new domain entry
   in updateDomainTab preAlphabetDomainEntry isaTh

-- | Make a Domain Entry for the PreAlphabet from a list of sorts.
mkPreAlphabetDE :: [SORT] -> DomainEntry
mkPreAlphabetDE sorts =
    (Type {typeId = preAlphabetS, typeSort = [isaTerm], typeArgs = []},
         map (\ sort ->
                  (mkVName (mkPreAlphabetConstructor sort),
                               [Type {typeId = convertSort2String sort,
                                      typeSort = [isaTerm],
                                      typeArgs = []}])
             ) sorts
    )

-- --------------------------------------------------------------
-- Functions for adding the eq functions and the compare_with --
-- functions to an Isabelle theory                            --
-- --------------------------------------------------------------

-- | Add the eq function to an Isabelle theory using a list of sorts
addEqFun :: [SORT] -> IsaTheory -> IsaTheory
addEqFun sortList isaTh =
    let eqtype = mkFunType preAlphabetType $ mkFunType preAlphabetType boolType
        isaThWithConst = addConst eq_PreAlphabetS eqtype isaTh
        mkEq sort =
            let x = mkFree "x"
                y = mkFree "y"
                lhs = binEq_PreAlphabet lhs_a y
                lhs_a = termAppl (conDouble (mkPreAlphabetConstructor sort)) x
                rhs = termAppl rhs_a y
                rhs_a = termAppl (conDouble (mkCompareWithFunName sort)) x
            in binEq lhs rhs
        eqs = map mkEq sortList
    in addPrimRec eqs isaThWithConst

-- | Add all compare_with functions for a given list of sorts to an
-- Isabelle theory. We need to know about the casl signature (data
-- part of a CspCASL spec) so that we can pass it on to the
-- addCompareWithFun function
addAllCompareWithFun :: CASLSign.CASLSign -> IsaTheory -> IsaTheory
addAllCompareWithFun caslSign isaTh =
    let sortList = Set.toList (CASLSign.sortSet caslSign)
    in foldl (addCompareWithFun caslSign) isaTh sortList

-- | Add a single compare_with function for a given sort to an
-- Isabelle theory.  We need to know about the casl signature (data
-- part of a CspCASL spec) to work out the RHS of the equations.
addCompareWithFun :: CASLSign.CASLSign -> IsaTheory -> SORT -> IsaTheory
addCompareWithFun caslSign isaTh sort =
    let sortList = Set.toList (CASLSign.sortSet caslSign)
        sortType = Type {typeId = convertSort2String sort, typeSort = [],
                                  typeArgs = []}
        funName = mkCompareWithFunName sort
        funType = mkFunType sortType $ mkFunType preAlphabetType boolType
        isaThWithConst = addConst funName funType isaTh
        sortSuperSet = CASLSign.supersortsOf sort caslSign
        mkEq sort' =
            let x = mkFree "x"
                y = mkFree "y"
                sort'Constructor = mkPreAlphabetConstructor sort'
                lhs = termAppl lhs_a lhs_b
                lhs_a = termAppl (conDouble funName) x
                lhs_b = termAppl (conDouble sort'Constructor) y
                sort'SuperSet = CASLSign.supersortsOf sort' caslSign
                commonSuperList = Set.toList (Set.intersection
                                                 sortSuperSet
                                                 sort'SuperSet)

                -- If there are no tests then the rhs=false else
                -- combine all tests using binConj
                rhs = if null allTests
                      then false
                      else foldr1 binConj allTests

                -- The tests produce a list of equations for each test
                -- Test 1 =  test equality at: current sort vs current sort
                -- Test 2 =  test equality at: current sort vs super sorts
                -- Test 3 =  test equality at: super sorts  vs current sort
                -- Test 4 =  test equality at: super sorts  vs super sorts
                allTests = concat [test1, test2, test3, test4]
                test1 = if sort == sort' then [binEq x y] else []
                test2 = if Set.member sort sort'SuperSet
                        then [binEq x (mkInjection sort' sort y)]
                        else []
                test3 = if Set.member sort' sortSuperSet
                        then [binEq (mkInjection sort sort' x) y]
                        else []
                test4 = if null commonSuperList
                        then []
                        else map test4_atSort commonSuperList
                test4_atSort s = binEq (mkInjection sort s x)
                                       (mkInjection sort' s y)
            in binEq lhs rhs
        eqs = map mkEq sortList
    in addPrimRec eqs isaThWithConst

-- ------------------------------------------------------
-- Functions that creates a lemma for group many lemmas
-- ------------------------------------------------------

-- | Add a series of lemmas sentences that collect together all the
-- automatically generate axioms. This allow us to group large collections of
-- lemmas in to a single lemma. This cuts down on the repreated addition of
-- lemmas in the proofs. We need to the CASL signature (from the datapart) and
-- the PFOL Signature to pass it on. We could recalculate the PFOL signature
-- from the CASL signature here, but we dont as it can be passed in. We need
-- the PFOL signature which is the data part CASL signature after translation
-- to PCFOL (i.e. without subsorting)
addAllGaAxiomsCollections :: CASLSign.CASLSign -> CASLSign.CASLSign ->
                        IsaTheory -> IsaTheory
addAllGaAxiomsCollections caslSign pfolSign isaTh =
    let sortRel = Rel.toList (CASLSign.sortRel caslSign)
        sorts = Set.toList (CASLSign.sortSet caslSign)
    in addLemmasCollection lemmasEmbInjAxS (getCollectionEmbInjAx sortRel)
     $ addLemmasCollection lemmasIdentityAxS (getCollectionIdentityAx caslSign)
     $ addLemmasCollection lemmasNotDefBotAxS (getCollectionNotDefBotAx sorts)
     $ addLemmasCollection lemmasTotalityAxS (getCollectionTotAx pfolSign)
     $ addLemmasCollection lemmasTransAxS (getCollectionTransAx caslSign)
       isaTh

-- ------------------------------------------------------
-- Functions for producing the Justification theorems --
-- ------------------------------------------------------

-- | Add all justification theorems to an Isabelle Theory. We need to
-- the CASL signature (from the datapart) and the PFOL Signature to
-- pass it on. We could recalculate the PFOL signature from the CASL
-- signature here, but we dont as it can be passed in. We need the
-- PFOL signature which is the data part CASL signature after
-- translation to PCFOL (i.e. without subsorting)
addJustificationTheorems :: CASLSign.CASLSign -> CASLSign.CASLSign ->
                            IsaTheory -> IsaTheory
addJustificationTheorems caslSign pfolSign isaTh =
    let sortRel = Rel.toList (CASLSign.sortRel caslSign)
        sorts = Set.toList (CASLSign.sortSet caslSign)
    in addTransitivityTheorem sorts sortRel
       $ addAllInjectivityTheorems pfolSign sorts sortRel
       $ addAllDecompositionTheorem caslSign pfolSign sorts sortRel
       $ addSymmetryTheorem sorts
       $ addReflexivityTheorem
         isaTh

-- | Add the reflexivity theorem and proof to an Isabelle Theory
addReflexivityTheorem :: IsaTheory -> IsaTheory
addReflexivityTheorem isaTh =
    let name = reflexivityTheoremS
        x = mkFree "x"
        thmConds = []
        thmConcl = binEq_PreAlphabet x x
        proof' = IsaProof {
                   proof = [Apply [Induct x, Auto] False],
                   end = Done
                 }
    in addTheoremWithProof name thmConds thmConcl proof' isaTh

-- | Add the symmetry theorem and proof to an Isabelle Theory. We need
-- to know the number of sorts, but instead we are given a list of
-- all sorts
addSymmetryTheorem :: [SORT] -> IsaTheory -> IsaTheory
addSymmetryTheorem _ isaTh =
    let -- numSorts = length(sorts)
        name = symmetryTheoremS
        x = mkFree "x"
        y = mkFree "y"
        thmConds = [binEq_PreAlphabet x y]
        thmConcl = binEq_PreAlphabet y x
        -- We want to induct Y then apply simp numSorts times and reapeat this
        -- apply as many times as possibe, thus the true at the end
        -- inductY = [Apply ((Induct y):(replicate numSorts Simp)) True]
        -- Bug in above in isabelle?? not sure - does not work for all specs?
        -- Now we do induction on Y then auto - I think this works for all specs
        inductY = [Apply [Induct y, Auto] True]
        proof' = IsaProof {
                   -- Add in front of inductY a apply induct on x
                   proof = Apply [Induct x] False : inductY,
                   end = Done
                 }
    in addTheoremWithProof name thmConds thmConcl proof' isaTh

-- | Add all the decoposition theorems and proofs
addAllDecompositionTheorem :: CASLSign.CASLSign -> CASLSign.CASLSign
                           -> [SORT] -> [(SORT, SORT)]
                           -> IsaTheory -> IsaTheory
addAllDecompositionTheorem caslSign pfolSign sorts sortRel isaTh =
    let tripples = [(s1, s2, s3) |
                    (s1, s2) <- sortRel, (s2', s3) <- sortRel, s2 == s2']
    in foldl (addDecompositionTheorem caslSign pfolSign sorts)
       isaTh tripples

-- | Add the decomposition theorem and proof which should be deduced
-- from the transitivity axioms from the translation CASL2PCFOL;
-- CASL2SubCFOL for a pair of injections represented as a tripple of
-- sorts. e.g. (S,T,U) means produce the lemma and proof for
-- inj_T_U(inj_S_T(x)) = inj_S_U(x). As a work around, we need to
-- know all sorts to pass them on.
addDecompositionTheorem :: CASLSign.CASLSign -> CASLSign.CASLSign -> [SORT]
                        -> IsaTheory -> (SORT, SORT, SORT)
                        -> IsaTheory
addDecompositionTheorem caslSign pfolSign sorts isaTh (s1, s2, s3) =
    let x = mkFree "x"
        -- These 5 lines make use of currying
        injOp_s1_s2 = mkInjection s1 s2
        injOp_s2_s3 = mkInjection s2 s3
        injOp_s1_s3 = mkInjection s1 s3
        inj_s1_s2_s3_x = injOp_s2_s3 (injOp_s1_s2 x)
        inj_s1_s3_x = injOp_s1_s3 x
        definedOp_s1 = getDefinedOp sorts s1
        definedOp_s3 = getDefinedOp sorts s3

        name = getDecompositionThmName (s1, s2, s3)
        conds = []
        concl = binEq inj_s1_s2_s3_x inj_s1_s3_x
        -- We only want to add these lemma sets if they exist
        lemmasIdentityAxS' = if null $ getCollectionIdentityAx caslSign
                             then []
                             else [lemmasIdentityAxS]
        lemmasTransAxS' = if null $ getCollectionTransAx caslSign
                          then []
                          else [lemmasTransAxS]
        lemmasTotalityAxS' = if null $ getCollectionTotAx pfolSign
                             then []
                             else [lemmasTotalityAxS]
        lemmasNotDefBotAxS' = if null $ getCollectionNotDefBotAx sorts
                              then []
                              else [lemmasNotDefBotAxS]
        proof' = IsaProof [Apply [CaseTac (definedOp_s3 inj_s1_s2_s3_x)] False,
                           -- Case 1
                           Apply [SubgoalTac (definedOp_s1 x)] False,
                           Apply [Insert $ lemmasIdentityAxS' ++
                                        lemmasTransAxS'] False,
                           Apply [Simp] False,
                           Apply [SimpAdd Nothing lemmasTotalityAxS'] False,

                           -- Case 2
                           Apply [SubgoalTac (
                             termAppl notOp (definedOp_s3 inj_s1_s3_x))] False,
                           Apply [SimpAdd Nothing lemmasNotDefBotAxS'] False,
                           Apply [SimpAdd Nothing lemmasTotalityAxS'] False]
                           Done
    in addTheoremWithProof name conds concl proof' isaTh

-- | Add all the injectivity theorems and proofs
addAllInjectivityTheorems :: CASLSign.CASLSign -> [SORT] -> [(SORT, SORT)] ->
                             IsaTheory -> IsaTheory
addAllInjectivityTheorems pfolSign sorts sortRel isaTh =
    foldl (addInjectivityTheorem pfolSign sorts sortRel) isaTh sortRel

-- | Add the injectivity theorem and proof which should be deduced
-- from the embedding_Injectivity axioms from the translation
-- CASL2PCFOL; CASL2SubCFOL for a single injection represented as a
-- pair of sorts. As a work around, we need to know all sorts to
-- pass them on
addInjectivityTheorem :: CASLSign.CASLSign -> [SORT] -> [(SORT, SORT)] ->
                         IsaTheory -> (SORT, SORT) -> IsaTheory
addInjectivityTheorem pfolSign sorts sortRel isaTh (s1, s2) =
    let x = mkFree "x"
        y = mkFree "y"
        injX = mkInjection s1 s2 x
        injY = mkInjection s1 s2 y
        definedOp_s1 = getDefinedOp sorts s1
        definedOp_s2 = getDefinedOp sorts s2
        name = getInjectivityThmName (s1, s2)
        conds = [binEq injX injY]
        concl = binEq x y
        -- We only want to add these lemma sets if they exist
        lemmasEmbInjAxS' = if null $ getCollectionEmbInjAx sortRel
                           then []
                           else [lemmasEmbInjAxS]
        lemmasTotalityAxS' = if null $ getCollectionTotAx pfolSign
                             then []
                             else [lemmasTotalityAxS]
        lemmasNotDefBotAxS' = if null $ getCollectionNotDefBotAx sorts
                              then []
                              else [lemmasNotDefBotAxS]

        proof' = IsaProof [Apply [CaseTac (definedOp_s2 injX)] False,
                           -- Case 1
                           Apply [SubgoalTac (definedOp_s1 x)] False,
                           Apply [SubgoalTac (definedOp_s1 y)] False,
                           Apply [Insert lemmasEmbInjAxS'] False,
                           Apply [Simp] False,
                           Apply [SimpAdd Nothing lemmasTotalityAxS'] False,
                           Apply [SimpAdd (Just No_asm_use) lemmasTotalityAxS']
                                False,
                           -- Case 2
                           Apply [SubgoalTac (termAppl notOp (definedOp_s1 x))]
                                False,
                           Apply [SubgoalTac (termAppl notOp (definedOp_s1 y))]
                                False,
                           Apply [SimpAdd Nothing lemmasNotDefBotAxS'] False,
                           Apply [SimpAdd Nothing lemmasTotalityAxS'] False,
                           Apply [SimpAdd (Just No_asm_use) lemmasTotalityAxS']
                                False]
                           Done
    in addTheoremWithProof name conds concl proof' isaTh

-- | Add the transitivity theorem and proof to an Isabelle Theory. We
-- need to know the number of sorts to know how much induction to
-- perfom and also the sub-sort relation to build the collection of
-- injectivity theorem names
addTransitivityTheorem :: [SORT] -> [(SORT, SORT)] -> IsaTheory -> IsaTheory
addTransitivityTheorem sorts sortRel isaTh =
    let -- First we extend the theory to include the collections of CspCASL
        -- prover's injectivity and decomposition theorems
        isaThExt =
            addLemmasCollection lemmasCCProverInjectivityThmsS
                (getColInjectivityThmName sortRel)
          $ addLemmasCollection lemmasCCProverDecompositionThmsS
                (getColDecompositionThmName sortRel)
            isaTh
        numSorts = length sorts
        name = transitivityS
        x = mkFree "x"
        y = mkFree "y"
        z = mkFree "z"
        thmConds = [binEq_PreAlphabet x y, binEq_PreAlphabet y z]
        thmConcl = binEq_PreAlphabet x z
        -- We only want to add these lemma sets if they exist
        lemmasCCProverDecompositionThmsS' =
            if null $ getColDecompositionThmName sortRel
            then []
            else [lemmasCCProverDecompositionThmsS]
        lemmasCCProverInjectivityThmsS' =
            if null $ getColInjectivityThmName sortRel
            then []
            else [lemmasCCProverInjectivityThmsS]

        simpPlus = SimpAdd Nothing (lemmasCCProverDecompositionThmsS' ++
                                    lemmasCCProverInjectivityThmsS')
        -- We want to induct Y, Z and perfom simplification is a clever way,
        -- namely,
        -- apply(induct y, (induct z, simp * numSorts) * numSorts)+
        inductZ = (Induct z) : (replicate numSorts simpPlus)
        inductYZ = ((Induct y) : concat (replicate numSorts inductZ))
        -- Main induction and simplification proof command
        inductPC = [Apply inductYZ True]
        proof' = IsaProof {
                   proof = (Apply [Induct x] False : inductPC),
                   end = Done
                 }
    in addTheoremWithProof name thmConds thmConcl proof' isaThExt

-- -----------------------------------------------------------
-- Functions for producing instances of equivalence classes --
-- ------------------------------------------------------------

-- | Function to add preAlphabet as an equivalence relation to an
-- Isabelle theory
addInstansanceOfEquiv :: IsaTheory -> IsaTheory
addInstansanceOfEquiv isaTh =
    let equivSort = [IsaClass equivTypeClassS]
        equivProof = IsaProof [Apply [Other "intro_classes"] False,
                               Apply [Other ("unfold " ++ preAlphabetSimS
                                             ++ "_def")] False,
                               Apply [Other ("rule " ++ reflexivityTheoremS)]
                                     False,
                               Apply [Other ("rule " ++ transitivityS
                                                ++ ", auto")] False,
                               Apply [Other ("rule " ++ symmetryTheoremS
                                                ++ ", simp")] False]
                               Done
        x = mkFree "x"
        y = mkFree "y"
        defLhs = binEqvSim x y
        defRhs = binEq_PreAlphabet x y
        def = IsaEq defLhs defRhs
    in addInstanceOf preAlphabetS [] equivSort
           [(preAlphabetSimS, def)] equivProof isaTh

-- -----------------------------------------------------------
-- Functions for producing the alphabet type               --
-- -----------------------------------------------------------

-- | Function to add the Alphabet type (type syonnym) to an Isabelle theory
addAlphabetType :: IsaTheory -> IsaTheory
addAlphabetType isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sign_tsig = tsig isaTh_sign
        myabbrs = abbrs isaTh_sign_tsig
        abbrsNew = Map.insert alphabetS ([], preAlphabetQuotType) myabbrs

        isaTh_sign_updated = isaTh_sign {
                               tsig = isaTh_sign_tsig {abbrs = abbrsNew}
                             }
    in (isaTh_sign_updated, snd isaTh)

-- -----------------------------------------------------------
-- Functions for producing the bar types                   --
-- -----------------------------------------------------------

-- | Function to add all the bar types to an Isabelle theory.
addAllBarTypes :: [SORT] -> IsaTheory -> IsaTheory
addAllBarTypes sorts isaTh = foldl addBarType isaTh sorts

-- | Function to add the bar types of a sort to an Isabelle theory.
addBarType :: IsaTheory -> SORT -> IsaTheory
addBarType isaTh sort =
    let sortBarString = mkSortBarString sort
        barType = mkSortBarType sort
        isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        x = mkFree "x"
        y = mkFree "y"
        rhs = termAppl (conDouble (mkPreAlphabetConstructor sort)) y
        bin_eq = binEq x $ termAppl (conDouble classS ) rhs
        exist_eq = termAppl (conDouble exS) (Abs y bin_eq NotCont)
        subset = SubSet x alphabetType exist_eq
        sen = TypeDef barType subset (IsaProof [] (By Auto))
        namedSen = (makeNamed sortBarString sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- -----------------------------------------------------------
-- Functions for producing the choose functions            --
-- -----------------------------------------------------------

-- | Add all choose functions for a given list of sorts to an Isabelle
-- theory.
addAllChooseFunctions :: [SORT] -> IsaTheory -> IsaTheory
addAllChooseFunctions sorts isaTh =
    let isaTh' = foldl addChooseFunction isaTh sorts -- add function and def
    in foldl addChooseFunctionLemma isaTh' sorts -- add theorem and proof

-- | Add a single choose function for a given sort to an Isabelle
-- theory.  The following Isabelle code is produced by this function:
-- consts choose_Nat :: "Alphabet => Nat"
-- defs choose_Nat_def: "choose_Nat x == contents{y . class(C_Nat y) = x}"
addChooseFunction :: IsaTheory -> SORT -> IsaTheory
addChooseFunction isaTh sort =
    let -- constant
        sortType = Type {typeId = convertSort2String sort,
                         typeSort = [],
                         typeArgs = []}
        chooseFunName = mkChooseFunName sort
        chooseFunType = mkFunType alphabetType sortType
        -- definition
        x = mkFree "x"
        y = mkFree "y"
        contentsOp = termAppl (conDouble "contents")
        sortConsOp = termAppl (conDouble (mkPreAlphabetConstructor sort))
        bin_eq = binEq (classOp $ sortConsOp y) x
        subset = SubSet y sortType bin_eq
        lhs = mkChooseFunOp sort x
        rhs = contentsOp (Set subset)
    in  -- Add defintion to theory
        addDef chooseFunName lhs rhs
        -- Add constant to theory
      $ addConst chooseFunName chooseFunType isaTh

-- | Add a single choose function lemma for a given sort to an
-- Isabelle theory.  The following Isabelle code is produced by this
-- function: lemma "choose_Nat (class (C_Nat x)) = x". The proof is
-- also produced.

addChooseFunctionLemma :: IsaTheory -> SORT -> IsaTheory
addChooseFunctionLemma isaTh sort =
    let sortType = Type {typeId = convertSort2String sort,
                         typeSort = [],
                         typeArgs = []}
        chooseFunName = mkChooseFunName sort
        x = mkFree "x"
        y = mkFree "y"
        sortConsOp = termAppl (conDouble (mkPreAlphabetConstructor sort))
        -- theorm
        subgoalTacTermLhsBinEq = binEq (classOp $ sortConsOp y)
                                       (classOp $ sortConsOp x)
        subgoalTacTermLhs = Set $ SubSet y sortType subgoalTacTermLhsBinEq
        subgoalTacTermRhs = Set $ FixedSet [x]
        subgoalTacTerm = binEq subgoalTacTermLhs subgoalTacTermRhs
        thmConds = []
        thmConcl = binEq (mkChooseFunOp sort $ classOp $ sortConsOp x) x
        proof' = IsaProof [Apply [Other ("unfold " ++ chooseFunName ++ "_def")]
                                False,
                           Apply [SubgoalTac subgoalTacTerm] False,
                           Apply [Simp] False,
                           Apply [SimpAdd Nothing [quotEqualityS]] False,
                           Apply [Other ("unfold " ++ preAlphabetSimS
                                           ++ "_def")] False,
                           Apply [Auto] False]
                           Done
    in addTheoremWithProof chooseFunName thmConds thmConcl proof' isaTh

-- -----------------------------------------------------------
-- Functions for producing the integration theorems        --
-- -----------------------------------------------------------

-- | Add all the integration theorems. We need to know all the sorts
-- to produce all the theorems. We need to know the CASL signature
-- of the data part to pass it on as an argument.
addAllIntegrationTheorems :: [SORT] -> CASLSign.CASLSign -> IsaTheory ->
                             IsaTheory
addAllIntegrationTheorems sorts caslSign isaTh =
    let pairs = [(s1, s2) | s1 <- sorts, s2 <- sorts]
    in foldl (addIntegrationTheorem_A caslSign) isaTh pairs

-- | Add Integration theorem A -- Compare to elements of the Alphabet.
-- We add the integration theorem based on the sorts of both
-- elements of the alphabet. We need to know the subsort relation to
-- find the highest common sort, but we pass in the CASL signature
-- for the data part.
addIntegrationTheorem_A :: CASLSign.CASLSign -> IsaTheory -> (SORT, SORT) ->
                           IsaTheory
addIntegrationTheorem_A caslSign isaTh (s1, s2) =
    let sortRel = Rel.toList (CASLSign.sortRel caslSign)
        s1SuperSet = CASLSign.supersortsOf s1 caslSign
        s2SuperSet = CASLSign.supersortsOf s2 caslSign
        commonSuperList = Set.toList (Set.intersection
                                         (Set.insert s1 s1SuperSet)
                                         (Set.insert s2 s2SuperSet))
        x = mkFree "x"
        y = mkFree "y"
        s1ConsOp = termAppl (conDouble (mkPreAlphabetConstructor s1))
        s2ConsOp = termAppl (conDouble (mkPreAlphabetConstructor s2))
        rhs = binEq (classOp $ s1ConsOp x) (classOp $ s2ConsOp y)
        lhs = if null commonSuperList
              then false
              else
                  -- BUG pick any common sort for now (this does hold
                  -- and is valid) we should pick the top most one.
                  let s' = head commonSuperList
                  in binEq (mkInjection s1 s' x) (mkInjection s2 s' y)
        thmConds = []
        thmConcl = binEq rhs lhs
        -- theorem names for proof
        colInjThmNames = getColInjectivityThmName sortRel
        colDecompThmNames = getColDecompositionThmName sortRel
        proof' = IsaProof [Apply [SimpAdd Nothing [quotEqualityS]] False,
                           Apply [Other ("unfold " ++ preAlphabetSimS
                                             ++ "_def")] False,
                           Apply [AutoSimpAdd Nothing
                                  (colDecompThmNames ++ colInjThmNames)] False]
                           Done
    in addTheoremWithProof "IntegrationTheorem_A"
       thmConds thmConcl proof' isaTh

-- ------------------------------------------------------------------------
-- Functions for adding the Event datatype and the channel encoding     --
-- ------------------------------------------------------------------------

-- | Add the Event datatype (built from a list of channels and the subsort
-- relation) to an Isabelle theory.
addEventDataType :: Rel.Rel SORT -> ChanNameMap -> IsaTheory -> IsaTheory
addEventDataType sortRel chanNameMap isaTh =
    let eventDomainEntry = mkEventDE sortRel chanNameMap
       -- Add to the isabelle signature the new domain entry
    in updateDomainTab eventDomainEntry isaTh

-- | Make a Domain Entry for the Event from a list of sorts.
mkEventDE :: Rel.Rel SORT -> ChanNameMap -> DomainEntry
mkEventDE _ chanNameMap =
    let flat = (mkVName flatS, [alphabetType])
        -- Make a constuctor type for a channel with a target sort
        mkChanCon (c, s) = (mkVName (convertChannelString c),
                                        [mkSortBarType s])
        -- Make pairs of channel and sorts, where we only build the declared
        -- channels and not the subsorted channels.
        mkAllChanCons = map mkChanCon $ Map.toList chanNameMap
        -- We build the event type out of the flat constructions and the list of
        -- channel constructions
    in (eventType, (flat : mkAllChanCons))

-- | Add the eq function to an Isabelle theory using a list of sorts
addProjFlatFun :: IsaTheory -> IsaTheory
addProjFlatFun isaTh =
    let eqtype = mkFunType eventType alphabetType
        isaThWithConst = addConst projFlatS eqtype isaTh
        x = mkFree "x"
        lhs = termAppl (conDouble projFlatS) flatX
        flatX = termAppl (conDouble flatS) x
        rhs = x
        -- projFlat(Flat x) = x
        eqs = [binEq lhs rhs]
    in addPrimRec eqs isaThWithConst

-- | Function to add all the Flat types. These capture the original sorts, but
-- use the bar values instead wrapped up in the Flat constructor(the Flat
-- channel). We use this as a set of normal communications (action prefix,
-- send, recieve).
addFlatTypes :: [SORT] -> IsaTheory -> IsaTheory
addFlatTypes sorts isaTh = foldl addFlatType isaTh sorts

-- | Function to add the flat type of a sort to an Isabelle theory.
addFlatType :: IsaTheory -> SORT -> IsaTheory
addFlatType isaTh sort =
    let sortFlatString = mkSortFlatString sort
        flatType = Type {typeId = sortFlatString, typeSort = [], typeArgs = []}
        isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        x = mkFree "x"
        y = mkFree "y"
        flatY = termAppl (conDouble flatS) y
        -- y in sort_Bar
        condition1 = binMembership y (conDouble $ mkSortBarString sort)
        -- x = Flat y
        condition2 = binEq x flatY
        -- y in sort_Bar /\ x = Flat y
        condition_eq = binConj condition1 condition2
        exist_eq = termAppl (conDouble exS) (Abs y condition_eq NotCont)
        subset = SubSet x eventType exist_eq
        proof' = AutoSimpAdd Nothing [(mkSortBarString sort) ++ "_def"]
        sen = TypeDef flatType subset (IsaProof [] (By proof'))
        namedSen = (makeNamed sortFlatString sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- ------------------------------------------------------------------------
-- Functions for adding the process name datatype to an Isabelle theory --
-- ------------------------------------------------------------------------

-- | Add process name datatype which has a constructor for each
-- process name (along with the arguments for the process) in the
-- CspCASL Signature to an Isabelle theory
addProcNameDatatype :: CspSign -> IsaTheory -> IsaTheory
addProcNameDatatype cspSign isaTh =
    let -- Create a list of pairs of process names and thier profiles
        procSetList = Map.toList (procSet cspSign)
        procNameDomainEntry = mkProcNameDE procSetList
    in updateDomainTab procNameDomainEntry isaTh

-- | Make a proccess name Domain Entry from a list of a Process name and profile
-- pair. This creates a data type for the process names.
mkProcNameDE :: [(PROCESS_NAME, ProcProfile)] -> DomainEntry
mkProcNameDE processes =
    let -- The a list of pairs of constructors and their arguments
        constructors = map mk_cons processes
        -- Take a proccess name and its argument sorts (also its
        -- commAlpha - thrown away) and make a pair representing the
        -- constructor and the argument types
        -- Note: The processes need to have arguments of the bar variants of the
        -- sorts not the original sorts
        mk_cons (procName, (ProcProfile sorts _)) =
            (mkVName (mkProcNameConstructor procName), map mkSortBarType sorts)
    in
    (procNameType, constructors)

-- -----------------------------------------------------------------------
-- Functions adding the process map function to an Isabelle theory     --
-- -----------------------------------------------------------------------

-- | Add the function procMap to an Isabelle theory. This function maps process
-- names to real processes build using the same names and the alphabet i.e.,
-- ProcName => (ProcName, Alphabet) proc. We need to know the CspCASL
-- sentences and the casl signature (data part). We need the PCFOL and CFOL
-- signatures of the data part after translation to PCFOL and CFOL to pass
-- along the process translation.
addProcMap :: [Named CspCASLSen] -> CspCASLSign ->
              CASLSign.Sign () () -> CASLSign.Sign () () ->
              IsaTheory -> IsaTheory
addProcMap namedSens ccSign pcfolSign cfolSign isaTh =
    let caslSign = ccSig2CASLSign ccSign
        -- Translate a fully qualified variable (CASL term) to Isabelle
        tyToks = CFOL2IsabelleHOL.typeToks caslSign
        trForm = CFOL2IsabelleHOL.formTrCASL
        strs = CFOL2IsabelleHOL.getAssumpsToks caslSign
        transVar fqVar = CASL_Fold.foldTerm
                         (CFOL2IsabelleHOL.transRecord
                          caslSign tyToks trForm strs) fqVar
        -- Extend Isabelle theory with additional constant
        isaThWithConst = addConst procMapS procMapType isaTh
        -- Get the plain sentences from the named senetences which are not
        -- implied i.e., where axiom=true. first filter the axioms only then
        -- stip the named annotation off them.
        sens = map (sentence) $
               filter (isAxiom) namedSens
        -- Filter so we only have proccess equations and no CASL senetences
        processEqs = filter isProcessEq sens
        -- the term representing the procMap that takes a term as a
        -- parameter
        procMapTerm = termAppl (conDouble procMapS)
        -- Make a single equation for the primrec from a process equation
        mkEq (ProcessEq procName fqVars _ proc) =
            let -- Make the name (string) for this process
                procNameString = convertProcessName2String procName
                -- Change the name to a term
                procNameTerm = conDouble procNameString
                -- Turn the list of variables into a list of Isabelle
                -- free variables
                varTerms = map transVar fqVars
                lhs = procMapTerm (foldl termAppl procNameTerm varTerms)
                addToVdm fqvar vdm' =
                    case fqvar of
                      Qual_var v _ _ -> Map.insert v GlobalParameter vdm'
                      _ -> error "CspCASLProver.Utils.addProcMap: Term other than fully qualified variable in process parameter variable list"
                vdm = foldr addToVdm Map.empty fqVars
                rhs = transProcess ccSign pcfolSign cfolSign vdm proc
             in binEq lhs rhs
        -- to avoid warnings we specify the behaviour on CASL sentences. This
        -- should never be called as they have been filtered out.
        mkEq (CASLSen _ ) = error "CspCASLProver.Utils.addProcMap: Unexpected CASLSen, Expected ProcessEq"
        -- Build equations for primrec using process equations
        eqs = map mkEq processEqs
    in addPrimRec eqs isaThWithConst

-- | Add the implied process equations as theorems to be proven by the user. We
-- need to know the CspCASL sentences and the casl signature (data part). We
-- need the PCFOL and CFOL signatures of the data part after translation to
-- PCFOL and CFOL to pass along the process translation.
addProcTheorems :: [Named CspCASLSen] -> CspCASLSign ->
                   CASLSign.Sign () () -> CASLSign.Sign () () ->
                   IsaTheory -> IsaTheory
addProcTheorems namedSens ccSign pcfolSign cfolSign isaTh =
    let -- Get the plain sentences from the named senetences which are
        -- implied i.e., where axiom=false. first filter the axioms only then
        -- stip the named annotation off them.
        sens = map (sentence) $
               filter (not . isAxiom) namedSens
        -- Filter so we only have proccess equations and no CASL senetences
        processEqs = filter isProcessEq sens
        -- Make a single equation for the primrec from a process equation
        mkEq (ProcessEq procName fqVars _ proc) =
            let -- the LHS a a process in abstract syntax i.e. process name with
                -- variables as arguments
                lhs' = NamedProcess procName fqVars nullRange
                addToVdm fqvar vdm' =
                    case fqvar of
                      Qual_var v _ _ -> Map.insert v GlobalParameter vdm'
                      _ -> error "CspCASLProver.Utils.addProcMap: Term other than fully qualified variable in process parameter variable list"
                vdm = foldr addToVdm Map.empty fqVars
                lhs = transProcess ccSign pcfolSign cfolSign vdm lhs'
                rhs = transProcess ccSign pcfolSign cfolSign vdm proc
             in cspProverbinEqF lhs rhs
        -- to avoid warnings we specify the behaviour on CASL sentences. This
        -- should never be called as they have been filtered out.
        mkEq (CASLSen _ ) = error "CspCASLProver.Utils.addProcMap: Unexpected CASLSen, Expected ProcessEq"
        eqs = map mkEq processEqs
        proof' = toIsaProof Sorry
        addTheorem eq' isaTh' = addTheoremWithProof "UserTheorem" [] eq'
                               proof' isaTh'
    in foldr addTheorem isaTh eqs


-- ----------------------------------------------------------
-- Basic function to help keep strings consistent         --
-- ----------------------------------------------------------

-- | Return the list of strings of all gn_totality axiom names produced by the
-- translation CASL2PCFOL; CASL2SubCFOL. This function is not implemented in a
-- satisfactory way.
getCollectionTotAx :: CASLSign.CASLSign -> [String]
getCollectionTotAx pfolSign =
    let opList = Map.toList $ CASLSign.opMap pfolSign
        -- This filter is not quite right
        totFilter (_, setOpType) = let listOpType = Set.toList setOpType
                                 in CASLSign.opKind (head listOpType) == Total
        totList = filter totFilter opList
    in map (mkTotalityAxiomName . fst) totList

-- | Return the name of the definedness function for a sort. We need
-- to know all sorts to perform this workaround
-- This function is not implemented in a satisfactory way
getDefinedName :: [SORT] -> SORT -> String
getDefinedName sorts s =
    let index = List.elemIndex s sorts
        str = case index of
                Nothing -> ""
                Just i -> show (i + 1)
    in "gn_definedX" ++ str

-- | Return the name of the injection as it is used in the alternative
-- syntax of the injection from one sort to another.
-- This function is not implemented in a satisfactory way
getInjectionName :: SORT -> SORT -> String
getInjectionName s s' =
    let t = CASLSign.toOP_TYPE (CASLSign.OpType {CASLSign.opKind = Total,
                                                CASLSign.opArgs = [s],
                                                CASLSign.opRes = s'})
        injName = show $ CASLInject.uniqueInjName t
    in injName

-- | Return the injection name of the injection from one sort to another
-- This function is not implemented in a satisfactory way
getDefinedOp :: [SORT] -> SORT -> Term -> Term
getDefinedOp sorts s t =
    termAppl (con $ VName (getDefinedName sorts s) Nothing) t

-- | Return the term representing the injection of a term from one sort to
-- another. Note: the term is returned if both sorts are the same. This
-- function is not implemented in a satisfactory way.
mkInjection :: SORT -> SORT -> Term -> Term
mkInjection s s' t =
    let injName = getInjectionName s s'
        replace string c s1 = concat (map (\ x -> if x == c
                                                 then s1
                                                 else [x]) string)
        injOp = Const {
                  termName = VName {
                              new = "X_" ++ injName,
                              altSyn = Just (AltSyntax
                                             (replace injName '_' "'_"
                                              ++ "/'(_')") [3] 999)
                            },
                  termType = Hide {
                               typ = Type {
                                       typeId = "dummy",
                                       typeSort = [IsaClass "type"],
                                       typeArgs = []
                                     },
                               kon = NA,
                               arit = Nothing
                             }
                }
    in if s == s'
       then t
       else termAppl injOp t

-- | Return the list of string of all ga_embedding_injectivity axioms
-- produced by the translation CASL2PCFOL; CASL2SubCFOL.
getCollectionEmbInjAx :: [(SORT, SORT)] -> [String]
getCollectionEmbInjAx sortRel =
    let mkName (s, s') = transString $ mkEmbInjName s s'
    in map mkName sortRel

-- | Return the list of strings of all ga_notDefBottom axioms produced by
-- the translation CASL2PCFOL; CASL2SubCFOL.
getCollectionNotDefBotAx :: [SORT] -> [String]
getCollectionNotDefBotAx = map $ transString . mkNotDefBotAxiomName

-- | Return the list of strings of all the transitivity axioms names produced by
-- the translation CASL2PCFOL; CASL2SubCFOL.
getCollectionTransAx :: CASLSign.CASLSign -> [String]
getCollectionTransAx caslSign =
    let sorts = Set.toList $ CASLSign.sortSet caslSign
        allSupers s s' s'' =
            (Set.member s' $ CASLSign.supersortsOf s caslSign) &&
            (Set.member s'' $ CASLSign.supersortsOf s' caslSign) && (s /= s'')
    in [transString $ mkTransAxiomName s s' s''
            | s <- sorts, s' <- sorts, s'' <- sorts, allSupers s s' s'']

-- | Return the list of strings of all the identity axioms names produced by
-- the translation CASL2PCFOL; CASL2SubCFOL.
getCollectionIdentityAx :: CASLSign.CASLSign -> [String]
getCollectionIdentityAx caslSign =
    let sorts = Set.toList $ CASLSign.sortSet caslSign
        isomorphic s s' = (Set.member s $ CASLSign.supersortsOf s' caslSign) &&
                          (Set.member s' $ CASLSign.supersortsOf s caslSign)
    in [transString $ mkIdAxiomName s s'
            | s <- sorts, s' <- sorts, isomorphic s s']


-- | Return the list of string of all decomposition theorem names that we
-- generate. This function is not implemented in a satisfactory way
getColDecompositionThmName :: [(SORT, SORT)] -> [String]
getColDecompositionThmName sortRel =
    let tripples = [(s1, s2, s3) |
                    (s1, s2) <- sortRel, (s2', s3) <- sortRel, s2 == s2']
    in map getDecompositionThmName tripples

-- | Produce the theorem name of the decomposition theorem that we produce for a
-- gievn tripple of sorts.
getDecompositionThmName :: (SORT, SORT, SORT) -> String
getDecompositionThmName (s, s', s'') =
    "ccprover_decomposition_" ++ (convertSort2String s) ++ "_" ++ (convertSort2String s')
                    ++ "_" ++ (convertSort2String s'')

-- | Return the list of strings of the injectivity theorem names that we
-- generate.  This function is not implemented in a satisfactory way
getColInjectivityThmName :: [(SORT, SORT)] -> [String]
getColInjectivityThmName sortRel = map getInjectivityThmName sortRel

-- | Produce the theorem name of the injectivity theorem that we produce for a
-- gievn pair of sorts.
getInjectivityThmName :: (SORT, SORT) -> String
getInjectivityThmName (s, s') =
    "ccprover_injectivity_" ++ convertSort2String s ++ "_" ++ convertSort2String s'
