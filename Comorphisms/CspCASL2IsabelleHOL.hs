{- |
Module      :  $Header$
Description :  to be deleted soon
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The comorphism from CspCASL to Isabelle-HOL.
-}

module Comorphisms.CspCASL2IsabelleHOL (
   CspCASL2IsabelleHOL(..)
) where

import CASL.AS_Basic_CASL
import CASL.Sign (Symbol)
import CASL.Morphism (RawSymbol)
import qualified CASL.Inject as CASLInject
import qualified CASL.Sign as CASLSign
import Common.AS_Annotation
import Common.Result
import qualified Common.Lib.Rel as Rel
import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL
import Comorphisms.CFOL2IsabelleHOL(IsaTheory)
import CspCASL.AS_CspCASL_Process (PROCESS_NAME)
import CspCASL.Logic_CspCASL
import CspCASL.AS_CspCASL
import CspCASL.Trans_CspProver
import CspCASL.Trans_Consts
import CspCASL.SignCSP
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Isabelle.IsaConsts as IsaConsts
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Logic.Logic
import Logic.Comorphism

-- | The identity of the comorphism
data CspCASL2IsabelleHOL = CspCASL2IsabelleHOL deriving Show

instance Language CspCASL2IsabelleHOL where
  language_name CspCASL2IsabelleHOL = "CspCASL2Isabelle"

instance Comorphism CspCASL2IsabelleHOL
               CspCASL ()
               CspBasicSpec CspCASLSen SYMB_ITEMS SYMB_MAP_ITEMS
               CspCASLSign
               CspMorphism
               Symbol RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic CspCASL2IsabelleHOL = cspCASL
    sourceSublogic CspCASL2IsabelleHOL = ()
    targetLogic CspCASL2IsabelleHOL = Isabelle
    mapSublogic _cid _sl = Just ()

    map_theory CspCASL2IsabelleHOL = transCCTheory
    map_morphism = mapDefaultMorphism
    map_sentence CspCASL2IsabelleHOL sign = transCCSentence sign
    has_model_expansion CspCASL2IsabelleHOL = False
    is_weakly_amalgamable CspCASL2IsabelleHOL = False
    isInclusionComorphism CspCASL2IsabelleHOL = True

-- Functions for translating CspCasl theories and sentences to IsabelleHOL

-- | Translate CspCASL theories to Isabelle
transCCTheory :: (CspCASLSign, [Named CspCASLSen]) -> Result IsaTheory
transCCTheory ccTheory =
    let ccSign = fst ccTheory
        ccSens = snd ccTheory

        caslSign = ccSig2CASLSign ccSign
        cspSign = ccSig2CspSign ccSign

        casl2pcfol = (map_theory CASL2PCFOL.CASL2PCFOL)
        pcfol2cfol = (map_theory CASL2SubCFOL.defaultCASL2SubCFOL)
        cfol2isabelleHol = (map_theory CFOL2IsabelleHOL.CFOL2IsabelleHOL)
        sortList = Set.toList(CASLSign.sortSet caslSign)
        -- fakeType = Type {typeId = "Fake_Type" , typeSort = [], typeArgs =[]}
    in do -- Remove Subsorting from the CASL part of the CspCASL specification
          translation1 <- casl2pcfol (caslSign,[])
          -- Next Remove partial functions
          translation2 <- pcfol2cfol translation1
          -- Next Translate to IsabelleHOL code
          translation3 <- cfol2isabelleHol translation2
          -- Next add the preAlphabet construction to the IsabelleHOL code
          return $ addProcMap ccSens caslSign
                 $ addProcNameDatatype cspSign
                 $ addAllIntegrationTheorems sortList ccSign
                 $ addAllChooseFunctions sortList
                 $ addAllBarTypes sortList
                 $ addAlphabetType
                 $ addInstansanceOfEquiv
                 $ addJustificationTheorems ccSign (fst translation1)
                 $ addEqFun sortList
                 $ addAllCompareWithFun ccSign
                 $ addPreAlphabet sortList
                 $ addWarning
                 -- hack: show the casl sentences
                 --  addConst (show(ccSens)) fakeType
                 $ translation3

-- BUG This is not implemented in a sensible way yet and is not used
transCCSentence :: CspCASLSign -> CspCASLSen -> Result IsaSign.Sentence
transCCSentence _ (ProcessEq pn _ _ _) = do
  return (mkSen (Const (mkVName (show pn))
                                (Disp (Type "byeWorld" [] []) TFun Nothing)))
transCCSentence _ _ = do
  return (mkSen (Const (mkVName ("a"))
                                (Disp (Type "byeWorld" [] []) TFun Nothing)))

--------------------------------------------------------------------------
-- Functions for adding the process name datatype to an Isabelle theory --
--------------------------------------------------------------------------

-- | Add process name datatype which has a constructor for each
--   process name (along with the arguments for the process) in the
--   CspCASL Signature to an Isabelle theory
addProcNameDatatype  :: CspSign -> IsaTheory -> IsaTheory
addProcNameDatatype cspSign isaTh =
    let -- Create a list of pairs of process names and thier profiles
        procSetList = Map.toList (procSet cspSign)
        procNameDomainEntry = mkProcNameDE procSetList
    in updateDomainTab procNameDomainEntry isaTh


-- | Make a proccess name Domain Entry from ...
mkProcNameDE :: [(PROCESS_NAME, ProcProfile)] -> DomainEntry
mkProcNameDE processes =
    let -- The a list of pairs of constructors and their arguments
        constructors = map mk_cons processes
        -- Take a proccess name and its argument sorts (also its
        -- commAlpha - thrown away) and make a pair representing the
        -- constructor and the argument types
        mk_cons (procName, (ProcProfile sorts _)) =
            (mkVName (mkProcNameConstructor procName), map sortToTyp sorts)
        -- Turn a sort in to a Typ suitable for the domain entry The
        -- processes need to have arguments of the bar variants of
        -- the sorts not the original sorts
        sortToTyp sort = Type {typeId = mkSortBarString sort,
                               typeSort = [isaTerm],
                               typeArgs = []}
    in
    (procNameType, constructors)

-------------------------------------------------------------------------
-- Functions adding the process map fucntion to an Isabelle theory     --
-------------------------------------------------------------------------

-- | Add the fucction procMap to an Isabelle theory. This function
--   maps process names to real processes build using the same names
--   and the alphabet i.e., ProcName => (ProcName, Alphabet) proc. We
--   need to know the CspCASL sentences and the casl signature (data
--   part)
addProcMap :: [Named CspCASLSen] -> CASLSign.Sign () () -> IsaTheory ->
              IsaTheory
addProcMap namedSens caslSign isaTh =
    let
        -- Build new Isabelle theory with additional constant
        isaThWithConst = addConst procMapS  procMapType isaTh
        -- Get the plain sentences from the named senetences
        sens = map (\namedsen -> sentence namedsen) namedSens
        -- Filter so we only have proccess equations and no CASL senetences
        processEqs = filter isProcessEq sens
        -- the term representing the procMap that tajes a term as a
        -- parameter
        procMapTerm = termAppl (conDouble procMapS)
        -- Make a single equation for the primrec from a process equation
        -- BUG HERE - this next part is not right - underscore is bad
        mkEq (ProcessEq procName _ _ proc) =
            let -- Make the name (string) for this process
                procNameString = convertProcessName2String procName
                -- Change the name to a term
                procNameTerm = conDouble procNameString
                -- Turn the list of variables into a list of Isabelle
                -- free variables
                varTerms = [] -- BUG - should be somehting like map (\x -> mkFree (show x)) vars
                 -- Make a lhs term built of termAppl applied to the
                 -- proccess name and the variables
                lhs = procMapTerm (foldl termAppl (procNameTerm) varTerms)
                rhs = transProcess caslSign proc
             in binEq lhs rhs
        -- Build equations for primrec using process equations
        eqs = map mkEq processEqs
    in addPrimRec eqs isaThWithConst

-------------------------------------------------------------------------
-- Functions for adding the PreAlphabet datatype to an Isabelle theory --
-------------------------------------------------------------------------

-- | Add the PreAlphabet (built from a list of sorts) to an Isabelle theory
addPreAlphabet :: [SORT] -> IsaTheory -> IsaTheory
addPreAlphabet sortList isaTh =
    let preAlphabetDomainEntry = mkPreAlphabetDE sortList
    in updateDomainTab preAlphabetDomainEntry isaTh

-- | Make a PreAlphabet Domain Entry from a list of sorts
mkPreAlphabetDE :: [SORT] -> DomainEntry
mkPreAlphabetDE sorts =
    (Type {typeId = preAlphabetS, typeSort = [isaTerm], typeArgs = []},
         map (\sort ->
                  (mkVName (mkPreAlphabetConstructor sort),
                               [Type {typeId = convertSort2String sort,
                                      typeSort = [isaTerm],
                                      typeArgs = []}])
             ) sorts
    )

----------------------------------------------------------------
-- Functions for adding the eq functions and the compare_with --
-- functions to an Isabelle theory                            --
----------------------------------------------------------------

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
--   Isabelle theory. We need to know about the casl signature so that
--   we can pass it on to the addCompareWithFun function
addAllCompareWithFun :: CspCASLSign -> IsaTheory -> IsaTheory
addAllCompareWithFun ccSign isaTh =
    let sortList = Set.toList(CASLSign.sortSet ccSign)
    in  foldl (addCompareWithFun ccSign) isaTh sortList

-- | Add a single compare_with function for a given sort to an
--   Isabelle theory.  We need to know about the casl signature to
--   work out the RHS of the equations.
addCompareWithFun :: CspCASLSign -> IsaTheory -> SORT -> IsaTheory
addCompareWithFun ccSign isaTh sort =
    let sortList = Set.toList(CASLSign.sortSet ccSign)
        sortType = Type {typeId = convertSort2String sort, typeSort = [],
                                  typeArgs =[]}
        funName = mkCompareWithFunName sort
        funType = mkFunType sortType $ mkFunType preAlphabetType boolType
        isaThWithConst = addConst funName funType isaTh
        sortSuperSet = CASLSign.supersortsOf sort ccSign
        mkEq sort' =
            let x = mkFree "x"
                y = mkFree "y"
                sort'Constructor = mkPreAlphabetConstructor sort'
                lhs = termAppl lhs_a lhs_b
                lhs_a = termAppl (conDouble funName) x
                lhs_b = termAppl (conDouble (sort'Constructor)) y
                sort'SuperSet =CASLSign.supersortsOf sort' ccSign
                commonSuperList = Set.toList (Set.intersection
                                                 sortSuperSet
                                                 sort'SuperSet)

                -- If there are no tests then the rhs=false else
                -- combine all tests using binConj
                rhs = if (null allTests)
                      then false
                      else foldr1 binConj allTests

                -- The tests produce a list of equations for each test
                -- Test 1 =  test equality at: current sort vs current sort
                -- Test 2 =  test equality at: current sort vs super sorts
                -- Test 3 =  test equality at: super sorts  vs current sort
                -- Test 4 =  test equality at: super sorts  vs super sorts
                allTests = concat [test1, test2, test3, test4]
                test1 = if (sort == sort') then [binEq x y] else []
                test2 = if (Set.member sort sort'SuperSet)
                        then [binEq x (mkInjection sort' sort y)]
                        else []
                test3 = if (Set.member sort' sortSuperSet)
                        then [binEq (mkInjection sort sort' x) y]
                        else []
                test4 = if (null commonSuperList)
                        then []
                        else map test4_atSort commonSuperList
                test4_atSort s = binEq (mkInjection sort  s x)
                                       (mkInjection sort' s y)
            in binEq lhs rhs
        eqs = map mkEq sortList
    in  addPrimRec eqs isaThWithConst

--------------------------------------------------------
-- Functions for producing the Justification theorems --
--------------------------------------------------------

-- | Add all justification theorems to an Isabelle Theory. We need to
--   the CspCASL signature and the PFOL Signature to pass it on. We
--   could recalculate the PFOL signature from the CspCASL signature
--   here, but we dont as it can be passed in.
addJustificationTheorems :: CspCASLSign -> CASLSign.CASLSign ->
                            IsaTheory -> IsaTheory
addJustificationTheorems ccSign pfolSign isaTh =
    let sortRel = Rel.toList(CASLSign.sortRel ccSign)
        sorts = Set.toList(CASLSign.sortSet ccSign)
    in   addTransitivityTheorem sorts sortRel
       $ addAllInjectivityTheorems pfolSign sorts sortRel
       $ addAllDecompositionTheorem pfolSign sorts sortRel
       $ addSymmetryTheorem sorts
       $ addReflexivityTheorem
       $ isaTh

-- | Add the reflexivity theorem and proof to an Isabelle Theory
addReflexivityTheorem :: IsaTheory -> IsaTheory
addReflexivityTheorem isaTh =
    let name = reflexivityTheoremS
        x = mkFree "x"
        thmConds = []
        thmConcl = binEq_PreAlphabet x x
        proof' = IsaProof {
                   proof = [Apply (Induct x),
                            Apply Auto],
                   end = Done
                 }
    in addThreomWithProof name thmConds thmConcl proof' isaTh

-- | Add the symmetry theorem and proof to an Isabelle Theory We need
--   to know the number of sorts, but instead we are given a list of
--   all sorts
addSymmetryTheorem :: [SORT] -> IsaTheory -> IsaTheory
addSymmetryTheorem sorts isaTh =
    let numSorts = length(sorts)
        name = symmetryTheoremS
        x = mkFree "x"
        y = mkFree "y"
        thmConds = [binEq_PreAlphabet x y]
        thmConcl = binEq_PreAlphabet y x
        inductY = concat $ map (\i -> [Prefer (i*numSorts+1),
                                       Apply (Induct y)])
                    [0..(numSorts-1)]
        proof' = IsaProof {
                   proof = [Apply (Induct x)] ++ inductY ++ [Apply Auto],
                   end = Done
                 }
    in addThreomWithProof name thmConds thmConcl proof' isaTh

-- | Add all the injectivity theorems and proofs
addAllInjectivityTheorems :: CASLSign.CASLSign -> [SORT] -> [(SORT,SORT)] ->
                             IsaTheory -> IsaTheory
addAllInjectivityTheorems pfolSign sorts sortRel isaTh =
    foldl (addInjectivityTheorem pfolSign sorts sortRel) isaTh sortRel

-- | Add the injectivity theorem and proof which should be deduced
--   from the embedding_Injectivity axioms from the translation
--   CASL2PCFOL; CASL2SubCFOL for a single injection represented as a
--   pair of sorts. As a work around, we need to know all sorts to
--   pass them on
addInjectivityTheorem :: CASLSign.CASLSign -> [SORT] -> [(SORT,SORT)] ->
                         IsaTheory -> (SORT,SORT) -> IsaTheory
addInjectivityTheorem pfolSign sorts sortRel isaTh (s1,s2) =
    let x = mkFree "x"
        y = mkFree "y"
        injX = mkInjection s1 s2 x
        injY = mkInjection s1 s2 y
        definedOp_s1 = getDefinedOp sorts s1
        definedOp_s2 = getDefinedOp sorts s2
        collectionEmbInjAx = getCollectionEmbInjAx sortRel
        collectionTotAx = getCollectionTotAx pfolSign
        collectionNotDefBotAx = getCollectionNotDefBotAx sorts
        name = getInjectivityThmName(s1, s2)
        conds = [binEq injX injY]
        concl = binEq x y
        proof' = IsaProof [Apply(CaseTac (definedOp_s2 injX)),
                           -- Case 1
                           Apply(SubgoalTac(definedOp_s1 x)),
                           Apply(SubgoalTac(definedOp_s1 y)),
                           Apply(Insert collectionEmbInjAx),
                           Apply(Simp),
                           Apply(SimpAdd Nothing collectionTotAx),
                           Apply(SimpAdd (Just No_asm_use) collectionTotAx),
                           -- Case 2
                           Apply(SubgoalTac(termAppl notOp (definedOp_s1 x))),
                           Apply(SubgoalTac(termAppl notOp(definedOp_s1 y))),
                           Apply(SimpAdd Nothing collectionNotDefBotAx),
                           Apply(SimpAdd Nothing collectionTotAx),
                           Apply(SimpAdd (Just No_asm_use) collectionTotAx)]
                           Done
    in addThreomWithProof name conds concl proof' isaTh

-- | Add all the decoposition theorems and proofs
addAllDecompositionTheorem :: CASLSign.CASLSign -> [SORT] -> [(SORT,SORT)] ->
                             IsaTheory -> IsaTheory
addAllDecompositionTheorem pfolSign sorts sortRel isaTh =
    let tripples = [(s1,s2,s3) |
                    (s1,s2) <- sortRel, (s2',s3) <- sortRel, s2==s2']
    in foldl (addDecompositionTheorem pfolSign sorts sortRel) isaTh tripples

-- | Add the decomposition theorem and proof which should be deduced
--   from the transitivity axioms from the translation CASL2PCFOL;
--   CASL2SubCFOL for a pair of injections represented as a tripple of
--   sorts. e.g. (S,T,U) means produce the lemma and proof for
--   inj_T_U(inj_S_T(x)) = inj_S_U(x). As a work around, we need to
--   know all sorts to pass them on.
addDecompositionTheorem :: CASLSign.CASLSign -> [SORT] -> [(SORT,SORT)] ->
                         IsaTheory -> (SORT,SORT,SORT) -> IsaTheory
addDecompositionTheorem pfolSign sorts sortRel isaTh (s1,s2,s3) =
    let x = mkFree "x"
        -- These 5 lines make use of currying
        injOp_s1_s2 = mkInjection s1 s2
        injOp_s2_s3 = mkInjection s2 s3
        injOp_s1_s3 = mkInjection s1 s3
        inj_s1_s2_s3_x = injOp_s2_s3 (injOp_s1_s2 x)
        inj_s1_s3_x = injOp_s1_s3 x

        definedOp_s1 = getDefinedOp sorts s1
        definedOp_s3 = getDefinedOp sorts s3
        collectionTransAx = getCollectionTransAx sortRel
        collectionTotAx = getCollectionTotAx pfolSign
        collectionNotDefBotAx = getCollectionNotDefBotAx sorts

        name = getDecompositionThmName(s1, s2, s3)
        conds = []
        concl = binEq inj_s1_s2_s3_x inj_s1_s3_x

        proof' = IsaProof [Apply(CaseTac (definedOp_s3 inj_s1_s2_s3_x)),
                           -- Case 1
                           Apply(SubgoalTac(definedOp_s1 x)),
                           Apply(Insert collectionTransAx),
                           Apply(Simp),
                           Apply(SimpAdd Nothing collectionTotAx),

                           -- Case 2
                           Apply(SubgoalTac(
                               termAppl notOp(definedOp_s3 inj_s1_s3_x))),
                           Apply(SimpAdd Nothing collectionNotDefBotAx),
                           Apply(SimpAdd Nothing collectionTotAx)]
                           Done
    in addThreomWithProof name conds concl proof' isaTh


-- | Add the transitivity theorem and proof to an Isabelle Theory. We
--   need to know the number of sorts to know how much induction to
--   perfom and also the sub-sort relation to build the collection of
--   injectivity theorem names
addTransitivityTheorem :: [SORT] -> [(SORT,SORT)] -> IsaTheory -> IsaTheory
addTransitivityTheorem sorts sortRel isaTh =
    let colInjThmNames = getColInjectivityThmName sortRel
        colDecompThmNames = getColDecompositionThmName sortRel
        numSorts = length(sorts)
        name = transitivityS
        x = mkFree "x"
        y = mkFree "y"
        z = mkFree "z"
        thmConds = [binEq_PreAlphabet x y, binEq_PreAlphabet y z]
        thmConcl = binEq_PreAlphabet x z
        inductY = concat $ map (\i -> [Prefer (i*numSorts+1),
                                       Apply (Induct y)])
                  [0..(numSorts-1)]
        inductZ = concat $ map (\i -> [Prefer (i*numSorts+1),
                                       Apply (Induct z)])
                  [0..((numSorts^(2::Int))-1)]
        proof' = IsaProof {
                   proof = [Apply (Induct x)] ++
                            inductY ++
                            inductZ ++
                           [Apply (AutoSimpAdd Nothing
                                  (colDecompThmNames ++ colInjThmNames))],
                   end = Done
                 }
    in addThreomWithProof name thmConds thmConcl proof' isaTh

--------------------------------------------------------------
-- Functions for producing instances of equivalence classes --
--------------------------------------------------------------

-- | Function to add preAlphabet as an equivalence relation to an
--   Isabelle theory
addInstansanceOfEquiv :: IsaTheory  -> IsaTheory
addInstansanceOfEquiv  isaTh =
    let eqvSort = [IsaClass eqvTypeClassS]
        eqvProof = IsaProof []  (By (Other "intro_classes"))
        equivSort = [IsaClass equivTypeClassS]
        equivProof = IsaProof [Apply (Other "intro_classes"),
                               Apply (Other ("unfold " ++ preAlphabetSimS
                                             ++ "_def")),
                               Apply (Other ("rule " ++ reflexivityTheoremS)),
                               Apply (Other ("rule " ++ transitivityS
                                                ++", auto")),
                               Apply (Other ("rule " ++ symmetryTheoremS
                                                ++ ", simp"))]
                               Done
        x = mkFree "x"
        y = mkFree "y"
        defLhs = binEqvSim x y
        defRhs = binEq_PreAlphabet x y
    in   addInstanceOf preAlphabetS [] equivSort equivProof
       $ addDef preAlphabetSimS defLhs defRhs
       $ addInstanceOf preAlphabetS [] eqvSort eqvProof
       $ isaTh

-------------------------------------------------------------
-- Functions for producing the alphabet type and bar types --
-------------------------------------------------------------

-- | Function to add the Alphabet type (type synonym) to an Isabelle theory
addAlphabetType :: IsaTheory -> IsaTheory
addAlphabetType  isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sign_tsig = tsig isaTh_sign
        myabbrs = abbrs isaTh_sign_tsig
        abbrsNew = Map.insert alphabetS ([], preAlphabetQuotType) myabbrs

        isaTh_sign_updated = isaTh_sign {
                               tsig = (isaTh_sign_tsig {abbrs =abbrsNew})
                             }
    in (isaTh_sign_updated, snd isaTh)

-- | Function to add all the bar types to an Isabelle theory.
addAllBarTypes :: [SORT] -> IsaTheory -> IsaTheory
addAllBarTypes sorts isaTh = foldl addBarType isaTh sorts

-- | Function to add the bar types of a sort to an Isabelle theory.
addBarType :: IsaTheory -> SORT -> IsaTheory
addBarType isaTh sort =
    let sortBarString = mkSortBarString sort
        barType = Type {typeId = sortBarString, typeSort = [], typeArgs =[]}
        isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        x = mkFree "x"
        y = mkFree "y"
        rhs = termAppl (conDouble (mkPreAlphabetConstructor sort)) y
        bin_eq = binEq x $ termAppl (conDouble classS ) rhs
        exist_eq =termAppl (conDouble exS) (Abs y bin_eq NotCont)
        subset = SubSet x alphabetType exist_eq
        sen = TypeDef barType subset (IsaProof [] (By Auto))
        namedSen = (makeNamed sortBarString sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- | Add all choose functions for a given list of sorts to an Isabelle
--   theory.
addAllChooseFunctions :: [SORT] -> IsaTheory -> IsaTheory
addAllChooseFunctions sorts isaTh =
    let isaTh' = foldl addChooseFunction isaTh sorts --add function and def
    in foldl addChooseFunctionLemma isaTh' sorts --add theorem and proof

-- | Add a single choose function for a given sort to an Isabelle
--   theory.  The following Isabelle code is produced by this function:
--   consts choose_Nat :: "Alphabet => Nat"
--   defs choose_Nat_def: "choose_Nat x == contents{y . class(C_Nat y) = x}"
addChooseFunction ::  IsaTheory -> SORT -> IsaTheory
addChooseFunction isaTh sort =
    let --constant
        sortType = Type {typeId = convertSort2String sort,
                         typeSort = [],
                         typeArgs =[]}
        chooseFunName = mkChooseFunName sort
        chooseFunType = mkFunType alphabetType sortType
        -- definition
        x = mkFree "x"
        y = mkFree "y"
        contentsOp = termAppl (conDouble "contents")
        chooseOp = termAppl (conDouble chooseFunName)
        sortConsOp = termAppl (conDouble (mkPreAlphabetConstructor sort))
        bin_eq = binEq (classOp $ sortConsOp y) x
        subset = SubSet y sortType bin_eq
        lhs = chooseOp x
        rhs = contentsOp (Set subset)
    in  addDef chooseFunName lhs rhs -- Add defintion to theory
      $ addConst chooseFunName chooseFunType isaTh -- Add constant to theory

-- | Add a single choose function lemma for a given sort to an
--   Isabelle theory.  The following Isabelle code is produced by this
--   function: lemma "choose_Nat (class (C_Nat x)) = x". The proof is
--   also produced.

addChooseFunctionLemma ::  IsaTheory -> SORT -> IsaTheory
addChooseFunctionLemma isaTh sort =
    let sortType = Type {typeId = convertSort2String sort,
                         typeSort = [],
                         typeArgs =[]}
        chooseFunName = mkChooseFunName sort
        x = mkFree "x"
        y = mkFree "y"
        chooseOp = termAppl (conDouble chooseFunName)
        sortConsOp = termAppl (conDouble (mkPreAlphabetConstructor sort))
        -- theorm
        subgoalTacTermLhsBinEq = binEq (classOp $ sortConsOp y)
                                       (classOp $ sortConsOp x)
        subgoalTacTermLhs = Set $ SubSet y sortType subgoalTacTermLhsBinEq
        subgoalTacTermRhs = Set $ FixedSet [x]
        subgoalTacTerm = binEq subgoalTacTermLhs subgoalTacTermRhs
        thmConds = []
        thmConcl = binEq (chooseOp $ classOp $ sortConsOp x) x
        proof' = IsaProof [Apply (Other ("unfold " ++ chooseFunName ++ "_def")),
                           Apply (SubgoalTac subgoalTacTerm),
                           Apply(Simp),
                           Apply(SimpAdd Nothing [quotEqualityS]),
                           Apply(Other ("unfold "++ preAlphabetSimS
                                           ++ "_def")),
                           Apply(Auto)]
                           Done
    in  addThreomWithProof chooseFunName thmConds thmConcl proof' isaTh

------------------------------------------------------
-- Functions for producing the integration theorems --
------------------------------------------------------

-- | Add all the integration theorems. We need to know all the sorts
--   to produce all the theorems.
addAllIntegrationTheorems :: [SORT] -> CspCASLSign -> IsaTheory -> IsaTheory
addAllIntegrationTheorems sorts ccSign isaTh =
    let pairs = [(s1,s2) | s1 <- sorts, s2 <- sorts]
    in foldl (addIntegrationTheorem_A ccSign) isaTh pairs

-- | Add Integration theorem A -- Compare to elements of the Alphabet.
--   We add the integration theorem based on the sorts of both
--   elements of the alphabet. We need to know the subsort relation to
--   find the highest common sort, but we pass in the CC signature for
--   use in function calls.
addIntegrationTheorem_A :: CspCASLSign -> IsaTheory -> (SORT,SORT) -> IsaTheory
addIntegrationTheorem_A ccSign isaTh (s1,s2) =
    let sortRel = Rel.toList(CASLSign.sortRel ccSign)
        s1SuperSet = CASLSign.supersortsOf s1 ccSign
        s2SuperSet = CASLSign.supersortsOf s2 ccSign
        commonSuperList = Set.toList (Set.intersection
                                         (Set.insert s1 s1SuperSet)
                                         (Set.insert s2 s2SuperSet))
        x = mkFree "x"
        y = mkFree "y"
        s1ConsOp = termAppl (conDouble (mkPreAlphabetConstructor s1))
        s2ConsOp = termAppl (conDouble (mkPreAlphabetConstructor s2))
        rhs = binEq (classOp $ s1ConsOp x) (classOp $ s2ConsOp y)
        lhs = if (null commonSuperList)
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
        proof' = IsaProof [Apply (SimpAdd Nothing ["quot_equality"]),
                           Apply (Other ("unfold " ++ preAlphabetSimS
                                             ++ "_def")),
                           Apply (AutoSimpAdd Nothing
                                  (colDecompThmNames ++ colInjThmNames))]
                           Done
    in  addThreomWithProof "IntegrationTheorem_A" thmConds thmConcl proof' isaTh

----------------------------------------------
-- Function to help keep strings consistent --
----------------------------------------------

-- | String of the name of the function to compare eqaulity of two
--   elements of the PreAlphabet
eq_PreAlphabetS :: String
eq_PreAlphabetS = "eq_PreAlphabet"

eq_PreAlphabetV :: VName
eq_PreAlphabetV   = VName eq_PreAlphabetS $ Nothing

binEq_PreAlphabet :: Term -> Term -> Term
binEq_PreAlphabet = binVNameAppl eq_PreAlphabetV


quotEqualityS :: String
quotEqualityS = "quot_equality"

reflexivityTheoremS :: String
reflexivityTheoremS = "eq_refl"

symmetryTheoremS :: String
symmetryTheoremS = "eq_symm"

transitivityS :: String
transitivityS = "eq_trans"

preAlphabetSimS :: String
preAlphabetSimS = "preAlphabet_sim"

-- | String for the name of the axiomatic type class of equivalence
-- | relations part 1
eqvTypeClassS :: String
eqvTypeClassS  = "eqv"

-- | String for the name of the axiomatic type class of equivalence
-- | relations part 2
equivTypeClassS :: String
equivTypeClassS  = "equiv"

-- | Return the term representing the injection of a term from one sort to another
--   note: the term is returned if both sorts are the same
--   This function is not implemented in a satisfactory way
mkInjection :: SORT -> SORT -> Term -> Term
mkInjection s s' t =
    let injName = getInjectionName s s'
        replace string c s1 = concat (map (\x -> if x==c
                                                 then s1
                                                 else [x]) string)
        injOp = Const {
                  termName= VName {
                              new = ("X_" ++ injName),
                              altSyn = Just (AltSyntax ((replace injName '_' "'_")
                                                        ++ "/'(_')") [3] 999)
                            },
                  termType = Hide {
                               typ = Type {
                                       typeId ="dummy",
                                       typeSort = [IsaClass "type"],
                                       typeArgs = []
                                     },
                               kon = NA,
                               arit= Nothing
                             }
                }
    in if s == s'
       then t
       else termAppl injOp t

-- | Return the name of the injection as it is used in the alternative
--   syntax of the injection from one sort to another.
--   This function is not implemented in a satisfactory way
getInjectionName :: SORT -> SORT -> String
getInjectionName s s' =
    let t = CASLSign.toOP_TYPE(CASLSign.OpType{CASLSign.opKind = Total,
                                               CASLSign.opArgs = [s],
                                               CASLSign.opRes = s'})
        injName = show $ CASLInject.uniqueInjName t
    in injName

-- | Return the injection name of the injection from one sort to another
--   This function is not implemented in a satisfactory way
getDefinedOp :: [SORT] -> SORT -> Term -> Term
getDefinedOp sorts s t =
    termAppl (con $ VName (getDefinedName sorts s) $ Nothing) t

-- | Return the name of the definedness function for a sort.  We need
--   to know all sorts to perform this workaround
--   This function is not implemented in a satisfactory way
getDefinedName :: [SORT] -> SORT -> String
getDefinedName sorts s =
    let index = List.elemIndex s sorts
        str = case index of
                Nothing -> ""
                Just i -> show (i + 1)
    in "gn_definedX" ++ str

-- Produce the theorem name of the decomposition theorem that we produce
getDecompositionThmName :: (SORT,SORT,SORT) -> String
getDecompositionThmName (s, s', s'') =
    "decomposition_" ++ (convertSort2String s) ++ "_" ++ (convertSort2String s')
                    ++ "_" ++ (convertSort2String s'')

-- This function is not implemented in a satisfactory way
-- Return the list of string of all decomposition theorem names that we generate
getColDecompositionThmName :: [(SORT,SORT)] -> [String]
getColDecompositionThmName sortRel =
    let tripples = [(s1,s2,s3) |
                    (s1,s2) <- sortRel, (s2',s3) <- sortRel, s2==s2']
    in map getDecompositionThmName tripples

-- Produce the theorem name of the injectivity theorem that we produce
getInjectivityThmName :: (SORT,SORT) -> String
getInjectivityThmName (s, s') =
    "injectivity_" ++ (convertSort2String s) ++ "_" ++ (convertSort2String s')

-- This function is not implemented in a satisfactory way
-- Return the list of strings of the injectivity theorem names
-- that we generate
getColInjectivityThmName :: [(SORT,SORT)] -> [String]
getColInjectivityThmName sortRel = map getInjectivityThmName sortRel

-- This function is not implemented in a satisfactory way. Return the
-- list of strings of all transitivity axioms produced by the
-- translation CASL2PCFOL; CASL2SubCFOL
getCollectionTransAx :: [(SORT,SORT)] -> [String]
getCollectionTransAx sortRel =
    let tripples = [(s1,s2,s3) |
                    (s1,s2) <- sortRel, (s2',s3) <- sortRel, s2==s2']
        mkEmbInjAxName = (\i -> "ga_transitivity"
                                ++ (if (i==0)
                                    then ""
                                    else ("_" ++ show i))
                         )
    in  map mkEmbInjAxName [0 .. (length(tripples) - 1)]

-- This function is not implemented in a satisfactory way. Return the
-- list of string of all embedding_injectivity axioms produced by the
-- translation CASL2PCFOL; CASL2SubCFOL
getCollectionEmbInjAx :: [(SORT,SORT)] -> [String]
getCollectionEmbInjAx sortRel =
    let mkEmbInjAxName = (\i -> "ga_embedding_injectivity"
                                ++ (if (i==0)
                                    then ""
                                    else ("_" ++ show i))
                         )
    in map mkEmbInjAxName [0 .. (length(sortRel) - 1)]

-- | Return the list of strings of all gn_totality axiom names. This
--   function is not implemented in a satisfactory way.
getCollectionTotAx :: CASLSign.CASLSign -> [String]
getCollectionTotAx pfolSign =
    let opList = Map.toList $ CASLSign.opMap pfolSign
        -- This filter is not quite right
        totFilter (_,setOpType) = let listOpType = Set.toList setOpType
                                 in CASLSign.opKind (head listOpType) == Total
        totList = filter totFilter opList

        mkTotAxName = (\i -> "ga_totality"
                             ++ (if (i==0)
                                 then ""
                                 else ("_" ++ show i))
                      )
    in map mkTotAxName [0 .. (length(totList) - 1)]

-- This function is not implemented in a satisfactory way
-- Return the list of strings of all ga_notDefBottom axioms
getCollectionNotDefBotAx :: [SORT] -> [String]
getCollectionNotDefBotAx sorts =
    let mkNotDefBotAxName = (\i -> "ga_notDefBottom"
                                   ++ (if (i==0)
                                       then ""
                                       else ("_" ++ show i)))
    in map mkNotDefBotAxName [0 .. (length(sorts) - 1)]

-- Function that returns the constructor of PreAlphabet for a given
mkPreAlphabetConstructor :: SORT -> String
mkPreAlphabetConstructor sort = "C_" ++ (convertSort2String sort)

mkProcNameConstructor :: PROCESS_NAME -> String
mkProcNameConstructor pn = show pn

-- Function that takes a sort and outputs a the function name for the
-- corresponing compare_with function
mkCompareWithFunName :: SORT -> String
mkCompareWithFunName sort = ("compare_with_" ++ (mkPreAlphabetConstructor sort))

-- Function that takes a sort and outputs a the function name for the
-- corresponing choose function
mkChooseFunName :: SORT -> String
mkChooseFunName sort = ("choose_" ++ (mkPreAlphabetConstructor sort))



-- Converts a SORT in to the corresponding bar sort represented as a
-- string
mkSortBarString :: SORT -> String
mkSortBarString s = convertSort2String s ++ barExtS
---------------------------------------------------
-- Functions for manipulating an Isabelle theory --
---------------------------------------------------

-- Add a single constant to the signature of an Isabelle theory
addConst :: String -> Typ -> IsaTheory -> IsaTheory
addConst cName cType isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        isaTh_sign_ConstTab = constTab isaTh_sign
        isaTh_sign_ConstTabUpdated =
            Map.insert (mkVName cName) cType isaTh_sign_ConstTab
        isaTh_sign_updated = isaTh_sign {constTab = isaTh_sign_ConstTabUpdated}
    in (isaTh_sign_updated, isaTh_sen)

-- Add a primrec defintion to the sentences of an Isabelle theory
addPrimRec :: [Term] -> IsaTheory -> IsaTheory
addPrimRec terms isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        recDef = RecDef {keyWord = primrecS, senTerms = [terms]}
        namedRecDef = (makeNamed "what_does_this_word_do?" recDef) {
                        isAxiom = False,
                        isDef = True}
    in (isaTh_sign, isaTh_sen ++ [namedRecDef])

-- Add a DomainEntry to the domain tab of a signature of an Isabelle Theory
updateDomainTab :: DomainEntry  -> IsaTheory -> IsaTheory
updateDomainTab domEnt isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        isaTh_sign_domTab = domainTab isaTh_sign
        isaTh_sign_updated = isaTh_sign {domainTab = (isaTh_sign_domTab
                                                      ++ [[domEnt]])}
    in (isaTh_sign_updated, isaTh_sen)

-- Add a theorem with proof to an Isabelle theory
addThreomWithProof :: String -> [Term] -> Term -> IsaProof -> IsaTheory ->
                      IsaTheory
addThreomWithProof name conds concl proof' isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = if (null conds)
              then ((mkSen concl) {thmProof = Just proof'})
              else ((mkCond conds concl) {thmProof = Just proof'})
        namedSen = (makeNamed name sen) {isAxiom = False}
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- Function to add an instance of command to an Isabelle theory
addInstanceOf :: String -> [Sort] -> Sort -> IsaProof -> IsaTheory -> IsaTheory
addInstanceOf name args res pr isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = Instance name args res pr
        namedSen = (makeNamed name sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- Function to add a def command to an Isabelle theory
addDef :: String -> Term -> Term -> IsaTheory -> IsaTheory
addDef name lhs rhs isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = ConstDef (IsaEq lhs rhs)
        namedSen = (makeNamed name sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])

----------------------------------
-- Code below this line is junk --
----------------------------------

-- Add a warning to an Isabelle theory
addWarning :: IsaTheory -> IsaTheory
addWarning isaTh =
    let fakeType = Type {typeId = "Fake_Type" , typeSort = [], typeArgs =[]}
    in addConst "Warning_this_is_not_a_stable_or_meaningful_translation"
       fakeType isaTh

-- Add a string version of the abstract syntax of an Isabelle theory to itself
{-
addDebug :: IsaTheory -> IsaTheory
addDebug isaTh =
    let isaTh_sign = fst(isaTh)
        isaTh_sens = snd(isaTh)
        sensType = Type {typeId = show isaTh_sens , typeSort = [], typeArgs =[]}
        signType = Type {typeId = show isaTh_sign , typeSort = [], typeArgs =[]}
    in   addConst "debug_isaTh_sens" sensType
       $ addConst "debug_isaTh_sign" signType
       $ isaTh
-}
