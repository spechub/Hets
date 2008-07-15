{- |
Module      :  $Header$
Description :  embedding from CspCASL to Isabelle-HOL
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach, Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The comorphism from CspCASL to Isabelle-HOL.
-}

module Comorphisms.CspCASL2IsabelleHOL where

import CASL.AS_Basic_CASL
import qualified CASL.Inject as CASLInject
import qualified CASL.Sign as CASLSign
import Common.AS_Annotation
import Common.Result
import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL
import Comorphisms.CFOL2IsabelleHOL(IsaTheory)
import CspCASL.Logic_CspCASL
import CspCASL.AS_CspCASL
import CspCASL.SignCSP
import qualified Data.Set as Set
import qualified Data.Map as Map
import Isabelle.IsaConsts as IsaConsts
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaProof
import Isabelle.Logic_Isabelle
import Logic.Logic
import Logic.Comorphism

-- | The identity of the comorphism
data CspCASL2IsabelleHOL = CspCASL2IsabelleHOL deriving (Show)

instance Language CspCASL2IsabelleHOL -- default definition is okay

instance Comorphism CspCASL2IsabelleHOL
               CspCASL ()
               CspBasicSpec CspCASLSentence SYMB_ITEMS SYMB_MAP_ITEMS
               CspCASLSign
               CspMorphism
               () () ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic CspCASL2IsabelleHOL = CspCASL
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

transCCTheory :: (CspCASLSign, [Named CspCASLSentence]) -> Result IsaTheory
transCCTheory ccTheory =
    let ccSign = fst ccTheory
        -- ccSens = snd ccTheory
        caslSign = ccSig2CASLSign ccSign
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
          -- Next add the preAlpabet construction to the IsabelleHOL code
          return $ addInstansanceOfEquiv
                 $ addJustificationTheorems sortList
                 $ addEqFun sortList
                 $ addManyCompareWithFun ccSign
                 $ addPreAlphabet sortList
                 $ addWarning
                 $ translation3

-- This is not implemented in a sensible way yet
transCCSentence :: CspCASLSign -> CspCASLSentence -> Result IsaSign.Sentence
transCCSentence _ s =
    do return (mkSen (Const (mkVName (show s)) (Disp (Type "byeWorld" [] []) TFun Nothing)))

-- Functions for adding the PreAlphabet datatype to an Isabelle theory

-- Add the PreAlphabet (built from a list of sorts) to an Isabelle theory
addPreAlphabet :: [SORT] -> IsaTheory -> IsaTheory
addPreAlphabet sortList isaTh =
    let preAlphabetDomainEntry = mkPreAlphabetDE sortList
    in updateDomainTab preAlphabetDomainEntry isaTh

-- Make a PreAlphabet Domain Entry from a list of sorts
mkPreAlphabetDE :: [SORT] -> DomainEntry
mkPreAlphabetDE sorts =
    (Type {typeId = preAlphabetS, typeSort = [isaTerm], typeArgs = []},
         map (\sort ->
                  (mkVName (mkPreAlphabetConstructor sort), [Type {typeId = convertSort2String sort,
                                                                       typeSort = [isaTerm],
                                                                       typeArgs = []}])
             ) sorts
    )

-- Functions for adding the eq functions and the compare_with functions to an Isabelle theory

-- Adds the eq function to an Isabelle theory using a list of sorts
addEqFun :: [SORT] -> IsaTheory -> IsaTheory
addEqFun sortList isaTh =
    let preAlphabetType = Type {typeId = preAlphabetS , typeSort = [], typeArgs =[]}
        eqtype = mkFunType preAlphabetType $ mkFunType preAlphabetType boolType
        isaThWithConst = addConst eqS eqtype isaTh
        mkEq sort =
            let x = mkFree "x"
                lhs = termAppl (conDouble eqS) (termAppl (conDouble (mkPreAlphabetConstructor sort)) x)
                rhs = termAppl (conDouble (mkCompareWithFunName sort)) x
            in binEq lhs rhs
        eqs = map mkEq sortList
    in addPrimRec eqs isaThWithConst

-- Add many compare_with functions for a given list sorts to an Isabelle theory
-- We need to know about the casl signature to pass to the addCompareWithFun function
addManyCompareWithFun :: CspCASLSign -> IsaTheory -> IsaTheory
addManyCompareWithFun ccSign isaTh =
    let sortList = Set.toList(CASLSign.sortSet ccSign)
    in  foldl (addCompareWithFun ccSign) isaTh sortList

-- Add a single compare_with function for a given sort to an Isabelle theory
-- We need to know about the casl signature to work out the RHS of the equations
addCompareWithFun :: CspCASLSign -> IsaTheory -> SORT -> IsaTheory
addCompareWithFun ccSign isaTh sort =
    let sortList = Set.toList(CASLSign.sortSet ccSign)
        preAlphabetType = Type {typeId = preAlphabetS , typeSort = [], typeArgs =[]}
        sortType = Type {typeId = convertSort2String sort, typeSort = [], typeArgs =[]}
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
                commonSuperList = Set.toList $ Set.intersection sortSuperSet sort'SuperSet

                -- If there are no tests then the rhs=false else combine all tests using binConj
                rhs = if (null allTests) then false else foldr1 binConj allTests

                -- The tests produce a list of equations for each test
                -- Test 1 =  test equality at: current sort vs current sort
                -- Test 2 =  test equality at: current sort vs super sorts
                -- Test 3 =  test equality at: super sorts  vs current sort
                -- Test 4 =  test equality at: super sorts  vs super sorts
                allTests = concat [test1, test2, test3, test4]
                test1 = if (sort == sort') then [binEq x y] else []
                test2 = if (Set.member sort sort'SuperSet)
                        then [binEq x (termAppl (getInjection sort' sort) y)]
                        else []
                test3 = if (Set.member sort' sortSuperSet)
                        then [binEq (termAppl (getInjection sort sort') x) y]
                        else []
                test4 = if (null commonSuperList) then [] else map test4_atSort commonSuperList
                test4_atSort s = binEq (termAppl (getInjection sort s) x)
                                       (termAppl (getInjection sort' s) y)
            in binEq lhs rhs
        eqs = map mkEq sortList
    in  addPrimRec eqs isaThWithConst

-- Functions for producing the Justification theorems

-- Add all justification theorems to an Isabelle Theory
-- We need to know the number of sorts
addJustificationTheorems :: [SORT] -> IsaTheory -> IsaTheory
addJustificationTheorems sorts isaTh = addTransitivityTheorem sorts
                                     $ addInjectivityTheorems
                                     $ addDecompositionTheorems
                                     $ addSymmetryTheorem sorts
                                     $ addReflexivityTheorem
                                     $ isaTh

-- Add the reflexivity theorem and proof to an Isabelle Theory
addReflexivityTheorem :: IsaTheory -> IsaTheory
addReflexivityTheorem isaTh =
    let name = reflexivityTheoremS
        x = mkFree "x"
        thmConds = []
        thmConcl = termAppl (termAppl (conDouble eqS) x) x
        proof' = IsaProof {
                   proof = [Apply (Induct "x"),
                            Apply Auto],
                   end = Done
                 }
    in addThreomWithProof name thmConds thmConcl proof' isaTh

-- Add the symmetry theorem and proof to an Isabelle Theory
-- We need to know the number of sorts
addSymmetryTheorem :: [SORT] -> IsaTheory -> IsaTheory
addSymmetryTheorem sorts isaTh =
    let numSorts = length(sorts)
        name = symmetryTheoremS
        x = mkFree "x"
        y = mkFree "y"
        thmConds = [termAppl (termAppl (conDouble eqS) x) y]
        thmConcl = termAppl (termAppl (conDouble eqS) y) x
        inductY = concat $ map (\i -> [Prefer (i*numSorts+1), Apply (Induct "y")]) [0..(numSorts-1)]
        proof' = IsaProof {
                   proof = [Apply (Induct "x")] ++ inductY ++ [Apply Auto],
                   end = Done
                 }
    in addThreomWithProof name thmConds thmConcl proof' isaTh

 -- Add the injectivity theorems and proofs which are deduced from the
 -- embedding_Injectivity axioms from the translation CASL2PCFOL;
 -- CASL2SubCFOL
addInjectivityTheorems :: IsaTheory -> IsaTheory
addInjectivityTheorems isaTh = isaTh

 -- Add the decomposition theorems and proofs which are deduced from the
 -- transitivity axioms from the translation CASL2PCFOL;
 -- CASL2SubCFOL
addDecompositionTheorems :: IsaTheory -> IsaTheory
addDecompositionTheorems isaTh = isaTh

-- Add the transitivity theorem and proof to an Isabelle Theory
-- We need to know the number of sorts
addTransitivityTheorem :: [SORT] -> IsaTheory -> IsaTheory
addTransitivityTheorem sorts isaTh =
    let numSorts = length(sorts)
        name = transitivityS
        x = mkFree "x"
        y = mkFree "y"
        z = mkFree "z"
        thmConds = [termAppl (termAppl (conDouble eqS) x) y, termAppl (termAppl (conDouble eqS) y) z]
        thmConcl = termAppl (termAppl (conDouble eqS) x) z
        inductY = concat $ map (\i -> [Prefer (i*numSorts+1), Apply (Induct "y")]) [0..(numSorts-1)]
        inductZ = concat $ map (\i -> [Prefer (i*numSorts+1), Apply (Induct "z")]) [0..((numSorts^(2::Int))-1)]
        proof' = IsaProof {
                   proof = [Apply (Induct "x")] ++ inductY ++ inductZ ++ [Apply Auto],
                   end = Sorry
                 }
    in addThreomWithProof name thmConds thmConcl proof' isaTh

--  Function to add preAlphabet as an equivalence relation to an Isabelle theory
addInstansanceOfEquiv :: IsaTheory  -> IsaTheory
addInstansanceOfEquiv  isaTh =
    let preAlphabetSort = [IsaClass preAlphabetS]
        eqvSort = [IsaClass eqvS]
        eqvProof = IsaProof []  (By (Other "intro_classes"))
        equivSort = [IsaClass equivS]
        equivProof = IsaProof [Apply (Other "intro_classes"),
                             Apply (Other "unfold preAlphabet_sim_def"),
                             Apply (Other "rule eq_refl"),
                             Apply (Other "rule eq_trans, auto"),
                             Apply (Other "rule eq_symm, simp")]
                            Done
        x = mkFree "x"
        y = mkFree "y"
        defLhs = termAppl x (termAppl (conDouble simS) y)
        defRhs = termAppl (termAppl (conDouble eqS) x) y
    in   addInstanceOf [preAlphabetSort] equivSort equivProof
       $ addDef preAlphabetSimDefS defLhs defRhs
       $ addInstanceOf [preAlphabetSort] eqvSort eqvProof
       $ isaTh

-- Function to help keep strings consistent

eqS :: String
eqS = "eq"

preAlphabetS :: String
preAlphabetS = "PreAlphabet"

reflexivityTheoremS :: String
reflexivityTheoremS = "eq_refl"

symmetryTheoremS :: String
symmetryTheoremS = "eq_symm"

transitivityS :: String
transitivityS = "eq_trans"

preAlphabetSimDefS :: String
preAlphabetSimDefS = "preAlphabet_sim_def"

simS :: String
simS = "\\<sim>"

-- String for the name of the axiomatic type class of equivalence relations part 1
eqvS :: String
eqvS  = "eqv"

-- String for the name of the axiomatic type class of equivalence relations part 2
equivS :: String
equivS  = "equiv"


-- This is NOT A GOOD way to do this function
-- Return the injection name of the injection from one sort to another
getInjection :: SORT -> SORT -> Term
getInjection s s' =
    let t = CASLSign.toOP_TYPE(CASLSign.OpType{CASLSign.opKind = Total,
                                               CASLSign.opArgs = [s],
                                               CASLSign.opRes = s'})
        injName = show $ CASLInject.uniqueInjName t
    --in conDouble $ "X_" ++ (show $ CASLInject.uniqueInjName t)
        replace string c s1 = concat (map (\x -> if x==c then s1 else [x]) string)

    in Const {
          termName= VName {
            new = ("X_" ++ injName),
            altSyn = Just (AltSyntax ((replace injName '_' "'_")   ++ "/'(_')") [3] 999)
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

-- Convert a SORT to a string
convertSort2String :: SORT -> String
convertSort2String s = show s

-- Function that returns the constructor of PreAlphabet for a given sort
mkPreAlphabetConstructor :: SORT -> String
mkPreAlphabetConstructor sort = "C_" ++ (show sort)

-- Function that takes a sort and outputs a the function name for the
-- corresponing compare_with function
mkCompareWithFunName :: SORT -> String
mkCompareWithFunName sort = ("compare_with_" ++ (show sort))

-- Functions for manipulating an Isabelle theory

-- Add a single constant to the signature of an Isabelle theory
addConst :: String -> Typ -> IsaTheory -> IsaTheory
addConst cName cType isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        isaTh_sign_ConstTab = constTab isaTh_sign
        isaTh_sign_ConstTabUpdated = Map.insert (mkVName cName) cType isaTh_sign_ConstTab
        isaTh_sign_updated = isaTh_sign {constTab = isaTh_sign_ConstTabUpdated}
    in (isaTh_sign_updated, isaTh_sen)

-- Add a primrec defintion to the sentences of an Isabelle theory
addPrimRec :: [Term] -> IsaTheory -> IsaTheory
addPrimRec terms isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        recDef = RecDef {keyWord = primrecS, senTerms = [terms]}
        namedRecDef = (makeNamed "what_does_this_word_do?" recDef) {isAxiom = False, isDef = True}
    in (isaTh_sign, isaTh_sen ++ [namedRecDef])

-- Add a DomainEntry to the domain tab of a signature of an Isabelle Theory
updateDomainTab :: DomainEntry  -> IsaTheory -> IsaTheory
updateDomainTab domEnt isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        isaTh_sign_domTab = domainTab isaTh_sign
        isaTh_sign_updated = isaTh_sign {domainTab = (isaTh_sign_domTab ++ [[domEnt]])}
    in (isaTh_sign_updated, isaTh_sen)

-- Add a theorem with proof to an Isabelle theory
addThreomWithProof :: String -> [Term] -> Term -> IsaProof -> IsaTheory -> IsaTheory
addThreomWithProof name conds concl proof' isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = if (null conds)
              then ((mkSen concl) {thmProof = Just proof'})
              else ((mkCond conds concl) {thmProof = Just proof'})
        namedSen = (makeNamed name sen) {isAxiom = False}
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- Function to add an instance of command to an Isabelle theory
addInstanceOf :: [Sort] -> Sort -> IsaProof -> IsaTheory -> IsaTheory
addInstanceOf args res pr isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = Instance "liam" args res pr
        namedSen = (makeNamed "" sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- Function to add a def command to an Isabelle theory
addDef :: String -> Term -> Term -> IsaTheory -> IsaTheory
addDef name lhs rhs isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = ConstDef (IsaEq lhs rhs)
        namedSen = (makeNamed name sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])

-- Code below this line is junk

-- Add a warning to an Isabelle theory
addWarning :: IsaTheory -> IsaTheory
addWarning isaTh =
    let fakeType = Type {typeId = "Fake_Type" , typeSort = [], typeArgs =[]}
    in addConst "Warning_this_is_not_a_stable_or_meaningful_translation" fakeType isaTh

-- Add a string version of the abstract syntax of an Isabelle theory to itself
addDebug :: IsaTheory -> IsaTheory
addDebug isaTh =
    let isaTh_sign = fst(isaTh)
        isaTh_sens = snd(isaTh)
        sensType = Type {typeId = show isaTh_sens , typeSort = [], typeArgs =[]}
        signType = Type {typeId = show isaTh_sign , typeSort = [], typeArgs =[]}
    in   addConst "debug_isaTh_sens" sensType
       $ addConst "debug_isaTh_sign" signType
       $ isaTh

addMR2 :: IsaTheory -> IsaTheory
addMR2  isaTh =
    let fakeType = Type {typeId = "Fake_Type" , typeSort = [], typeArgs =[]}
        isaTh_sign = fst isaTh
        isaTh_sign_tsig = tsig isaTh_sign
        myabbrs = abbrs isaTh_sign_tsig
        abbrsNew = Map.insert "Liam" (["MR2"], fakeType) myabbrs

        isaTh_sign_updated = isaTh_sign {tsig = (isaTh_sign_tsig {abbrs =abbrsNew}) }
    in (isaTh_sign_updated, snd isaTh)

addMR3 :: IsaTheory -> IsaTheory
addMR3 isaTh =
    let fakeType = Type {typeId = "Fake_Type" , typeSort = [], typeArgs =[]}
        fakeType2 = Type {typeId = "Fake_Type2" , typeSort = [], typeArgs =[]}
        isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        x = mkFree "x"
        y = mkFree "y"
        eq' = binEq x y
        set = SubSet x fakeType2 eq'
        sen = TypeDef fakeType set (IsaProof [] Sorry)
        namedSen = (makeNamed "tester" sen)
    in (isaTh_sign, isaTh_sen ++ [namedSen])
