{- |
Module      :  $Header$
Description :  embedding from CspCASL to Isabelle-HOL
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach,
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
import qualified CASL.Inject as CASLInject
import qualified CASL.Sign as CASLSign
import Common.AS_Annotation
import Common.Result
import qualified Common.Lib.Rel as Rel
import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL
import Comorphisms.CFOL2IsabelleHOL(IsaTheory)
import CspCASL.Logic_CspCASL
import CspCASL.AS_CspCASL
import CspCASL.Trans_CspProver
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

-- | Translate CspCASL theories to Isabelle
transCCTheory :: (CspCASLSign, [Named CspCASLSentence]) -> Result IsaTheory
transCCTheory ccTheory =
    let ccSign = fst ccTheory
        ccSens = snd ccTheory
        caslSign = ccSig2CASLSign ccSign
        casl2pcfol = (map_theory CASL2PCFOL.CASL2PCFOL)
        pcfol2cfol = (map_theory CASL2SubCFOL.defaultCASL2SubCFOL)
        cfol2isabelleHol = (map_theory CFOL2IsabelleHOL.CFOL2IsabelleHOL)
        sortList = Set.toList(CASLSign.sortSet caslSign)
        --fakeType = Type {typeId = "Fake_Type" , typeSort = [], typeArgs =[]}
    in do -- Remove Subsorting from the CASL part of the CspCASL specification
          translation1 <- casl2pcfol (caslSign,[])
          -- Next Remove partial functions
          translation2 <- pcfol2cfol translation1
          -- Next Translate to IsabelleHOL code
          translation3 <- cfol2isabelleHol translation2
          -- Next add the preAlpabet construction to the IsabelleHOL code
          return $ addCspCaslSentences ccSens
                 $ addInstansanceOfEquiv
                 $ addJustificationTheorems ccSign (fst translation1)
                 $ addEqFun sortList
                 $ addAllCompareWithFun ccSign
                 $ addPreAlphabet sortList
                 $ addWarning
                 $ translation3

-- This is not implemented in a sensible way yet and is not used
transCCSentence :: CspCASLSign -> CspCASLSentence -> Result IsaSign.Sentence
transCCSentence _ (CspCASLSentence pn _ _) =
    do return (mkSen (Const (mkVName (show pn))
                                (Disp (Type "byeWorld" [] []) TFun Nothing)))

-- | Add a list of CspCASL sentences to an Isabelle theory
addCspCaslSentences :: [Named CspCASLSentence] -> IsaTheory -> IsaTheory
addCspCaslSentences namedSens isaTh = foldl addCspCaslSentence isaTh namedSens

-- | Add a single CspCASL sentence to an Isabelle theory
addCspCaslSentence :: IsaTheory -> Named CspCASLSentence -> IsaTheory
addCspCaslSentence isaTh namedSen =
    let sen = sentence namedSen
    in case sen of
         CspCASLSentence pn _ proc ->
             let name = show pn
                 t1 = conDouble name
                 t2 = transProcess proc
             in addDef name t1 t2 isaTh

-- Functions for adding the PreAlphabet datatype to an Isabelle theory

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

-- Functions for adding the eq functions and the compare_with
-- functions to an Isabelle theory

-- | Add the eq function to an Isabelle theory using a list of sorts
addEqFun :: [SORT] -> IsaTheory -> IsaTheory
addEqFun sortList isaTh =
    let preAlphabetType = Type {typeId = preAlphabetS,
                                typeSort = [],
                                typeArgs =[]}
        eqtype = mkFunType preAlphabetType $ mkFunType preAlphabetType boolType
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
        preAlphabetType = Type {typeId = preAlphabetS,
                                typeSort = [],
                                typeArgs =[]}
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
                        then [binEq x (termAppl (getInjectionOp sort' sort) y)]
                        else []
                test3 = if (Set.member sort' sortSuperSet)
                        then [binEq (termAppl (getInjectionOp sort sort') x) y]
                        else []
                test4 = if (null commonSuperList)
                        then []
                        else map test4_atSort commonSuperList
                test4_atSort s = binEq (termAppl (getInjectionOp sort s) x)
                                       (termAppl (getInjectionOp sort' s) y)
            in binEq lhs rhs
        eqs = map mkEq sortList
    in  addPrimRec eqs isaThWithConst

-- Functions for producing the Justification theorems

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
        injOp = getInjectionOp s1 s2
        injX = termAppl injOp x
        injY = termAppl injOp y
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
        injOp_s1_s2 = getInjectionOp s1 s2
        injOp_s2_s3 = getInjectionOp s2 s3
        injOp_s1_s3 = getInjectionOp s1 s3
        inj_s1_s2_s3 = termAppl injOp_s2_s3 (termAppl injOp_s1_s2 x)
        inj_s1_s3 = termAppl injOp_s1_s3 x
        definedOp_s1 = getDefinedOp sorts s1
        definedOp_s3 = getDefinedOp sorts s3
        collectionTransAx = getCollectionTransAx sortRel
        collectionTotAx = getCollectionTotAx pfolSign
        collectionNotDefBotAx = getCollectionNotDefBotAx sorts

        name = getDecompositionThmName(s1, s2, s3)
        conds = []
        concl = binEq inj_s1_s2_s3 inj_s1_s3

        proof' = IsaProof [Apply(CaseTac (definedOp_s3 inj_s1_s2_s3)),
                           -- Case 1
                           Apply(SubgoalTac(definedOp_s1 x)),
                           Apply(Insert collectionTransAx),
                           Apply(Simp),
                           Apply(SimpAdd Nothing collectionTotAx),

                           -- Case 2
                           Apply(SubgoalTac(
                               termAppl notOp(definedOp_s3 inj_s1_s3))),
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

-- | Function to add preAlphabet as an equivalence relation to an
--   Isabelle theory
addInstansanceOfEquiv :: IsaTheory  -> IsaTheory
addInstansanceOfEquiv  isaTh =
    let eqvSort = [IsaClass eqvTypeClassS]
        eqvProof = IsaProof []  (By (Other "intro_classes"))
        equivSort = [IsaClass equivTypeClassS]
        equivProof = IsaProof [Apply (Other "intro_classes"),
                               Apply (Other "unfold preAlphabet_sim_def"),
                               Apply (Other "rule eq_refl"),
                               Apply (Other "rule eq_trans, auto"),
                               Apply (Other "rule eq_symm, simp")]
                               Done
        x = mkFree "x"
        y = mkFree "y"
        defLhs = binEqvSim x y
        defRhs = binEq_PreAlphabet x y
    in   addInstanceOf preAlphabetS [] equivSort equivProof
       $ addDef preAlphabetSimS defLhs defRhs
       $ addInstanceOf preAlphabetS [] eqvSort eqvProof
       $ isaTh

-- Function to help keep strings consistent

eq_PreAlphabetS :: String
eq_PreAlphabetS = "eq_PreAlphabet"

eq_PreAlphabetV :: VName
eq_PreAlphabetV   = VName eq_PreAlphabetS $ Nothing

binEq_PreAlphabet :: Term -> Term -> Term
binEq_PreAlphabet = binVNameAppl eq_PreAlphabetV


preAlphabetS :: String
preAlphabetS = "PreAlphabet"

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

-- | Return the injection name of the injection from one sort to another
--   This function is not implemented in a satisfactory way
getInjectionOp :: SORT -> SORT -> Term
getInjectionOp s s' =
    let injName = getInjectionName s s'
        replace string c s1 = concat (map (\x -> if x==c
                                                 then s1
                                                 else [x]) string)
    in Const {
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

-- This function is not implemented in a satisfactory way
-- Return the list of strings of all gn_totality axioms
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
        namedSen = (makeNamed "tester" sen)
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
{-
addMR2 :: IsaTheory -> IsaTheory
addMR2  isaTh =
    let fakeType = Type {typeId = "Fake_Type" , typeSort = [], typeArgs =[]}
        isaTh_sign = fst isaTh
        isaTh_sign_tsig = tsig isaTh_sign
        myabbrs = abbrs isaTh_sign_tsig
        abbrsNew = Map.insert "Liam" (["MR2"], fakeType) myabbrs

        isaTh_sign_updated = isaTh_sign {
                               tsig = (isaTh_sign_tsig {abbrs =abbrsNew})
                             }
    in (isaTh_sign_updated, snd isaTh)
-}
{-
addMR3 :: IsaTheory -> IsaTheory
addMR3 isaTh =
    let fakeType = Type {typeId = "Fake_TypeMR3" , typeSort = [], typeArgs =[]}
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
-}
