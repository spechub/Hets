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
import qualified CASL.Sign as CaslSign
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

-- ***************************************************************************
-- * Functions for translating CspCasl theories and sentences to IsabelleHOL *
-- ***************************************************************************

transCCTheory :: (CspCASLSign, [Named CspCASLSentence]) -> Result IsaTheory
transCCTheory ccTheory = let ccSign = fst ccTheory
                             caslSign = ccSig2CASLSign ccSign 
                             casl2pcfol = (map_theory CASL2PCFOL.CASL2PCFOL)
                             pcfol2cfol = (map_theory CASL2SubCFOL.defaultCASL2SubCFOL)
                             cfol2isabelleHol = (map_theory CFOL2IsabelleHOL.CFOL2IsabelleHOL)                
                             sortList = Set.toList(CaslSign.sortSet caslSign)
                         in do -- Remove Subsorting from the CASL part of the CspCASL specification
                               translation1 <- casl2pcfol (caslSign,[])
                               -- Next Remove partial functions
                               translation2 <- pcfol2cfol translation1
                               -- Next Translate to IsabelleHOL code
                               translation3 <- cfol2isabelleHol translation2
                               -- Next add the preAlpabet construction to the IsabelleHOL code
                               return $ addEqFun sortList
                                      $ addPreAlphabet sortList
                                      $ addTesterThreomAndProof
                                      $ addDebug
                                      $ addWarning
                                      $ translation3

-- This is not implemented in a sensible way yet
transCCSentence :: CspCASLSign -> CspCASLSentence -> Result IsaSign.Sentence
transCCSentence _ _ = do return (mkSen (Const (mkVName "helloWorld") (Disp (Type "byeWorld" [] []) TFun Nothing)))

-- ***********************************************************************
-- * Functions for adding the PreAlphabet datatype to an Isabelle theory *
-- ***********************************************************************

-- Add the PreAlphabet (built from a list of sorts) to an Isabelle theory 
addPreAlphabet :: [SORT] -> IsaTheory -> IsaTheory
addPreAlphabet sortList isaTh = let preAlphabetDomainEntry = mkPreAlphabetDE sortList
                                in updateDomainTab preAlphabetDomainEntry isaTh

-- Make a PreAlphabet Domain Entry from a list of sorts
mkPreAlphabetDE :: [SORT] -> DomainEntry
mkPreAlphabetDE sorts = (Type {typeId = "PreAlphabet", typeSort = [isaTerm], typeArgs = []},
                         map (\sortName ->
                              (mkVName ("C_" ++ sortName), [Type {typeId = sortName,
                                                                  typeSort = [isaTerm],
                                                                  typeArgs = []}])
                             ) (map show sorts)
                        )

-- **************************************************************
-- * Functions for adding the eq function to an Isabelle theory *
-- **************************************************************

-- Adds the Eq function to an Isabelle theory using a list of sorts
addEqFun :: [SORT] -> IsaTheory -> IsaTheory
addEqFun sortlist isaTh = let isaThWithConst = addConst "eq" "PreAlphabet => PreAlphabet => Bool" isaTh     
                              mkEq = (\sortName ->
                                let x = mkFree "x"
                                    lhs = termAppl (conDouble "eq") (termAppl (conDouble ("C_" ++ sortName)) x)
                                    rhs = termAppl (conDouble ("compare_with_" ++ sortName)) x
                                in binEq lhs rhs)
                              eqs = map mkEq $ map show sortlist
                          in addPrimRec eqs isaThWithConst

-- ************************************************************************
-- * Functions for creating the equations in the compare_with_X functions *
-- ************************************************************************

-- This is what we want to represent
-- Const ("op =", "bool => bool => bool")

-- This is what we have as a type
-- Const { termName   :: VName,
--   termType   :: DTyp }

-- Const { termName   :: VName,
--   termType   :: DTyp }


mkLHS :: SORT -> SORT -> Term
mkLHS s1 s2 = let s1Name = show s1 
                  s2Name = show s2
                  funName = "compare_with_" ++ s1Name
                  s2constructor = "C_" ++ s2Name
                  x = mkFree "x"
                  y = mkFree "y"
                  c1 = termAppl (conDouble funName) x
                  c2 = termAppl (conDouble s2constructor) y
                  c3 = termAppl c1 c2
              in c3

mkRHS :: [Term] -> Term
mkRHS eqs = foldr1 binEq eqs 

{-
termInj = termAppl (conDouble "g__inj")
e1 = binEq s1 s2
e2 = binEq (termInj s1) (termInj s2)
a = binConj e1 e2
final = binEq c3 a

into Isabelle/IsaPrint.hs and calling printTerm:

*Isabelle.IsaPrint> printTerm final
compare_with_A s1 (C_A s2) = (s1 = s2 & g__inj s1 = g__inj s2)
-}

-- *************************************************
-- * Functions for manipulating an Isabelle theory *
-- *************************************************

-- Add a constant to the signature of an Isabelle theory
addConst :: String -> String -> IsaTheory -> IsaTheory
addConst cName cType isaTh = let isaTh_sign = fst isaTh
                                 isaTh_sen = snd isaTh
                                 isaTh_sign_ConstTab = constTab isaTh_sign
                                 constVName = mkVName cName
                                 constTyp = Type {typeId = cType , typeSort = [], typeArgs =[]}
                                 isaTh_sign_ConstTabUpdated = Map.insert constVName constTyp isaTh_sign_ConstTab
                                 isaTh_sign_updated = isaTh_sign {constTab = isaTh_sign_ConstTabUpdated}
                             in (isaTh_sign_updated, isaTh_sen)


-- Add a primrec defintion to the sentences of an Isabelle theory
addPrimRec :: [Term] -> IsaTheory -> IsaTheory
addPrimRec terms isaTh = let isaTh_sign = fst isaTh
                             isaTh_sen = snd isaTh
                             recDef = RecDef {keyWord = primrecS, senTerms = [terms]}
                             namedRecDef = (makeNamed "what_does_this_word_do?" recDef) {isAxiom = False, isDef = True}
                         in (isaTh_sign, isaTh_sen ++ [namedRecDef])

-- Add a DomainEntry to the domain tab of a signature of an Isabelle Theory
updateDomainTab :: DomainEntry  -> IsaTheory -> IsaTheory 
updateDomainTab domEnt isaTh = let isaTh_sign = fst isaTh
                                   isaTh_sen = snd isaTh
                                   isaTh_sign_domTab = domainTab isaTh_sign
                                   isaTh_sign_updated = isaTh_sign {domainTab = (isaTh_sign_domTab ++ [[domEnt]])}
                               in (isaTh_sign_updated, isaTh_sen)


-- ********************************
-- * Code below this line is junk *
-- ********************************

-- Add a warning to an Isabelle theory
addWarning :: IsaTheory -> IsaTheory
addWarning isaTh = addConst "Warning_this_is_not_a_stable_or_meaningful_translation" "fake_type" isaTh

-- Add a string version of the abstract syntax of an Isabelle theory to itself
addDebug :: IsaTheory -> IsaTheory
addDebug isaTh = let isaTh_sign = fst(isaTh)
                     isaTh_sens = snd(isaTh)
                 in   addConst "debug_isaTh_sens" (show isaTh_sens)
                    $ addConst "debug_isaTh_sign" (show isaTh_sign)
                    $ isaTh

-- Add a test theorm and proof to an Isabelle theory
addTesterThreomAndProof :: IsaTheory -> IsaTheory
addTesterThreomAndProof isaTh = let isaTh_sign = fst isaTh
                                    isaTh_sen = snd isaTh
                                    term = binEq (mkFree "x") (mkFree "x")
                                    sen = (mkSen term) {thmProof = Just "apply(induct x)\napply(auto)\ndone"}
                                    namedSen = (makeNamed "testTheorem" sen) {isAxiom =False}
                                in (isaTh_sign, isaTh_sen ++ [namedSen])