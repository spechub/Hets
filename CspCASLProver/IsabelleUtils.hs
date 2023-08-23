{- |
Module      :  ./CspCASLProver/IsabelleUtils.hs
Description :  Utilities for CspCASLProver related to Isabelle
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
               Swansea University 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Utilities for CspCASLProver related to Isabelle. The functions here
typically manipulate Isabelle signatures.
-}

module CspCASLProver.IsabelleUtils
    ( addConst
    , addDef
    , addInstanceOf
    , addLemmasCollection
    , addPrimRec
    , addTheoremWithProof
    , updateDomainTab
    , writeIsaTheory
    ) where

import Common.AS_Annotation (makeNamed, Named, SenAttr (..))
import Common.ProofUtils (prepareSenNames)

import Comorphisms.CFOL2IsabelleHOL (IsaTheory)

-- import CspCASLProver.Consts

import qualified Data.Map as Map

import Isabelle.IsaParse (parseTheory)
import Isabelle.IsaPrint (getAxioms, printIsaTheory)
import Isabelle.IsaSign (DomainEntry, IsaProof (..), mkCond, mkSen
                         , Sentence (..), Sign (..), Sort
                         , Term (..), Typ (..))
import Isabelle.IsaConsts (mkVName)
import Isabelle.Translate (transString)

import Logic.Prover (Theory (..), toNamedList)

import Text.ParserCombinators.Parsec (parse)

-- | Add a single constant to the signature of an Isabelle theory
addConst :: String -> Typ -> IsaTheory -> IsaTheory
addConst cName cType isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        isaTh_sign_ConstTab = constTab isaTh_sign
        isaTh_sign_ConstTabUpdated =
            Map.insert (mkVName cName) cType isaTh_sign_ConstTab
        isaTh_sign_updated = isaTh_sign {
                               constTab = isaTh_sign_ConstTabUpdated
                             }
    in (isaTh_sign_updated, isaTh_sen)

-- | Function to add a def command to an Isabelle theory
addDef :: String -> Term -> Term -> IsaTheory -> IsaTheory
addDef name lhs rhs isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = ConstDef (IsaEq lhs rhs)
        namedSen = makeNamed name sen
    in (isaTh_sign, isaTh_sen ++ [namedSen])

{- | Function to add an instance of command to an Isabelle theory. The
sort parameters here are basically strings. -}
addInstanceOf :: String -> [Sort] -> Sort -> [(String, Term)] -> IsaProof ->
                 IsaTheory -> IsaTheory
addInstanceOf name args res defs prf isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = Instance name args res defs prf
        namedSen = makeNamed name sen
    in (isaTh_sign, isaTh_sen ++ [namedSen])

{- | Add a lemmas sentence (definition) that allow us to group large collections
of lemmas in to a single lemma. This cuts down on the repreated addition of
lemmas in the proofs. -}
addLemmasCollection :: String -> [String] -> IsaTheory -> IsaTheory
addLemmasCollection lemmaname lemmas isaTh =
    if null lemmas
    then isaTh
    else let isaTh_sign = fst isaTh
             isaTh_sen = snd isaTh
             -- Make a named lemmas sentence
             namedSen = (makeNamed lemmaname (Lemmas lemmaname lemmas))
                        {isAxiom = False}
         in (isaTh_sign, isaTh_sen ++ [namedSen])

{- | Add a constant with a primrec defintion to the sentences of an Isabelle
theory. Parameters: constant name, type, primrec defintions and isabelle
theory to be added to. -}
addPrimRec :: String -> Typ -> [Term] -> IsaTheory -> IsaTheory
addPrimRec cName cType terms isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        primRecDef = RecDef {
          keyword = Nothing, constName = mkVName cName,
          constType = Just cType, primRecSenTerms = terms}
        namedPrimRecDef = (makeNamed "BUG_what_does_this_word_do?" primRecDef) {
          isAxiom = False,
          isDef = True}
    in (isaTh_sign, isaTh_sen ++ [namedPrimRecDef])

-- | Add a theorem with proof to an Isabelle theory
addTheoremWithProof :: String -> [Term] -> Term -> IsaProof -> IsaTheory ->
                      IsaTheory
addTheoremWithProof name conds concl proof' isaTh =
    let isaTh_sign = fst isaTh
        isaTh_sen = snd isaTh
        sen = if null conds
              then ((mkSen concl) {thmProof = Just proof'})
              else ((mkCond conds concl) {thmProof = Just proof'})
        namedSen = (makeNamed name sen) {isAxiom = False}
    in (isaTh_sign, isaTh_sen ++ [namedSen])

{- | Prepare a theory for writing it out to a file. This function is based off
the function Isabelle.IsaProve.prepareTheory. The difference being that
this function does not mark axioms nor theorms as to be added to the
simplifier in Isabelle. -}
prepareTheory :: Theory Sign Sentence ()
    -> (Sign, [Named Sentence], [Named Sentence], Map.Map String String)
prepareTheory (Theory sig nSens) = let
    oSens = toNamedList nSens
    nSens' = prepareSenNames transString oSens
    (disAxs, disGoals) = getAxioms nSens'
    in (sig, disAxs, disGoals,
       Map.fromList $ zip (map senAttr nSens') $ map senAttr oSens)

-- | Add a DomainEntry to the domain tab of an Isabelle signature.
updateDomainTab :: DomainEntry -> IsaTheory -> IsaTheory
updateDomainTab domEnt (isaSign, isaSens) =
    let oldDomTab = domainTab isaSign
        isaSignUpdated = isaSign {domainTab = oldDomTab ++ [[domEnt]]}
    in (isaSignUpdated, isaSens)

{- | Write out an Isabelle Theory. The theory should just run through
in Isabelle without any user interactions. This is based heavily
off Isabelle.IsaProve.isaProve -}
writeIsaTheory :: String -> Theory Sign Sentence () -> IO ()
writeIsaTheory thName th = do
  let (sig, axs, ths, _) = prepareTheory th
      -- thms = map senAttr ths
      thBaseName = reverse . takeWhile (/= '/') $ reverse thName
      {- useaxs = filter (\ s ->
      sentence s /= mkSen true && (isDef s ||
      isSuffixOf "def" (senAttr s))) axs
      defaultProof = Just $ IsaProof
      (if null useaxs then [] else [Using $ map senAttr useaxs])
      By Auto -}
      thy = shows (printIsaTheory thBaseName sig $ axs ++ ths) "\n"
      thyFile = thBaseName ++ ".thy"
  -- Check if the Isabelle theory is a valid Isabelle theory
  case parse parseTheory thyFile thy of
    Right _ -> do
      {- prepareThyFiles (ho, bo) thyFile thy
      removeDepFiles thBaseName thms
      isabelle <- getEnvDef "HETS_ISABELLE" "Isabelle"
      callSystem $ isabelle ++ " " ++ thyFile
      ok <- checkFinalThyFile (ho, bo) thyFile
      if ok then getAllProofDeps m thBaseName thms
      else return [] -}
      writeFile thyFile thy
      return ()
    {- The Isabelle theory is not a valid theory (according to Hets)
    as it cannot be parsed. -}
    Left err -> do
      print err
      putStrLn $ "Sorry, a generated theory cannot be parsed, see: "
                   ++ thyFile
      writeFile thyFile thy
      putStrLn "Aborting Isabelle proof attempt"
      return ()
