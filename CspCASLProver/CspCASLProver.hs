{- |
Module      :  $Header$
Description :  Interface to the CspCASLProver (Isabelle based) theorem prover
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach, Swansea University 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Interface for CspCASLProver theorem prover.
-}

{-
  Interface between CspCASLProver and Hets:
   Hets writes CspCASLProver's Isabelle .thy files and
     starts Isabelle with CspProver
   User extends .thy file with proofs
   User finishes Isabelle
   Hets reads in created *.deps files
-}

module CspCASLProver.CspCASLProver
    ( cspCASLProver
    ) where

import CASL.AS_Basic_CASL
import CASL.Fold
import CASL.Sign (CASLSign, Sign (..))

import Common.AS_Annotation (Named, mapNamedM)
import Common.Result

import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.SignCSP
import CspCASL.Morphism (CspCASLMorphism)

import CspCASLProver.Consts
import CspCASLProver.IsabelleUtils
import CspCASLProver.Utils

import qualified Data.Maybe as Maybe
import qualified Data.Set as Set

import Isabelle.IsaProve (isaProve)
import qualified Isabelle.IsaSign as Isa

import Logic.Prover
import Logic.Comorphism (wrapMapTheory)

-- | The string that Hets uses as CspCASLProver
cspCASLProverS :: String
cspCASLProverS = "CspCASLProver"

-- | The wrapper function that is CspCASL Prover
cspCASLProver :: Prover CspCASLSign CspCASLSen CspCASLMorphism () ()
cspCASLProver = mkProverTemplate cspCASLProverS () cspCASLProverProve

-- | The main cspCASLProver function
cspCASLProverProve :: String -> Theory CspCASLSign CspCASLSen () -> a ->
                      IO [ProofStatus ()]
cspCASLProverProve thName (Theory ccSign ccSensThSens) _freedefs =
  let -- get the CASL signature of the data part of the CspcASL theory
      caslSign = ccSig2CASLSign ccSign
      -- Get a list of CspCASL named sentences
      ccNamedSens = toNamedList ccSensThSens
      -- A filter to change a CspCASLSen to a CASLSen (if possible)
      caslSenFilter ccSen = case ccSen of
        ExtFORMULA (ProcessEq _ _ _ _) -> Nothing
        sen -> Just $ foldFormula (mapRecord $ const ()) sen
      -- All named CASL sentences from the datapart
      caslNamedSens = Maybe.mapMaybe (mapNamedM caslSenFilter) ccNamedSens
      -- Generate data encoding. This may fail.
      Result diag dataTh = produceDataEncoding caslSign caslNamedSens
  in case dataTh of
    Nothing -> do
      -- Data translation failed
      putStrLn $ "Sorry, could not encode the data part:" ++ show diag
      return []
    Just (dataThSig, dataThSens, pcfolSign, cfolSign) -> do
      -- Data translation succeeded
      -- Write out the data encoding
      writeIsaTheory (mkThyNameDataEnc thName)
                         (Theory dataThSig (toThSens dataThSens))
      -- Generate and write out the preAlpbate, justification theorems
      -- and the instances code.
      writeIsaTheory (mkThyNamePreAlphabet thName)
                         (producePreAlphabet thName caslSign pcfolSign)
      -- Generate and write out the Alpbatet construction, bar types
      -- and choose functions.
      writeIsaTheory (mkThyNameAlphabet thName)
                         (produceAlphabet thName caslSign)
      -- Generate and write out the integration theorems
      writeIsaTheory (mkThyNameIntThms thName)
                         (produceIntegrationTheorems thName caslSign)
      -- Generate and Isabelle to prove the process refinements (also produces
      -- the processes)
      isaProve thName (produceProcesses thName ccSign ccNamedSens pcfolSign
                                        cfolSign) ()

-- |Produce the Isabelle theory of the data part of a CspCASL
-- specification. The data transalation can fail. If it does fail there will
-- be an error message. Its arguments are the CASL signature from the data
-- part and a list of the named CASL sentences from the data part. Returned
-- are the Isabelle signature, Isabelle named sentences and also the CASL
-- signature of the data part after translation to pcfol (i.e. with out
-- subsorting) and cfol (i.e. with out subsorting and partiality).
produceDataEncoding :: CASLSign -> [Named CASLFORMULA] ->
                       Result (Isa.Sign, [Named Isa.Sentence], CASLSign,
                                  CASLSign)
produceDataEncoding caslSign caslNamedSens =
    let -- Comorphisms
        casl2pcfol = wrapMapTheory CASL2PCFOL.CASL2PCFOL
        pcfol2cfol = wrapMapTheory $ CASL2SubCFOL.CASL2SubCFOL True
                     CASL2SubCFOL.AllSortBottoms
        cfol2isabelleHol = wrapMapTheory CFOL2IsabelleHOL.CFOL2IsabelleHOL
    in do
      -- Remove Subsorting from the CASL part of the CspCASL
      -- specification
      th_pcfol <- casl2pcfol (caslSign, caslNamedSens)
      -- Next Remove partial functions
      th_cfol <- pcfol2cfol th_pcfol
      -- Next Translate to IsabelleHOL code
      (th_isa_Sig, th_isa_Sens) <- cfol2isabelleHol th_cfol
      return (th_isa_Sig, th_isa_Sens, fst th_pcfol, fst th_cfol)

-- | Produce the Isabelle theory which contains the PreAlphabet,
-- Justification Theorems and also the instances code. We need the
-- PFOL signature which is the data part CASL signature after
-- translation to PCFOL (i.e. without subsorting) to pass on as an
-- argument.
producePreAlphabet :: String -> CASLSign -> CASLSign ->
                      Theory Isa.Sign Isa.Sentence ()
producePreAlphabet thName caslSign pfolSign =
    let sortList = Set.toList (sortSet caslSign)
        -- empty Isabelle signature which imports the data encoding
        -- and quotient.thy (which is needed for the instances code)
        isaSignEmpty = Isa.emptySign {Isa.imports = [mkThyNameDataEnc thName
                                                    , quotientThyS] }
        -- Start with our empty Isabelle theory, add the constructs
        (isaSign, isaSens) = addInstanceOfEquiv
                           $ addJustificationTheorems caslSign pfolSign
                           $ addAllGaAxiomsCollections caslSign pfolSign
                           $ addEqFun sortList
                           $ addAllCompareWithFun caslSign
                           $ addPreAlphabet sortList
                             (isaSignEmpty, [])
    in Theory isaSign (toThSens isaSens)

-- |Produce the Isabelle theory which contains the Alphabet
-- construction,  and also the bar types and choose
-- fucntions for CspCASLProver.
produceAlphabet :: String -> CASLSign -> Theory Isa.Sign Isa.Sentence ()
produceAlphabet thName caslSign =
    let sortList = Set.toList (sortSet caslSign)
        -- empty Isabelle signature which imports the preAlphabet encoding
        isaSignEmpty = Isa.emptySign {
                         Isa.imports = [mkThyNamePreAlphabet thName]}
        -- Start with our empty isabelle theory, add the Alphabet type
        -- , then the bar types and finally the choose functions.
        (isaSign, isaSens) = addAllChooseFunctions sortList
                           $ addAllBarTypes sortList
                           $ addAlphabetType
                             (isaSignEmpty, [])
    in Theory isaSign (toThSens isaSens)

-- |Produce the Isabelle theory which contains the Integration
-- Theorems on data
produceIntegrationTheorems :: String -> CASLSign ->
                              Theory Isa.Sign Isa.Sentence ()
produceIntegrationTheorems thName caslSign =
    let sortList = Set.toList (sortSet caslSign)
        -- empty Isabelle signature which imports the alphabet encoding
        isaSignEmpty = Isa.emptySign {Isa.imports = [mkThyNameAlphabet thName] }
        -- Start with our empty isabelle theory and add the
        -- integration theorems.
        (isaSign, isaSens) = addAllIntegrationTheorems sortList caslSign
                             (isaSignEmpty, [])
    in Theory isaSign (toThSens isaSens)

-- |Produce the Isabelle theory which contains the Process Translations and
-- process refinement theorems. We -- need the PCFOL and CFOL signatures of
-- the data part after translation to PCFOL and CFOL to pass -- along to the
-- process translation.
produceProcesses :: String -> CspCASLSign -> [Named CspCASLSen] ->
                    CASLSign -> CASLSign -> Theory Isa.Sign Isa.Sentence ()
produceProcesses thName ccSign ccNamedSens pcfolSign cfolSign =
    let caslSign = ccSig2CASLSign ccSign
        cspSign = ccSig2CspSign ccSign
        sortList = Set.toList (sortSet caslSign)
        sortRel' = sortRel caslSign
        chanNameMap = chans cspSign
        -- Isabelle signature which imports the integration theorems encoding
        -- and CSP_F
        isaSignEmpty = Isa.emptySign {Isa.imports = [mkThyNameIntThms thName
                                                    , cspFThyS] }
        -- Start with our empty isabelle theory and add the
        -- processes the the process refinement theorems.
        (isaSign, isaSens) =
            addProcTheorems ccNamedSens ccSign pcfolSign cfolSign
          $ addProcMap ccNamedSens ccSign pcfolSign cfolSign
          $ addProcNameDatatype cspSign
          $ addFlatTypes sortList
          $ addProjFlatFun
          $ addEventDataType sortRel' chanNameMap
            (isaSignEmpty, [])
    in Theory isaSign (toThSens isaSens)
