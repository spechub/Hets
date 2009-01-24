{- |
Module      :  $Header$
Description :  interface to the CspCASLProver (Isabelle based) theorem prover
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach, Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import CASL.AS_Basic_CASL (CASLFORMULA)
import CASL.Sign (CASLSign, Sign(..))

import Common.AS_Annotation (Named, mapNamedM)
import Common.Result

import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.SignCSP (ccSig2CASLSign, CspCASLSign, CspCASLSen(..), CspMorphism)

import CspCASLProver.Consts
import CspCASLProver.IsabelleUtils
import CspCASLProver.Utils

import qualified Data.Map as Map
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
cspCASLProver :: Prover CspCASLSign CspCASLSen CspMorphism () ()
cspCASLProver = mkProverTemplate cspCASLProverS () cspCASLProverProve

-- | The main cspCASLProver function
cspCASLProverProve :: String -> Theory CspCASLSign CspCASLSen () -> a ->
                      IO([Proof_status ()])
cspCASLProverProve thName (Theory ccSign ccSensThSens) _freedefs =
  let -- get the CASL signature of the data part of the CspcASL theory
      caslSign = ccSig2CASLSign ccSign
      -- Get a list of CspCASL named sentences
      ccNamedSens = toNamedList ccSensThSens
      -- A filter to change a CspCASLSen to a CASLSen (if possible)
      caslSenFilter ccSen = case ccSen of
                              CASLSen sen -> Just sen
                              ProcessEq _ _ _ _ -> Nothing
      -- All named CASL sentences from the datapart
      caslNamedSens = Maybe.catMaybes $
                      map (mapNamedM caslSenFilter) ccNamedSens
      -- Generate data encoding. This may fail.
      Result diag (dataTh) = produceDataEncoding caslSign caslNamedSens
  in case dataTh of
    Nothing -> do
      -- Data translation failed
      putStrLn $ "Sorry, could not encode the data part:" ++ (show diag)
      return []
    Just (dataThSig, dataThSens) -> do
      -- Data translation succeeded
      -- Write out the data encoding
      writeIsaTheory (mkThyNameDataEnc thName)
                         (Theory dataThSig (toThSens dataThSens))
      -- Generate and write out the other Isabelle theory files
      writeIsaTheory (mkThyNameAlphabet thName)
                         (produceAlphabet thName caslSign)
      -- writeIsaTheory (thName ++ "_integrationThms")
      --               produceIntegrationTheorems
      -- writeIsaTheory (thName ++ "_processes") produceProcesses
      -- Use Isabelle to prove the refinement
      isaProve thName (produceProcessRefinements thName) ()

-- | Produce the Isabelle theory of the data part of a CspCASL
--   specification. The data transaltion can fail. If it does fail
--   there will be an error message. Its arguments are the CASL
--   signature from the data part and a list of the named CASL
--   sentences from the data part
produceDataEncoding :: CASLSign -> [Named CASLFORMULA] ->
                       Result (Isa.Sign, [Named Isa.Sentence])
produceDataEncoding caslSign caslNamedSens =
    let -- Comorphisms
        casl2pcfol = (wrapMapTheory CASL2PCFOL.CASL2PCFOL)
        pcfol2cfol = (wrapMapTheory CASL2SubCFOL.defaultCASL2SubCFOL)
        cfol2isabelleHol = (wrapMapTheory CFOL2IsabelleHOL.CFOL2IsabelleHOL)
    in do -- Remove Subsorting from the CASL part of the CspCASL
          -- specification
          th1 <- casl2pcfol (caslSign, caslNamedSens)
          -- Next Remove partial functions
          th2 <- pcfol2cfol th1
          -- Next Translate to IsabelleHOL code
          cfol2isabelleHol th2

-- | Produce the Isabelle theory which contains the Alphabet and
--   Justification Theorems
produceAlphabet :: String -> CASLSign -> Theory Isa.Sign Isa.Sentence ()
produceAlphabet thName caslSign =
    let sortList = Set.toList(sortSet caslSign)
        -- Isabelle sgnature which imports the data encoding
        isaSign = Isa.emptySign {Isa.imports = [mkThyNameDataEnc thName] }
        -- Add to the empty isabelle signature our domain entry
        isaSign' = addPreAlphabet sortList isaSign
    in Theory isaSign' Map.empty

-- | Produce the Isabelle theory which contains the Integration
--   Theorems on data
--produceIntegrationTheorems :: Theory Isa.Sign Isa.Sentence ()
--produceIntegrationTheorems = Theory Isa.emptySign Map.empty

-- | Produce the Isabelle theory which contains the Process
-- | Translations
--produceProcesses :: Theory Isa.Sign Isa.Sentence ()
--produceProcesses = Theory Isa.emptySign Map.empty

-- | Produce the Isabelle theory which contains the Data Theorems
--   place holder code and the Process Refinement theorems
produceProcessRefinements :: String -> Theory Isa.Sign Isa.Sentence ()
produceProcessRefinements thName =
    --  Isabelle sgnature which imports the data encoding (for now)
    let isaSign = Isa.emptySign {Isa.imports = [mkThyNameAlphabet thName] }
    in Theory isaSign Map.empty
