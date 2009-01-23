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

import Common.AS_Annotation (Named, mapNamedM)
import Common.Result

import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.SignCSP (ccSig2CASLSign, CspCASLSign, CspCASLSen(..), CspMorphism)

import CspCASLProver.Utils

import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

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
cspCASLProverProve thName ccTh _freedefs = do
  -- Generate data encoding. This may fail.
  let Result diag (dataTh) = produceDataEncoding ccTh
  case dataTh of
    -- Data translation failed
    Nothing -> do
      putStrLn $ "Sorry, could not encode the data part:" ++ (show diag)
      return []
    Just (dataThSig, dataThSens) -> do
      -- Write out the data encoding
      writeIsaTheory (mkThyNameDataEnc thName)
                         (Theory dataThSig (toThSens dataThSens))
      -- Generate and write out the other Isabelle theory files
      writeIsaTheory (mkThyNameAlphabet thName) produceAlphabet
      -- writeIsaTheory (thName ++ "_integrationThms")
      --               produceIntegrationTheorems
      -- writeIsaTheory (thName ++ "_processes") produceProcesses
      -- Use Isabelle to prove the refinement
      isaProve thName produceProcessRefinements ()

-- | Produce the Isabelle theory of the data part of a CspCASL
--   specification. The data transaltion can fail. If it does fail
--   there will be an error message.
produceDataEncoding :: Theory CspCASLSign CspCASLSen () ->
                       Result (Isa.Sign, [Named Isa.Sentence])
produceDataEncoding (Theory ccSign ccSensThSens) =
    let caslSign = ccSig2CASLSign ccSign
        -- Get a list of CASL sentences from the data part
        ccNamedSens = toNamedList ccSensThSens
        caslSenFilter ccSen = case ccSen of
                                CASLSen sen -> Just sen
                                ProcessEq _ _ _ _ -> Nothing
        caslNamedSens = Maybe.catMaybes $
                        map (mapNamedM caslSenFilter) ccNamedSens
        -- Comorphisms
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
produceAlphabet :: Theory Isa.Sign Isa.Sentence ()
produceAlphabet = Theory Isa.emptySign Map.empty


-- -- | Add the PreAlphabet (built from a list of sorts) to an Isabelle theory
-- addPreAlphabet :: [SORT] -> IsaTheory -> IsaTheory
-- addPreAlphabet sortList isaTh =
--    let preAlphabetDomainEntry = mkPreAlphabetDE sortList
--    in updateDomainTab preAlphabetDomainEntry isaTh

-- - | Make a PreAlphabet Domain Entry from a list of sorts
-- mkPreAlphabetDE :: [SORT] -> DomainEntry
-- mkPreAlphabetDE sorts =
--     (Type {typeId = preAlphabetS, typeSort = [isaTerm], typeArgs = []},
--          map (\sort ->
--                   (mkVName (mkPreAlphabetConstructor sort),
--                                [Type {typeId = convertSort2String sort,
--                                       typeSort = [isaTerm],
--                                       typeArgs = []}])
--              ) sorts
--     )



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
produceProcessRefinements :: Theory Isa.Sign Isa.Sentence ()
produceProcessRefinements = Theory Isa.emptySign Map.empty
