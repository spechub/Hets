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

import Common.AS_Annotation ()

-- import qualified Comorphisms.CASL2PCFOL as CASL2PCFOL
-- import qualified Comorphisms.CASL2SubCFOL as CASL2SubCFOL
-- import qualified Comorphisms.CFOL2IsabelleHOL as CFOL2IsabelleHOL

import CspCASL.SignCSP (CspCASLSign, CspCASLSen, CspMorphism)
-- also may need ccSig2CASLSign from above

import qualified Data.Map as Map

import Logic.Prover
-- import Logic.Comorphism (map_theory)

import Isabelle.IsaParse (parseTheory)
import Isabelle.IsaPrint (printIsaTheory)
import Isabelle.IsaProve (isaProve, prepareTheory)
import qualified Isabelle.IsaSign as Isa
-- import Isabelle.MarkSimp (markSimp, markThSimp)
-- import Isabelle.Translate (transString)

import Text.ParserCombinators.Parsec (parse)

-- | The string that Hets uses as CspCASLProver
cspCASLProverS :: String
cspCASLProverS = "CspCASLProver"

-- | The wrapper function that is CspCASL Prover
cspCASLProver :: Prover CspCASLSign CspCASLSen CspMorphism () ()
cspCASLProver = mkProverTemplate cspCASLProverS () cspCASLProverProve

-- | Write out an Isabelle Theory. The theory should just run through
--   in Isabelle without any user interactions. This is based heavily
--   off Isabelle.IsaProve.isaProve
writeIsaTheory :: String -> Theory Isa.Sign Isa.Sentence () -> IO ()
writeIsaTheory thName th = do
  let (sig, axs, ths, _) = prepareTheory th
      -- thms = map senAttr ths
      thBaseName = reverse . takeWhile (/= '/') $ reverse thName
      -- useaxs = filter (\ s ->
      --      sentence s /= mkSen true && (isDef s ||
      --         isSuffixOf "def" (senAttr s))) axs
      -- defaultProof = Just $ IsaProof
      --  (if null useaxs then [] else [Using $ map senAttr useaxs])
      --  $ By Auto
      thy = shows (printIsaTheory thBaseName sig $ axs ++ ths) "\n"
      thyFile = thBaseName ++ ".thy.liam"
  -- | Check if the Isabelle theory is a valid Isabelle theory
  case parse parseTheory thyFile thy of
    Right _ -> do
      -- prepareThyFiles (ho, bo) thyFile thy
      -- removeDepFiles thBaseName thms
      -- isabelle <- getEnvDef "HETS_ISABELLE" "Isabelle"
      -- callSystem $ isabelle ++ " " ++ thyFile
      -- ok <- checkFinalThyFile (ho, bo) thyFile
      -- if ok then getAllProofDeps m thBaseName thms
      --    else return []
      writeFile thyFile thy
      return ()
    -- | The Isabelle theory is not a valid theory (according to Hets)
    -- | as it cannot be parsed.
    Left err -> do
      putStrLn $ show err
      putStrLn $ "Sorry, a generated theory cannot be parsed, see: "
                   ++ thyFile
      writeFile thyFile thy
      putStrLn "Aborting Isabelle proof attempt"
      return ()

-- | The main cspCASLProver function
cspCASLProverProve :: String -> Theory CspCASLSign CspCASLSen () -> a ->
                      IO([Proof_status ()])
cspCASLProverProve thName (Theory ccSign _) _freedefs = do
  -- Generate all theory files and then allow interactive proving on
  -- the main file.
  writeIsaTheory (thName ++ "_dataenc.thy") (produceDataEncoding ccSign)
  writeIsaTheory (thName ++ "_alphabet.thy") produceAlphabet
  writeIsaTheory (thName ++ "_integrationThms.thy") produceIntegrationTheorems
  writeIsaTheory (thName ++ "_processes.thy") produceProcesses
  isaProve thName produceProcessRefinements ()

-- | Produce the Isabelle theory of the data part of a CspCASL
-- | specification
produceDataEncoding :: CspCASLSign -> Theory Isa.Sign Isa.Sentence ()
produceDataEncoding _ = -- ccSign =
    let -- caslSign = ccSig2CASLSign ccSign
        -- Comorphisms
        -- casl2pcfol = (map_theory CASL2PCFOL.CASL2PCFOL)
        -- pcfol2cfol = (map_theory CASL2SubCFOL.defaultCASL2SubCFOL)
        -- cfol2isabelleHol = (map_theory CFOL2IsabelleHOL.CFOL2IsabelleHOL)
          -- Remove Subsorting from the CASL part of the CspCASL
          -- specification
        -- trans1 <- casl2pcfol (caslSign,[])
          -- Next Remove partial functions
        -- trans2 <- pcfol2cfol trans1
          -- Next Translate to IsabelleHOL code
        -- trans3 <- cfol2isabelleHol trans2
    in Theory Isa.emptySign Map.empty

-- | Produce the Isabelle theory which contains the Alphabet and
--   Justification Theorems
produceAlphabet :: Theory Isa.Sign Isa.Sentence ()
produceAlphabet = Theory Isa.emptySign Map.empty

-- | Produce the Isabelle theory which contains the Integration
--   Theorems on data
produceIntegrationTheorems :: Theory Isa.Sign Isa.Sentence ()
produceIntegrationTheorems = Theory Isa.emptySign Map.empty

-- | Produce the Isabelle theory which contains the Process
-- | Translations
produceProcesses :: Theory Isa.Sign Isa.Sentence ()
produceProcesses = Theory Isa.emptySign Map.empty

-- | Produce the Isabelle theory which contains the Data Theorems
--   place holder code and the Process Refinement theorems
produceProcessRefinements :: Theory Isa.Sign Isa.Sentence ()
produceProcessRefinements = Theory Isa.emptySign Map.empty
