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

import CspCASL.SignCSP (CspCASLSign, CspCASLSen, CspMorphism)

import Logic.Prover


import qualified Isabelle.IsaSign as Isa
-- import Isabelle.IsaConsts
import Isabelle.IsaPrint (getAxioms, printIsaTheory)
import Isabelle.IsaParse (parseTheory)
import Isabelle.Translate (transString)
import Isabelle.MarkSimp (markSimp, markThSimp)
import Isabelle.IsaProve (isaProve, prepareTheory)

import Common.AS_Annotation
-- import Common.DocUtils
-- import Common.DefaultMorphism
import Common.ProofUtils (prepareSenNames)
-- import Common.Utils (getEnvDef)
import qualified Data.Map as Map
-- import qualified Data.Set as Set

import Text.ParserCombinators.Parsec (parse)
-- import Data.Char
-- import Data.List (isSuffixOf)
-- import Control.Monad

-- import System.Directory
-- import System.Exit
-- import System.Cmd

-- | The string that Hets uses as CspCASLProver
cspCASLProverS :: String
cspCASLProverS = "CspCASLProver"

-- openCspCASLProof_status :: String -> Proof_status ()
-- openCspCASLProof_status n = openProof_status n cspCASLProverS ()

-- | The wrapper function that is CspCASL Prover
cspCASLProver :: Prover CspCASLSign CspCASLSen CspMorphism () ()
cspCASLProver = mkProverTemplate cspCASLProverS () cspCASLProverProve

-- mkIsaTheory :: Theory CspCASLSign CspCASLSen () -> Theory Isa.Sign Isa.Sentence ()
-- mkIsaTheory (Theory sig nSens) = Theory Isa.emptySign Map.empty

-- | The main cspCASLProver function
cspCASLProverProve :: String -> Theory CspCASLSign CspCASLSen () -> a -> IO([Proof_status ()])
cspCASLProverProve thName ccTh _freedefs = do
    -- We can use this to do the proof on the final file - but first
    -- we need to generate the other 4 files - 1 for each part
    let isaThy = Theory Isa.emptySign Map.empty
    writeIsaTheory "liamtest" isaThy
    isaProve thName isaThy ()

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
    Right (ho, bo) -> do
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
      putStrLn $ "Sorry, a generated theory cannot be parsed, see: " ++ thyFile
      writeFile thyFile thy
      putStrLn "Aborting Isabelle proof attempt"
      return ()