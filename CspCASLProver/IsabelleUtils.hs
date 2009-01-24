{- |
Module      :  $Header$
Description :  Utilities for CspCASLProver related to Isabelle
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
               Swansea University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Utilities for CspCASLProver related to Isabelle. The functions here
typically manipulate Isabelle signatures.
-}

module CspCASLProver.IsabelleUtils
    ( updateDomainTab
    , writeIsaTheory
    ) where

import Isabelle.IsaParse (parseTheory)
import Isabelle.IsaPrint (printIsaTheory)
import Isabelle.IsaProve (prepareTheory)
import Isabelle.IsaSign  (DomainEntry, Sentence, Sign(..))

import Logic.Prover (Theory)

import Text.ParserCombinators.Parsec (parse)

-- | Add a DomainEntry to the domain tab of an Isabelle signature.
updateDomainTab :: DomainEntry  -> Sign -> Sign
updateDomainTab domEnt isaSign =
    let oldDomTab = domainTab isaSign
        isaSignUpdated = isaSign {domainTab = (oldDomTab ++ [[domEnt]])}
    in isaSignUpdated

-- | Write out an Isabelle Theory. The theory should just run through
--   in Isabelle without any user interactions. This is based heavily
--   off Isabelle.IsaProve.isaProve
writeIsaTheory :: String -> Theory Sign Sentence () -> IO ()
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
      thyFile = thBaseName ++ ".thy"
  -- Check if the Isabelle theory is a valid Isabelle theory
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
    -- The Isabelle theory is not a valid theory (according to Hets)
    -- as it cannot be parsed.
    Left err -> do
      putStrLn $ show err
      putStrLn $ "Sorry, a generated theory cannot be parsed, see: "
                   ++ thyFile
      writeFile thyFile thy
      putStrLn "Aborting Isabelle proof attempt"
      return ()
