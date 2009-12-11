{- |
Module      :  $Header$
Description :  Taxonomy extraction for OWL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portabl

Taxonomy extraction for OWL
-}

module OWL.Taxonomy ( onto2Tax ) where

import OWL.AS
import OWL.Sign
import OWL.Print

import Common.AS_Annotation
import Common.Result
import Taxonomy.MMiSSOntology
import Common.Taxonomy

import System.IO.Unsafe

import Common.Utils

import Data.Time ()
import Data.Time.Clock (UTCTime(..), getCurrentTime)

import System.Exit
import System.IO
import System.Directory

import qualified Data.Foldable as Fold
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import Data.List

import qualified Data.Set as Set

-- | Derivation of an Taxonomy for OWL
onto2Tax :: TaxoGraphKind
         -> MMiSSOntology
         -> Sign -> [Named Axiom]
         -> Result MMiSSOntology
onto2Tax gk inOnto sig sens = case gk of
  KSubsort -> fail "Dear user, this logic is single sorted, sorry!"
  KConcept -> do
    cs <- unsafePerformIO $ runClassifier sig sens
    tree <- relBuilder cs
    let subRel = Rel.transReduce $ foldl Rel.union Rel.empty tree
        superRel = Rel.irreflex $ Rel.transpose subRel
        superMap = Rel.toMap superRel
        classes  = Set.toList $ Set.map fst $ Rel.toSet subRel
    makeMiss inOnto superMap classes

dropClutter :: String -> String
dropClutter a = case (stripPrefix "unamed:" a) of
  Nothing -> a
  Just b  -> b

-- | Generation of a MissOntology
makeMiss :: MMiSSOntology
         -> Map.Map String (Set.Set String)
         -> [String]
         -> Result MMiSSOntology
makeMiss o r =
  Fold.foldlM (\x y -> fromWithError $ insertClass x (dropClutter y) ""
                (case Map.lookup y r of
                   Nothing -> []
                   Just z  -> Set.toList $ Set.map dropClutter z
                ) Nothing) o

-- | Builder for all relations
relBuilder :: String
           -> Result [Rel.Rel String]
relBuilder tr =
  let ln = filter (not . null) $ lines tr in
  if any (isPrefixOf "ERROR: ") ln || null ln then
    fail "Classification via Pellet failed! Ontology might be inconsistent!"
    else return $ map relBuild $ splitter $ map tail ln

-- | splitter for output
splitter :: [String] -> [[String]]
splitter ls = case ls of
  []    -> []
  (h:t) -> let (l,r) = span (\x -> head x == ' ') t in (h:l) : splitter r

-- | builder for a single relation
relBuild :: [String]
         -> Rel.Rel String
relBuild s = case s of
  []     -> Rel.empty
  (t:ts) ->
    let nt = map (drop 3) ts
        children = splitter nt
        ch  = foldl Rel.union Rel.empty $ map relBuild children
        suc = map head children
    in Rel.insert t t $ Rel.fromList (zip (repeat t) suc) `Rel.union` ch

-- | Invocation of Pellet
runClassifier :: Sign -> [Named Axiom] -> IO (Result String)
runClassifier sig sen = do
  let th      = show $ printOWLBasicTheory (sig, filter isAxiom sen)
      options = "classify "
      tmpFile = "PelletClassifier"
      timeLimit = 800
  (proTh, propEx) <- check4Pellet
  case (proTh, propEx) of
    (True,True) -> do
      t <- getCurrentTime
      tempDir <- getTemporaryDirectory
      let timeTmpFile = tempDir ++ "/" ++ tmpFile ++ show (utctDay t) ++ "-"
                                ++ show (utctDayTime t) ++ ".owl"
          command = "sh pellet.sh " ++ options ++ timeTmpFile
      writeFile timeTmpFile th
      pPath <- getEnvDef "PELLET_PATH" ""
      setCurrentDirectory pPath
      (mExit, outh,_) <- timeoutCommand timeLimit command
      outState <- case mExit of
        Just exCode -> do
          ls <- hGetContents outh
          case exCode of
            ExitSuccess -> return $ return ls
            _           -> return $ fail ls
        Nothing -> return $ fail "Time is up!"
      removeFile timeTmpFile
      return outState
    (True,False) -> return $ fail "Pellet prover" "Pellet not executable"
    (False,_)    -> return $ fail "Pellet prover" "Pellet not found"

-- | Checker if pellet is installed
check4Pellet :: IO (Bool, Bool)
check4Pellet = do
  pPath <- getEnvDef "PELLET_PATH" ""
  let path = pPath ++ "/pellet.sh"
  progTh <- doesFileExist path
  progEx <- if progTh then do
      progPerms <- getPermissions path
      return $ executable progPerms
    else return False
  return (progTh, progEx)
