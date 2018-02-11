{- |
Module      :  ./OWL2/Taxonomy.hs
Description :  Taxonomy extraction for OWL
Copyright   :  (c) Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portabl

Taxonomy extraction for OWL
-}

module OWL2.Taxonomy ( onto2Tax ) where

import OWL2.MS
import OWL2.Sign
import OWL2.ManchesterPrint
import OWL2.ProvePellet

import Common.AS_Annotation
import Common.Result
import Taxonomy.MMiSSOntology
import Common.Taxonomy
import Common.Utils

import System.IO.Unsafe

import qualified Data.Foldable as Fold
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import Data.List
import Data.Maybe

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
        classes = Set.toList $ Set.map fst $ Rel.toSet subRel
    makeMiss inOnto superMap classes

dropClutter :: String -> String
dropClutter = tryToStripPrefix "unamed:"

-- | Generation of a MissOntology
makeMiss :: MMiSSOntology
         -> Map.Map String (Set.Set String)
         -> [String]
         -> Result MMiSSOntology
makeMiss o r =
  Fold.foldlM (\ x y -> fromWithError $ insertClass x (dropClutter y) ""
                (case Map.lookup y r of
                   Nothing -> []
                   Just z -> Set.toList $ Set.map dropClutter z
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
  [] -> []
  (h : t) -> let (l, r) = span (\ x -> head x == ' ') t in (h : l) : splitter r

-- | builder for a single relation
relBuild :: [String]
         -> Rel.Rel String
relBuild s = case s of
  [] -> Rel.empty
  (t : ts) ->
    let nt = map (drop 3) ts
        children = splitter nt
        ch = foldl Rel.union Rel.empty $ map relBuild children
        suc = map head children
    in Rel.insertKey t $ Rel.fromList (zip (repeat t) suc) `Rel.union` ch

-- | Invocation of Pellet
runClassifier :: Sign -> [Named Axiom] -> IO (Result String)
runClassifier sig sen = do
  let th = show $ printOWLBasicTheory (sig, filter isAxiom sen)
      tLimit = 800
  res <- runTimedPellet "classify" "PelletClassifier" th Nothing tLimit
  return $ case res of
    Nothing -> fail $ "Timeout after " ++ show tLimit ++ " seconds!"
    Just (progTh, out, _) ->
      if progTh then return out else fail "Pellet not found"
