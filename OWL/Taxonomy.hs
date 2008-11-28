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

module OWL.Taxonomy
    (
     onto2Tax
    )
    where

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

import qualified Control.Concurrent as Concurrent

import System.Exit
import System.IO
import System.Process
import System.Directory

import Control.Concurrent
import Control.Concurrent.MVar

import qualified Data.Foldable as Fold
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import Data.List

import qualified Data.Set as Set

-- | Derivation of an Taxonomy for OWL
onto2Tax :: TaxoGraphKind
         -> MMiSSOntology
         -> Sign -> [Named Sentence]
         -> Result MMiSSOntology
onto2Tax gk inOnto sig sens =
    case gk of
      KSubsort -> fail "Dear user, this logic is single sorted, sorry!"
      KConcept ->
          do
            cs <- unsafePerformIO $ runClassifier sig sens
            let tree = relBuilder cs
                subRel = Rel.transReduce $ foldl (\x y -> x `Rel.union` y)
                   Rel.empty tree
                superRel = Rel.irreflex $ Rel.transpose subRel
                superMap = Rel.toMap superRel
                classes  = Set.toList $ Set.map fst $ Rel.toSet subRel
            ontos <- makeMiss inOnto superMap classes
            return ontos

dropClutter :: [Char] -> [Char]
dropClutter a =
    case (stripPrefix "unamed:" a) of
      Nothing -> a
      Just b  -> b

-- | Generation of a MissOntology
makeMiss :: MMiSSOntology
            -> Map.Map String (Set.Set String)
            -> [String]
            -> Result MMiSSOntology
makeMiss o r s =
    do
      onto <- Fold.foldlM (\x y -> fromWithError $ insertClass x
                                   (dropClutter y) ""
                           (
                            case Map.lookup y r of
                              Nothing -> []
                              Just z  -> Set.toList $ Set.map dropClutter z
                           )
                           Nothing) o s
      return onto

-- | Builder for all relations
relBuilder :: String ->
               [Rel.Rel String]
relBuilder tr = map relBuild $
                 splitter $ map (tail) $ filter (/= []) $ lines tr

-- | splitter for output
splitter :: [String] -> [[String]]
splitter ls =
    case ls of
      []    -> []
      (h:t) ->
          let
              (l,r) = span (\x -> (head $ x) == ' ') t
          in
            [(h:l)] ++ splitter r

-- | builder for a single relation
relBuild :: [String]
          -> Rel.Rel String
relBuild s =
    case s of
      []     -> Rel.empty
      (t:ts) ->
          let
              nt = map (drop 3) ts
              children = splitter nt
          in
            let
                ch  = (foldl (\x y -> x `Rel.union` y) Rel.empty) $
                      map relBuild children
                suc = map head $ children
            in
              Rel.insert t t
              $ (Rel.fromList $ zip (repeat t) suc) `Rel.union` ch

-- | Invocation of Pellet
runClassifier :: Sign
              -> [Named Sentence]
              -> IO (Result String)
runClassifier sig sen =
    do
      let th      = show $ printOWLBasicTheory (sig, sen)
          options = "classify "
          tmpFile = "PelletClassifier"
          timeLimit = 800
      (proTh, propEx) <- check4Pellet
      case (proTh, propEx) of
        (True,True)  ->
            do
              t <- getCurrentTime
              tempDir <- getTemporaryDirectory
              let timeTmpFile = tempDir ++ "/" ++ tmpFile
                                ++ (show $ utctDay t) ++
                                "-" ++ (show $ utctDayTime t) ++ ".owl"
              writeFile timeTmpFile th
              let command = "sh pellet.sh "
                            ++ options
                            ++ timeTmpFile
              pPath     <- getEnvDef "PELLET_PATH" ""
              setCurrentDirectory(pPath)
              outState <- timeWatch timeLimit $
                (
                 do
                   (_, outh,_, proch) <- runInteractiveCommand command
                   exCode <- waitForProcess proch
                   ls <- hGetContents outh
                   case exCode of
                     ExitSuccess ->
                         do
                           return $ return ls
                     _           ->
                         do
                           return $ fail ls
                )
              return $ outState
        (True,False) -> do
          return $ fail "Pellet prover" "Pellet not executable"
        (False,_)    -> do
          return $ fail "Pellet prover" "Pellet not found"

-- | Time monitor
timeWatch :: Int
          -> IO (Result String)
          -> IO (Result String)
timeWatch time process =
    do
      mvar <- newEmptyMVar
      tid1 <- forkIO $ do z <- process
                          putMVar mvar (Just z)
      tid2 <- forkIO $ do threadDelay (time * 1000000)
                          putMVar mvar Nothing
      res <- takeMVar mvar
      case res of
        Just z -> do
                 killThread tid2 `catch` (\e -> putStrLn (show e))
                 return  z
        Nothing -> do
                 killThread tid1 `catch` (\e -> putStrLn (show e))
                 return $ fail "Time is up!"

-- | Checker if pellet is installed
check4Pellet :: IO (Bool, Bool)
check4Pellet =
    do
      pPath     <- getEnvDef "PELLET_PATH" ""
      progTh    <- doesFileExist $ pPath ++ "/pellet.sh"
      progEx <- if (progTh)
                 then
                     do
                       progPerms <- getPermissions $ pPath ++ "/pellet.sh"
                       return $ executable $ progPerms
                 else
                     return False
      return $ (progTh, progEx)
