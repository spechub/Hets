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

import Debug.Trace

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
onto2Tax _ inOnto sig sens =
    do
      cs <- unsafePerformIO $ runClassifier sig sens
      let tree = treeBuilder cs
          subRel = foldl (\x y -> x `Rel.union` y) Rel.empty $
                   map tree2assocs tree
          superRel = Rel.transpose subRel
          superMap = Rel.toMap superRel
          classes  = nub $ concat $ map getClasses tree
      ontos <- trace (show subRel) $ makeMiss inOnto superMap classes
      return ontos

data Tree a = Empty | Node a [Tree a]
            deriving (Eq, Ord, Show)

makeMiss :: MMiSSOntology
            -> Map.Map String (Set.Set String)
            -> [String]
            -> Result MMiSSOntology
makeMiss o r s =
    do
      onto <- Fold.foldlM (\x y -> fromWithError $ insertClass x y ""
                           (
                            case Map.lookup y r of
                              Nothing -> []
                              Just z  -> Set.toList z
                           )
                           Nothing) o s
      return onto

getClasses :: Tree String -> [String]
getClasses t =
    case t of
      Empty     -> []
      Node a [] -> a:[]
      Node a ts -> a:(concat $ map getClasses ts)

childreN :: t -> Tree t1 -> [(t, t1)]
childreN a t =
    case t of
      Empty     -> []
      Node b _  -> [(a,b)]

tree2assocs :: Tree String -> Rel.Rel String
tree2assocs t =
    case t of
      Empty     -> Rel.empty
      Node _ [] -> Rel.empty
      Node a ts -> (Rel.fromList $ concat $ map (childreN a) ts)
                   `Rel.union` (foldl (\x y -> (tree2assocs y)
                                       `Rel.union` x) Rel.empty ts)

treeBuilder :: String ->
               [Tree String]
treeBuilder tr = map treeBuild $
                 splitter $ map (tail) $ filter (/= []) $ lines tr

splitter :: [String] -> [[String]]
splitter ls =
    case ls of
      []    -> []
      (h:t) ->
          let
              (l,r) = span (\x -> (head $ x) == ' ') t
          in
            [(h:l)] ++ splitter r

treeBuild :: [String]
          -> Tree String
treeBuild s =
    case s of
      []     -> Empty
      (t:ts) ->
          let
              nt = map (drop 3) ts
              children = splitter nt
          in
            Node t (map treeBuild children)

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
