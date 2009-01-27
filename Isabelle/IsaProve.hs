{- |
Module      :  $Header$
Description :  interface to the Isabelle theorem prover
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Interface for Isabelle theorem prover.
-}
{-
  Interface between Isabelle and Hets:
   Hets writes Isabelle .thy file and starts Isabelle
   User extends .thy file with proofs
   User finishes Isabelle
   Hets reads in created *.deps files
-}

module Isabelle.IsaProve where

import Logic.Prover
import Isabelle.IsaSign
import Isabelle.IsaConsts
import Isabelle.IsaPrint
import Isabelle.IsaParse
import Isabelle.Translate
import Isabelle.MarkSimp

import Common.AS_Annotation
import Common.DocUtils
import Common.DefaultMorphism
import Common.ProofUtils
import Common.Utils (getEnvDef)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec
import Data.Char
import Data.List (isSuffixOf)
import Control.Monad

import System.Directory
import System.Exit
import System.Cmd

isabelleS :: String
isabelleS = "Isabelle"

openIsaProof_status :: String -> Proof_status ()
openIsaProof_status n = openProof_status n isabelleS ()

isabelleProver :: Prover Sign Sentence (DefaultMorphism Sign) () ()
isabelleProver = mkProverTemplate isabelleS () isaProve

isabelleConsChecker :: ConsChecker Sign Sentence () (DefaultMorphism Sign) ()
isabelleConsChecker = mkProverTemplate "Isabelle-refute" () consCheck

-- | the name of the inconsistent lemma for consistency checks
inconsistentS :: String
inconsistentS = "inconsistent"

metaToTerm :: MetaTerm -> Term
metaToTerm mt = case mt of
  Term t -> t
  Conditional ts t -> case ts of
    [] -> t
    _ -> binImpl (foldr1 binConj ts) t

consCheck :: String -> TheoryMorphism Sign Sentence (DefaultMorphism Sign) ()
          -> a -> IO([Proof_status ()])
consCheck thName tm freedefs = case t_target tm of
    Theory sig nSens -> let (axs, _) = getAxioms $ toNamedList nSens in
       isaProve (thName ++ "_c")
           (Theory sig
               $ markAsGoal $ toThSens $ if null axs then [] else
                   [ makeNamed inconsistentS $ mkRefuteSen $ termAppl notOp
                     $ foldr1 binConj
                     $ map (metaToTerm . metaTerm . sentence) axs ])
           freedefs

prepareTheory :: Theory Sign Sentence ()
    -> (Sign, [Named Sentence], [Named Sentence], Map.Map String String)
prepareTheory (Theory sig nSens) = let
    oSens = toNamedList nSens
    nSens' = prepareSenNames transString oSens
    (disAxs, disGoals) = getAxioms nSens'
    in (sig, map markSimp disAxs, map markThSimp disGoals,
       Map.fromList $ zip (map senAttr nSens') $ map senAttr oSens)
-- return a reverse mapping for renamed sentences

removeDepFiles :: String -> [String] -> IO ()
removeDepFiles thName = mapM_ $ \ thm -> do
  let depFile = getDepsFileName thName thm
  ex <- doesFileExist depFile
  when ex $ removeFile depFile

getDepsFileName :: String -> String -> String
getDepsFileName thName thm = thName ++ "_" ++ thm ++ ".deps"

getProofDeps :: Map.Map String String -> String -> String
             -> IO (Proof_status ())
getProofDeps m thName thm = do
    let file = getDepsFileName thName thm
        mapN n = Map.findWithDefault n n m
        strip = takeWhile (not . isSpace) . dropWhile isSpace
    b <- doesFileExist file
    if b then do
        s <- readFile file
        return $ mkProved (mapN thm) $ map mapN $
               Set.toList $ Set.filter (not . null) $
               Set.fromList $ map strip $ lines s
      else return $ openIsaProof_status $ mapN thm

getAllProofDeps :: Map.Map String String -> String -> [String]
                -> IO([Proof_status ()])
getAllProofDeps m thName = mapM $ getProofDeps m thName

checkFinalThyFile :: (TheoryHead, Body) -> String -> IO Bool
checkFinalThyFile (ho, bo) thyFile = do
  s <- readFile thyFile
  case parse parseTheory thyFile s of
    Right (hb, b) -> do
            let ds = compatibleBodies bo b
            mapM_ (\ d -> putStrLn $ showDoc d "") $ ds ++ warnSimpAttr b
            if hb /= ho then do
                  putStrLn "illegal change of theory header"
                  return False
              else return $ null ds
    Left err -> putStrLn (show err) >> return False

mkProved :: String -> [String] -> Proof_status ()
mkProved thm used = (openIsaProof_status thm)
    { goalStatus = Proved Nothing
    , usedAxioms = used
    , tacticScript = Tactic_script "unknown isabelle user input"
    }

prepareThyFiles :: (TheoryHead, Body) -> String -> String -> IO ()
prepareThyFiles ast thyFile thy = do
    let origFile = thyFile ++ ".orig"
    exOrig <- doesFileExist origFile
    exThyFile <- doesFileExist thyFile
    if exOrig then return () else writeFile origFile thy
    if exThyFile then return () else writeFile thyFile thy
    thy_time <- getModificationTime thyFile
    orig_time <- getModificationTime origFile
    s <- readFile origFile
    unless (thy_time >= orig_time && s == thy)
      $ patchThyFile ast origFile thyFile thy

patchThyFile :: (TheoryHead, Body) -> FilePath -> FilePath -> String -> IO ()
patchThyFile (ho, bo) origFile thyFile thy = do
  let patchFile = thyFile ++ ".patch"
      oldFile = thyFile ++ ".old"
      diffCall = "diff -u " ++ origFile ++ " " ++ thyFile
                 ++ " > " ++ patchFile
      patchCall = "patch -bfu " ++ thyFile ++ " " ++ patchFile
  callSystem diffCall
  renameFile thyFile oldFile
  removeFile origFile
  writeFile origFile thy
  writeFile thyFile thy
  callSystem patchCall
  s <- readFile thyFile
  case parse parseTheory thyFile s of
    Right (hb, b) -> do
            let ds = compatibleBodies bo b
                h = hb == ho
            mapM_ (\ d -> putStrLn $ showDoc d "") ds
            unless h $ putStrLn "theory header is corrupt"
            unless (h && null ds) $ revertThyFile thyFile thy
    Left err -> do
      putStrLn $ show err
      revertThyFile thyFile thy

revertThyFile :: String -> String -> IO ()
revertThyFile thyFile thy = do
    putStrLn $ "replacing corrupt file " ++ show thyFile
    removeFile thyFile
    writeFile thyFile thy

callSystem :: String -> IO ExitCode
callSystem s = putStrLn s >> system s

isaProve :: String -> Theory Sign Sentence () -> a -> IO([Proof_status ()])
isaProve thName th _freedefs = do
  let (sig, axs, ths, m) = prepareTheory th
      thms = map senAttr ths
      thBaseName = reverse . takeWhile (/= '/') $ reverse thName
      useaxs = filter (\ s ->
            sentence s /= mkSen true && (isDef s ||
               isSuffixOf "def" (senAttr s))) axs
      defaultProof = Just $ IsaProof
        (if null useaxs then [] else [Using $ map senAttr useaxs])
        $ By Auto
      thy = shows (printIsaTheory thBaseName sig
        $ axs ++ map (mapNamed $ \ t -> case t of
           Sentence { thmProof = Nothing } -> t { thmProof = defaultProof }
           _ -> t) ths)
        "\n"
      thyFile = thBaseName ++ ".thy"
  case parse parseTheory thyFile thy of
    Right (ho, bo) -> do
      prepareThyFiles (ho, bo) thyFile thy
      removeDepFiles thBaseName thms
      isabelle <- getEnvDef "HETS_ISABELLE" "Isabelle"
      callSystem $ isabelle ++ " " ++ thyFile
      ok <- checkFinalThyFile (ho, bo) thyFile
      if ok then getAllProofDeps m thBaseName thms
          else return []
    Left err -> do
      putStrLn $ show err
      putStrLn $ "Sorry, generated theory cannot be parsed, see: " ++ thyFile
      writeFile thyFile thy
      putStrLn "aborting Isabelle proof attempt"
      return []
