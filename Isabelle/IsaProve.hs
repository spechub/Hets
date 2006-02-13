{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Interface for Isabelle theorem prover.
-}
{-
  todo: thy files in subdir, check of legal changes in thy file
   consistency check
   check if goalUsedInProof is can be derived from isabelle's proof tree

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

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.ProofUtils
import Common.PrettyPrint
import qualified Common.Lib.Map as Map

import Text.ParserCombinators.Parsec

import Driver.Options

import Data.Char
import Control.Monad

import System.Directory
import System.Environment
import System.Exit
import System.Cmd

isabelleS :: String
isabelleS = "Isabelle"

isabelleProver :: Prover Sign Sentence ()
isabelleProver =
     Prover { prover_name = isabelleS,
              prover_sublogic = isabelleS,
              prove = isaProve
            }

isabelleConsChecker :: ConsChecker Sign Sentence (DefaultMorphism Sign) ()
isabelleConsChecker =
     Prover { prover_name = "Isabelle-refute",
              prover_sublogic = isabelleS,
              prove = consCheck }

openIsaProof_status :: String -> Proof_status ()
openIsaProof_status n =
    ((openProof_status n (prover_name isabelleProver))::Proof_status ())
    {proofTree = ()}

-- | the name of the inconsistent lemma for consistency checks
inconsistentS :: String
inconsistentS = "inconsistent"

consCheck :: String -> TheoryMorphism Sign Sentence (DefaultMorphism Sign) ()
          -> IO([Proof_status ()])
consCheck thName tm = case t_target tm of
    Theory sig nSens -> let (axs, _) = getAxioms $ toNamedList nSens in
       isaProve (thName ++ "_c") $
           Theory emptySign { baseSig = baseSig sig }
               $ markAsGoal $ toThSens $ if null axs then [] else
                   [ (emptyName $ mkRefuteSen $ termAppl notOp
                     $ foldr1 binConj $ map (senTerm . sentence) axs)
                     { senName = inconsistentS } ]

prepareTheory :: Theory Sign Sentence ()
    -> (Sign, [Named Sentence], [Named Sentence], Map.Map String String)
prepareTheory (Theory sig nSens) = let
    oSens = toNamedList nSens
    nSens' = prepareSenNames transString oSens
    (disAxs, disGoals) = getAxioms nSens'
    in (sig, map markSimp disAxs, map markSimp disGoals,
       Map.fromList $ zip (map senName nSens') $ map senName oSens)
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
    b <- checkInFile file
    if b then do
        s <- readFile file
        let l = filter (not . null) $ map strip $ lines s
        return $ mkProved (mapN thm) $ map mapN l
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
            mapM_ (\ d -> putStrLn $ showPretty d "") ds
            if hb /= ho then do
                  putStrLn "illegal change of theory header"
                  return False
              else return $ null ds
    Left err -> putStrLn (show err) >> return False

mkProved :: String -> [String] -> Proof_status ()
mkProved thm used = (openIsaProof_status thm)
    { goalStatus = Proved
    , usedAxioms = used
    , goalUsedInProof = True
    , tacticScript = Tactic_script "unknown isabelle user input"
    }

prepareThyFiles :: (TheoryHead, Body) -> String -> String -> IO ()
prepareThyFiles ast thyFile thy = do
    let origFile = thyFile ++ ".orig"
    exOrig <- checkInFile origFile
    exThyFile <- checkInFile thyFile
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
      patchCall = "patch -fu " ++ thyFile ++ " " ++ patchFile
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
            mapM_ (\ d -> putStrLn $ showPretty d "") ds
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

isaProve :: String -> Theory Sign Sentence () -> IO([Proof_status ()])
isaProve thName th = do
  let (sig, axs, ths, m) = prepareTheory th
      thms = map senName ths
  hlibdir <- getEnv "HETS_LIB"
  let thBaseName = reverse . takeWhile (/= '/') $ reverse thName
      thy = shows (printIsaTheory thBaseName hlibdir sig $ axs ++ ths) "\n"
      thyFile = thName ++ ".thy"
  case parse parseTheory thyFile thy of
    Right (ho, bo) -> do
      prepareThyFiles (ho, bo) thyFile thy
      removeDepFiles thName thms
      isabelleEnv <- getEnv "HETS_ISABELLE"
      let isabelle = if null isabelleEnv then "Isabelle" else isabelleEnv
      callSystem $ isabelle ++ " " ++ thyFile
      ok <- checkFinalThyFile (ho, bo) thyFile
      if ok then getAllProofDeps m thName thms
          else return []
    Left err -> do
      putStrLn $ show err
      putStrLn $ "Sorry, generated theory cannot be parsed, see: " ++ thyFile
      writeFile thyFile thy
      putStrLn "aborting Isabelle proof attempt"
      return []

markSimp :: Named Sentence -> Named Sentence
markSimp = mapNamed markSimpSen

markSimpSen :: Sentence -> Sentence
markSimpSen s = case s of
                  Sentence {} -> s {isSimp = isSimpRuleSen s}
                  _ -> s

isSimpRuleSen :: Sentence -> Bool
isSimpRuleSen sen = case sen of
    RecDef {} -> False
    _ -> isSimpRule $ senTerm sen

-- | test whether a formula should be put into the simpset
isSimpRule :: Term -> Bool
-- only universal quantifications
isSimpRule App { funId = Const {termName = VName { new = q }}
               , argId = arg@Abs{}}
    | q == exS || q == ex1S = False
    | q == allS             = isSimpRule (termId arg)
-- accept everything expect from abstractions
isSimpRule App {funId = arg1, argId = arg2} =
    isSimpRule arg1 && isSimpRule arg2
isSimpRule MixfixApp {funId = arg1, argIds = args } =
    isSimpRule arg1 && all isSimpRule args
isSimpRule Const{} = True
isSimpRule Free{}  = True
isSimpRule Var{}   = True
isSimpRule Bound{} = True
isSimpRule Abs{}   = False
isSimpRule If{}    = True
isSimpRule Case{}  = True
isSimpRule Let{}   = True
isSimpRule (Paren t) = isSimpRule t
isSimpRule _       = False
