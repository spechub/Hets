{-# OPTIONS -cpp #-}

{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Interface for Isabelle theorem prover.
-}
{-
  todo: thy files in subdir
  
  Interface between Isabelle and Hets:
  Hets writes Isabelle .thy file and opens window with button (GUI/HTkUtils.hs, uni/htk/test, ask cxl)
  User extends .thy file with proofs
  User presses button
  Hets reads in user-modified .thy file
  Hets write new .thy file (different name), consisting of
    - original theory (i.e. put theory string into variable)
    - proof part of user-modified file (look for first "\ntheorem")
    - ML code for check_theorem
    - ML "check_theorem \"name1\" \"theorem1\" name.thy"   (name: thName)
      ...
    - ML "check_theorem \"namen\" "\theoremn\" name.thy"
  Hets runs new .thy file in Isar batch mode (system " .... ")
  Hets inspects log file and extracts proven theorems

  fun check_theorem name thm thy =
    aconv(#prop(rep_thm(Drule.freeze_all(get_thm thy name))), snd(read_axm (sign_of thy) (name,thm)))
    handle _ => false;
-}

module Isabelle.IsaProve where

import Logic.Prover
import Isabelle.IsaSign
import Isabelle.IsaPrint

import Common.AS_Annotation
import Common.PrettyPrint

import Data.List
import Data.Maybe

import Configuration

import System.Posix.IO
import ChildProcess
import Directory
import System

import HTk

import Debug.Trace

isabelleProver :: Prover Sign Sentence () ()
isabelleProver =
     Prover { prover_name = "Isabelle",
              prover_sublogic = "Isabelle",
              prove = isaProve
            }

                 -- input: theory name, theory, goals
                 -- output: proof status for goals and lemmas
isaProve :: String -> (Sign,[Named Sentence]) -> [Named Sentence] 
              -> IO([Proof_status Sentence ()])
isaProve thName (sig,axs) goals = do
  let fileName = thName++".thy"
      origName = thName++".orig.thy"
      patchName = thName++".patch"
      proofedName = thName++".proofed.thy"
      theory = showTheory
  ex <- doesFileExist fileName
  exorig <- doesFileExist origName
  case (ex,exorig) of
    (True,True) -> do 
             putStrLn ("diff -u "++origName++" "++fileName++" > "++patchName)
             system ("diff -u "++origName++" "++fileName++" > "++patchName)
             writeFile fileName theory 
             putStrLn ("cp "++fileName++" "++origName)
             system ("cp "++fileName++" "++origName)
             putStrLn ("patch -u "++fileName++" "++patchName)
             system ("patch -u "++fileName++" "++patchName)
             return ()
    (True,False) -> do
             system ("cp "++fileName++" "++fileName++".old")
             writeFile fileName theory 
             system ("cp "++fileName++" "++origName)
             return ()
    (False,_) -> do
             writeFile fileName theory 
             system ("cp "++fileName++" "++origName)
             return ()
  isabelle <- getEnv "HETS_ISABELLE"
  isa <- newChildProcess (isabelle ++ "/Isabelle") [arguments [fileName]]
  htk <- initHTk [withdrawMainWin]
  t <- createToplevel [text "Proof confirmation window"]
  b <- newButton t [text "Please press me when current theory is proofed!",size(50,10)]
  pack b []
  clickedb <- clicked b
  spawnEvent (clickedb >>> destroy htk)
  finishHTk
  closeChildProcessFds isa
  proofedThy <- readFile fileName
  let newThy = withoutThms theory ++ onlyThms proofedThy ++ checkThm ++ concat (map checkThms disGoals)
  writeFile proofedName newThy
--   system (isabelle ++ "/isabelle -e "++newThy++" -q HOL" ++ " heap.isa")
  return [] -- ??? to be implemented
  where
      disAxs = disambiguateSens [] $ nameSens $ transSens axs
      (lemmas, decs) = unzip (map formLemmas disAxs)
      showLemma = if showLemmas sig 
                   then concat lemmas ++ "\n" ++ concat (map (++"\n") decs)
                   else ""
      showAxs = concat $ map ((++"\n") . showSen) disAxs
      disGoals = disambiguateSens disAxs $ nameSens $ transSens goals
      showGoals = concat $ map showGoal disGoals
      getFN = reverse . fst . break (=='/') . reverse
      showGoal goal = (("theorem "++) .  (++"\noops\n") . showSen) goal
      showTheory = thyPath
                   ++ "theory " ++ getFN thName ++ " = " 
                   ++ showPretty sig "\n\naxioms\n" 
                   ++ showAxs ++ "\n" ++ showLemma ++ "\n\n" ++ showGoals
                   ++ "\nend\n"
      withoutThms thy = (unlines . takeWhile (isNotPrefixOf "theorem")) (lines thy)
      onlyThms thy = (unlines . dropWhile (isNotPrefixOf "theorem")) (lines thy)
      isNotPrefixOf t s = (not . (isPrefixOf t)) s
      checkThm = "\n\nML  \"fun check_theorem name thm thy = "
                 ++ "aconv(#prop(rep_thm(Drule.freeze_all(get_thm thy name))),"
                 ++ "snd(read_axm (sign_of thy) (name,thm))) handle _ => false;\"\n\n"
      checkThms thm = "ML \"check_theorem \\\"" 
                      ++ senName thm ++ "\\\" " 
                      ++ "\\\""++showPretty (sentence thm) "\\\" " 
                      ++ thName ++ ".thy \"\n"
      thyPath = "ML \"val hetsLib = (OS.Process.getEnv \\\"HETS_LIB\\\"); \n"
                   ++ "case hetsLib of NONE => add_path \\\".\\\" \n"
                   ++ "| SOME s => add_path (s ^ \\\"/Isabelle\\\")\"\n\n"

-- translate special characters in sentence names
transSens :: [Named a] -> [Named a]
transSens = map (\ax -> ax{senName = transString $ senName ax})

-- disambiguate sentence names
disambiguateSens :: [Named a] -> [Named a] -> [Named a]
disambiguateSens others axs = reverse $ disambiguateSensAux others axs []

disambiguateSensAux :: [Named a] -> [Named a] -> [Named a] -> [Named a]
disambiguateSensAux _ [] soFar = soFar
disambiguateSensAux others (ax:rest) soFar =
  disambiguateSensAux (ax':others) rest (ax':soFar)
  where
  name' = fromJust $ find (not . flip elem namesSoFar) 
                          (name:[name++show i | i<-[1..]])
  name = senName ax 
  namesSoFar = map senName others
  ax' = ax{senName = name'}


-- output a sentences
showSen :: PrettyPrint a => Named a -> String
showSen s =  (if null (senName s) then "" 
                else senName s++": ")
             ++ "\""++showPretty (sentence s) "\""

-- name unlabeled axioms with "Axnnn"
nameSens :: [Named a] -> [Named a]
nameSens sens = 
  map nameSen (zip sens [1..length sens])
  where nameSen (sen,no) = if senName sen == "" 
                              then sen{senName = "Ax"++show no}
                              else sen

-- form a lemmas from given axiom and add them both to Isabelles simplifier
formLemmas :: Named a -> (String, String)
formLemmas sen = 
  let (sn, ln) = lemmaName (senName sen)
   in
     ("lemmas " ++ ln ++ " = " ++ sn ++ " [simplified]\n",
      dec ln ++ "\n" ++ dec sn)
  where 
  lemmaName s = (s, s++"'")
  dec s = "declare " ++ s ++ " [simp]"
