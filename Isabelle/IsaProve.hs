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
  ex <- doesFileExist fileName
  exorig <- doesFileExist origName
  case (ex,exorig) of
    (True,True) -> do 
             putStrLn ("diff -u "++origName++" "++fileName++" > "++patchName)
             system ("diff -u "++origName++" "++fileName++" > "++patchName)
             writeFile fileName showTheory 
             putStrLn ("cp "++fileName++" "++origName)
             system ("cp "++fileName++" "++origName)
             putStrLn ("patch -u "++fileName++" "++patchName)
             system ("patch -u "++fileName++" "++patchName)
             return ()
    (True,False) -> do
             system ("cp "++fileName++" "++fileName++".old")
             writeFile fileName showTheory 
             system ("cp "++fileName++" "++origName)
             return ()
    (False,_) -> do
             writeFile fileName showTheory 
             system ("cp "++fileName++" "++origName)
             return ()
  isa <- newChildProcess "/home/linux-bkb/bin/Isabelle" [arguments ({-["/home/cofi/sonja/HetCATS/Comorphisms/MainHC.thy"]++ -} [fileName])]
--  writeFile (thName++".thy") (showTheory (writeTo isa))
  msgs <- readProofs isa
  closeChildProcessFds isa
  return [] -- ??? to be implemented
  where
      disAxs = disambiguateSens [] $ nameSens $ transSens axs
      showLemma = concat $ map ((++"\n") . formLemmas) disAxs
      showAxs = concat $ map ((++"\n") . showSen) disAxs
      disGoals = disambiguateSens disAxs $ nameSens $ transSens goals
      showGoals = concat 
         $ map showGoal disGoals
      getFileName = reverse . fst . break (=='/') . reverse
      showGoal goal = (("theorem "++) . -- (++(ipc (show fd) (senName goal))) .
                      (++"\noops\n") . showSen) goal
      showTheory = "theory " ++ getFileName thName ++ " = " 
                   ++ showPretty sig "\n\naxioms\n" 
                   ++ showAxs ++ "\n" ++ showLemma ++ "\n\n" ++ showGoals --fd
                   ++ "\nend\n"
      -- ipc fd thmName = "\nML \" writeArr("++ fd ++ ", {Pretty.string_of(pretty_proof_of \""++ thmName ++"\") , 0, None})\"\n\n"

readProofs :: ChildProcess -> IO [String]
readProofs = rP []

rP :: [String] -> ChildProcess -> IO [String]
rP s cp = do
  msg <- readMsg cp
  case msg of
     "EOF" -> return s
     _ -> rP (s++[msg]) cp

-- translate special characters in sentence names
transSens :: [Named a] -> [Named a]
transSens = map (\ax -> ax{senName = transString $ senName ax})

-- disambiguate sentence names
disambiguateSens :: [Named a] -> [Named a] -> [Named a]
disambiguateSens others axs = reverse $ disambiguateSensAux others axs []
disambiguateSensAux others [] soFar = soFar
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
showSen x =  (if null (senName x) then "" 
                else senName x++": ")
             ++ "\""++showPretty (sentence x) "\""

-- name unlabeled axioms with "Axnnn"
nameSens :: [Named a] -> [Named a]
nameSens sens = 
  map nameSen (zip sens [1..length sens])
  where nameSen (sen,no) = if senName sen == "" 
                              then sen{senName = "Ax"++show no}
                              else sen

-- form a lemmas from given axiom and add them both to Isabelles simplifier
formLemmas :: Named a -> String
formLemmas sen = 
  let (sn, ln) = lemmaName (senName sen)
   in
     "lemmas " ++ ln ++ " = " ++ sn ++ " [simplified]\n" ++
     dec ln ++ "\n" ++ dec sn
  where 
  lemmaName s = (s, s++"a")
  dec s = "declare " ++ s ++ "[simp]"
