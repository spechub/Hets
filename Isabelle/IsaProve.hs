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

module Isabelle.IsaProve where

import Logic.Prover
import Isabelle.IsaSign
import Isabelle.IsaPrint

import Common.AS_Annotation
import Common.PrettyPrint

import Data.List
import Data.Maybe

import TextDisplay
import Configuration

isabelleProver :: Prover Sign Sentence () ()
isabelleProver =
     Prover { prover_name ="Isabelle",
              prover_sublogic = "Isabelle",
              prove = isaProve
            }

                 -- input: theory name, theory, goals
                 -- output: proof status for goals and lemmas
isaProve :: String -> (Sign,[Named Sentence]) -> [Named Sentence] 
              -> IO([Proof_status Sentence ()])
isaProve thName (sig,axs) goals = do
  let disAxs = disambiguateSens [] $ nameSens $ transSens axs
      showAxs = concat $ map ((++"\n") . showSen) disAxs
      showGoals = concat 
         $ map (("theorem "++) . (++"\noops\n\n") . showSen) 
                  $ disambiguateSens disAxs $ nameSens $ transSens goals
      showTheory = "theory " ++ thName ++ " = " 
                   ++ showPretty sig "\n\naxioms\n" 
                   ++ showAxs ++ "\n\n" ++ showGoals
                   ++ "\nend\n"
  writeFile (thName++".thy") showTheory
  createTextDisplay thName ("Wrote Isabelle/Isar theory "++thName++".thy") 
                    [size(50,10)]
  return [] -- ??? to be implemented

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
