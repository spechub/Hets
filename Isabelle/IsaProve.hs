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

import Common.AS_Annotation
import Common.PrettyPrint

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
  let showAxs = concat $ map ((++"\n") . showSen) (nameSens axs)
      showGoals = concat 
         $ map (("theorem "++) . (++"\noops\n\n") . showSen) goals
      showTheory = thName ++ " = " 
                   ++ showPretty sig "\n\naxioms\n" 
                   ++ showAxs ++ "\n\n" ++ showGoals
                   ++ "\nend\n"
  writeFile (thName++".thy") showTheory
  createTextDisplay thName ("Written Isabelle/Isar theory "++thName++".thy") 
                    [size(30,30)]
  return [] -- ??? to be implemented


-- output an axiom
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
