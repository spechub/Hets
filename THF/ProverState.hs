{- |
Module      :  $Header$
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Rainer Grabbe
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Data structures and initialising functions for Prover state and configurations.

-}

module THF.ProverState where

import Logic.Prover

import THF.Cons
import THF.Sign
import THF.Print

import Common.AS_Annotation


-- * Data structures

data ProverStateTHF = ProverStateTHF
    { axioms    :: [Named SentenceTHF]
    , signature :: SignTHF
    , freeDefs  :: [FreeDefMorphism SentenceTHF MorphismTHF]
    }

-- * THF specific functions for prover GUI

{- |
  Creates an initial THF prover state.
-}
initialProverStateTHF :: SignTHF -> [Named SentenceTHF]
    -> [FreeDefMorphism SentenceTHF MorphismTHF]
    -> ProverStateTHF
initialProverStateTHF sign oSens freedefs = ProverStateTHF
    { axioms = filter isAxiom oSens
    , signature = sign
    , freeDefs = freedefs }

insertSentenceTHF :: ProverStateTHF -> Named SentenceTHF -> ProverStateTHF
insertSentenceTHF ps ns = ps {axioms = ns : axioms ps}

showProblemTHF :: ProverStateTHF -> Named SentenceTHF -> [String] -> IO String
showProblemTHF ps goal _ = return $ show $
        printProblemTHF (signature ps) (filter isAxiom $ axioms ps) goal
