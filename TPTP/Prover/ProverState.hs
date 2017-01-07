{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./TPTP/Prover/ProverState.hs
Description :  Help functions for all automatic theorem provers.
Copyright   :  (c) Rainer Grabbe
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

Data structures and initialising functions for Prover state and configurations.

-}

module TPTP.Prover.ProverState ( ProverState (..)
                               , getAxioms
                               , insertSentenceIntoProverState
                               , ioShowTPTPProblem
                               , tptpProverState
                               ) where

import TPTP.AS
import TPTP.Pretty
import TPTP.Sign

import Common.AS_Annotation
import Common.ProofUtils
import Common.Doc
import Logic.Prover

import Data.Data
import Data.List

-- * Data structures

data PProblem = PProblem { identifier :: String
                         , logicalPart :: PLogicalPart
                         } deriving (Show, Eq, Ord, Typeable, Data)

data ProverState = ProverState { psLogicalPart :: PLogicalPart
                               } deriving (Show, Ord, Eq, Data, Typeable)

tptpProverState :: Sign -- ^ TPTP signature
            -> [Named Sentence]
               -- ^ list of named TPTP sentences containing axioms
            -> [FreeDefMorphism Sentence Morphism] -- ^ freeness constraints
            -> ProverState
tptpProverState _ sentences _ = ProverState {
  psLogicalPart = foldr (flip insertSentence) emptyPLogicalPart axiomList}
  where newSentences = prepareSenNames id sentences
        axiomList = filter isAxiom newSentences

-- ** proving Logical Parts

{- |
  A proving logical part consists of a symbol list, a declaration list, and a
  set of formula lists. Support for clause lists and proof lists hasn't
  been implemented yet.
-}
data PLogicalPart = PLogicalPart { formulaeList :: [Named Sentence]
                                 } deriving (Show, Eq, Ord, Typeable, Data)

emptyPLogicalPart :: PLogicalPart
emptyPLogicalPart = PLogicalPart { formulaeList = [] }

-- | gets all axioms possibly used in a proof
getAxioms :: ProverState -> [String]
getAxioms = map senAttr . filter isAxiom . formulaeList . psLogicalPart

-- * TPTP specific functions for prover GUI

-- Inserts a named TPTP term into TPTP prover state.
insertSentenceIntoProverState :: ProverState
                                 -- ^ prover state containing initial logical part
                              -> Named Sentence -- ^ goal to add
                              -> ProverState
insertSentenceIntoProverState proverState namedSentence =
  proverState { psLogicalPart =
                  insertSentence (psLogicalPart proverState) namedSentence }

{- |
  Inserts a Named Sentence (axiom or goal) into a PLogicalPart.
-}
insertSentence :: PLogicalPart -> Named Sentence -> PLogicalPart
insertSentence pLogicalPart newSentence =
  pLogicalPart { formulaeList = newSentence : formulaeList pLogicalPart }


{- |
  Generate a TPTP problem with time stamp while maybe adding a goal.
-}
generateTPTPProblem :: PLogicalPart
                    -> Maybe (Named Sentence) -> PProblem
generateTPTPProblem pLogicalPart mNewGoal = PProblem
    { identifier = "hets_exported"
    , logicalPart = maybe pLogicalPart (insertSentence pLogicalPart) mNewGoal
    }

{- |
  Pretty printing TPTP goal in TPTP format.
-}
ioShowTPTPProblem :: String -- ^ theory name
                  -> ProverState -- ^ prover state containing initial logical part
                  -> Named Sentence -- ^ goal to print
                  -> [String] -- ^ extra options
                  -> IO String -- ^ formatted output of the goal
ioShowTPTPProblem theoryName proverState newGoal _ = do
  let problem = generateTPTPProblem
                  (psLogicalPart proverState)
                  (Just newGoal)
  return $ show $ printTPTPProblem theoryName problem

-- Print a newline at the end of the document for good style.
printTPTPProblem :: String -> PProblem -> Doc
printTPTPProblem theoryName problem =
  text "% Problem: " <> text (identifier problem)
  $+$ text "% generated from the library " <> text theoryName
  $+$ vsep (map printNamedSentence $ sortBy sentenceOrder $ formulaeList $
             logicalPart problem)
  $+$ text ""
  where
    sentenceOrder :: Named Sentence -> Named Sentence -> Ordering
    sentenceOrder s t =
      case (formulaRole $ sentence s, formulaRole $ sentence t) of
        (Unknown, _) -> LT
        (Type, _) -> LT
        (Definition, _) -> LT
        (Conjecture, _) -> GT
        (_, _) -> EQ
