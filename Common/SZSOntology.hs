{- |
Module      :  $Header$
Description :  The SZS ontology for TPTP prover results
Copyright   :  (c) Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

see <http://www.cs.miami.edu/~tptp/> under Documents and SZSOntology
-}

module Common.SZSOntology where

import Data.Char

successes :: [(String, String)]
successes =
  [ ("Success", "SUC")
  -- The logical data has been processed successfully.

  , ("UnsatisfiabilityPreserving", "UNP")
  {- If there does not exist a model of Ax then there does not exist a model of
  C, i.e., if Ax is unsatisfiable then C is unsatisfiable. -}

  , ("SatisfiabilityPreserving", "SAP")
  {- If there exists a model of Ax then there exists a model of C, i.e., if Ax
  is satisfiable then C is satisfiable.
  - F is satisfiable. -}

  , ("EquiSatisfiable", "ESA")
  {- There exists a model of Ax iff there exists a model of C, i.e., Ax is
  (un)satisfiable iff C is (un)satisfiable. -}

  , ("Satisfiable", "SAT")
  {- Some interpretations are models of Ax, and
  some models of Ax are models of C.
  - F is satisfiable, and ~F is not valid.
  - Possible dataforms are Models of Ax | C. -}

  , ("FinitelySatisfiable", "FSA")
  {- Some finite interpretations are finite models of Ax, and
  some finite models of Ax are finite models of C.
  - F is satisfiable, and ~F is not valid.
  - Possible dataforms are FiniteModels of Ax | C. -}

  , ("Theorem", "THM")
  {- All models of Ax are models of C.
  - F is valid, and C is a theorem of Ax.
  - Possible dataforms are Proofs of C from Ax. -}

  , ("Equivalent", "EQV")
  {- Some interpretations are models of Ax,
  all models of Ax are models of C, and
  all models of C are models of Ax.
  - F is valid, C is a theorem of Ax, and Ax is a theorem of C.
  - Possible dataforms are Proofs of C from Ax and of Ax from C. -}

  , ("TautologousConclusion", "TAC")
  {- Some interpretations are models of Ax, and
  all interpretations are models of C.
  - F is valid, and C is a tautology.
  - Possible dataforms are Proofs of C. -}

  , ("WeakerConclusion", "WEC")
  {- Some interpretations are models of Ax,
  all models of Ax are models of C, and
  some models of C are not models of Ax.
  - See Theorem and Satisfiable. -}

  , ("EquivalentTheorem", "ETH")
  {- Some, but not all, interpretations are models of Ax,
  all models of Ax are models of C, and
  all models of C are models of Ax.
  - See Equivalent. -}

  , ("Tautology", "TAU")
  {- All interpretations are models of Ax, and
  all interpretations are models of C.
  - F is valid, ~F is unsatisfiable, and C is a tautology.
  - Possible dataforms are Proofs of Ax and of C. -}

  , ("WeakerTautologousConclusion", "WTC")
  {- Some, but not all, interpretations are models of Ax, and
  all interpretations are models of C.
  - F is valid, and C is a tautology.
  - See TautologousConclusion and WeakerConclusion. -}

  , ("WeakerTheorem", "WTH")
  {- Some interpretations are models of Ax,
  all models of Ax are models of C,
  some models of C are not models of Ax, and
  some interpretations are not models of C.
  - See Theorem and Satisfiable. -}

  , ("ContradictoryAxioms", "CAX")
  {- No interpretations are models of Ax.
  - F is valid, and anything is a theorem of Ax.
  - Possible dataforms are Refutations of Ax. -}

  , ("SatisfiableConclusionContradictoryAxioms", "SCA")
  {- No interpretations are models of Ax, and
  some interpretations are models of C.
  - See ContradictoryAxioms. -}

  , ("TautologousConclusionContradictoryAxioms", "TCA")
  {- No interpretations are models of Ax, and
  all interpretations are models of C.
  - See TautologousConclusion and SatisfiableConclusionContradictoryAxioms. -}

  , ("WeakerConclusionContradictoryAxioms", "WCA")
  {- No interpretations are models of Ax, and
  some, but not all, interpretations are models of C.
  - See SatisfiableConclusionContradictoryAxioms and
    SatisfiableCounterConclusionContradictoryAxioms. -}

  , ("CounterUnsatisfiabilityPreserving", "CUP")
  {- If there does not exist a model of Ax then there does not exist a model of
  ~C, i.e., if Ax is unsatisfiable then ~C is unsatisfiable. -}

  , ("CounterSatisfiabilityPreserving", "CSP")
  {- If there exists a model of Ax then there exists a model of ~C, i.e., if Ax
  is satisfiable then ~C is satisfiable. -}

  , ("EquiCounterSatisfiable", "ECS")
  {- There exists a model of Ax iff there exists a model of ~C, i.e., Ax is
  (un)satisfiable iff ~C is (un)satisfiable. -}

  , ("CounterSatisfiable", "CSA")
  {- Some interpretations are models of Ax, and
  some models of Ax are models of ~C.
  - F is not valid, ~F is satisfiable, and C is not a theorem of Ax.
  - Possible dataforms are Models of Ax | ~C. -}

  , ("CounterTheorem", "CTH")
  {- All models of Ax are models of ~C.
  - F is not valid, and ~C is a theorem of Ax.
  - Possible dataforms are Proofs of ~C from Ax. -}

  , ("CounterEquivalent", "CEQ")
  {- Some interpretations are models of Ax,
  all models of Ax are models of ~C, and
  all models of ~C are models of Ax
  (i.e., all interpretations are models of Ax xor of C).
  - F is not valid, and ~C is a theorem of Ax.
  - Possible dataforms are Proofs of ~C from Ax and of Ax from ~C. -}

  , ("UnsatisfiableConclusion", "UNC")
  {- Some interpretations are models of Ax, and
  all interpretations are models of ~C
  (i.e., no interpretations are models of C).
  - F is not valid, and ~C is a tautology.
  - Possible dataforms are Proofs of ~C. -}

  , ("WeakerCounterConclusion", "WCC")
  {- Some interpretations are models of Ax, and
  all models of Ax are models of ~C, and
  some models of ~C are not models of Ax.
  - See CounterTheorem and CounterSatisfiable. -}

  , ("EquivalentCounterTheorem", "ECT")
  {- Some, but not all, interpretations are models of Ax,
  all models of Ax are models of ~C, and
  all models of ~C are models of Ax.
  - See CounterEquivalent. -}

  , ("FinitelyUnsatisfiable", "FUN")
  {- All finite interpretations are finite models of Ax, and
  all finite interpretations are finite models of ~C
  (i.e., no finite interpretations are finite models of C). -}

  , ("Unsatisfiable", "UNS")
  {- All interpretations are models of Ax, and
  all interpretations are models of ~C.
  (i.e., no interpretations are models of C).
  - F is unsatisfiable, ~F is valid, and ~C is a tautology.
  - Possible dataforms are Proofs of Ax and of C, and Refutations of F. -}

  , ("WeakerUnsatisfiableConclusion", "WUC")
  {- Some, but not all, interpretations are models of Ax, and
  all interpretations are models of ~C.
  - See Unsatisfiable and WeakerCounterConclusion. -}

  , ("WeakerCounterTheorem", "WCT")
  {- Some interpretations are models of Ax,
  all models of Ax are models of ~C,
  some models of ~C are not models of Ax, and
  some interpretations are not models of ~C.
  - See CounterSatisfiable. -}

  , ("SatisfiableCounterConclusionContradictoryAxioms", "SCC")
  {- No interpretations are models of Ax, and
  some interpretations are models of ~C.
  - See ContradictoryAxioms. -}

  , ("UnsatisfiableConclusionContradictoryAxioms", "UCA")
  {- No interpretations are models of Ax, and
  all interpretations are models of ~C
  (i.e., no interpretations are models of C).
  - See UnsatisfiableConclusion and
  - SatisfiableCounterConclusionContradictoryAxioms. -}

  , ("NoConsequence", "NOC") ]
  {- Some interpretations are models of Ax,
  some models of Ax are models of C, and
  some models of Ax are models of ~C.
  - F is not valid, F is satisfiable, ~F is not valid, ~F is satisfiable, and
    C is not a theorem of Ax.
  - Possible dataforms are pairs of models, one Model of Ax | C and one Model
    of Ax | ~C. -}

nosuccess :: [(String, String)]
nosuccess =
  [ ("NoSuccess", "NOS")
  -- The logical data has not been processed successfully (yet).

  , ("Open", "OPN")
  -- A success value has never been established.

  , ("Unknown", "UNK")
  -- Success value unknown, and no assumption has been made.

  , ("Assumed", "ASS(U,S)")
  {- The success ontology value S has been assumed because the actual value is
  unknown for the no-success ontology reason U. U is taken from the
  subontology starting at Unknown in the no-success ontology. -}

  , ("Stopped", "STP")
  {- Software attempted to process the data, and stopped without a success
  status. -}

  , ("Error", "ERR")
  -- Software stopped due to an error.

  , ("OSError", "OSE")
  -- Software stopped due to an operating system error.

  , ("InputError", "INE")
  -- Software stopped due to an input error.

  , ("SyntaxError", "SYE")
  -- Software stopped due to an input syntax error.

  , ("SemanticError", "SEE")
  -- Software stopped due to an input semantic error.

  , ("TypeError", "TYE")
  -- Software stopped due to an input type error (for typed logical data).

  , ("Forced", "FOR")
  -- Software was forced to stop by an external force.

  , ("User", "USR")
  -- Software was forced to stop by the user.

  , ("ResourceOut", "RSO")
  -- Software stopped because some resource ran out.

  , ("Timeout", "TMO")
  -- Software stopped because the CPU time limit ran out.

  , ("MemoryOut", "MMO")
  -- Software stopped because the memory limit ran out.

  , ("GaveUp", "GUP")
  -- Software gave up of its own accord.

  , ("Incomplete", "INC")
  -- Software gave up because it's incomplete.

  , ("Inappropriate", "IAP")
  -- Software gave up because it cannot process this type of data.

  , ("InProgress", "INP")
  -- Software is still running.

  , ("NotTried", "NTT")
  -- Software has not tried to process the data.

  , ("NotTriedYet", "NTY") ]
  -- Software has not tried to process the data yet, but might in the future.

szsCheck :: [(String, String)] -> [String] -> String -> Bool
szsCheck pl l = maybe False (`elem` l)
   . (`lookup` map (\ (t, r) -> (map toLower t, r)) pl) . map toLower

szsProved :: String -> Bool
szsProved = szsCheck successes ["SAT", "THM"]

szsDisproved :: String -> Bool
szsDisproved = szsCheck successes ["CSA", "UNS"]

szsTimeout :: String -> Bool
szsTimeout = szsCheck nosuccess ["TMO"]

szsMemoryOut :: String -> Bool
szsMemoryOut = szsCheck nosuccess ["MMO"]

szsStopped :: String -> Bool
szsStopped = szsCheck nosuccess ["STP"]

