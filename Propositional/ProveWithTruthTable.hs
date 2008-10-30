{- |
Module      :  $Header$
Description :  Provers for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

This is the connection of the SAT-Solver minisat to Hets
-}

module Propositional.ProveWithTruthTable
    (
     ttProver --,    
--     ttConsistencyChecker,
--     ttConservativityChecker
    )
    where

import Text.Tabular.AsciiArt
import Text.Tabular

import Propositional.AS_BASIC_Propositional
import Propositional.Sign
import qualified Propositional.Morphism as PMorphism
import qualified Propositional.ProverState as PState
import qualified Propositional.Sign as Sig
import Propositional.Sublogic(PropSL,top)

import Proofs.BatchProcessing

import qualified Logic.Prover as LP

import qualified GUI.GenericATPState as ATPState
import GUI.GenericATP
import GUI.HTkUtils

import HTk

import Common.ProofTree
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import qualified Common.OrderedMap as OMap
import System.IO

import Common.Utils (readMaybe)



-- * Prover implementation

-- | the name of the prover
ttS :: String
ttS = "truth tables"

-- maximal size of the signature
maxSigSize :: Int
maxSigSize = 15

ttHelpText :: String
ttHelpText = "An implementation of the truth table method.\n"++
                 "Very inefficient, but useful for learning and teaching\n"++
                 "Works well for signatures with less than "++show maxSigSize++
                 " symbols."

{- |
  Models and evaluation of sentences
-}

type Model = Set.Set Id.Id -- a model specifies which propositions are true

-- | show Bools in truth table
showBool :: Bool -> String
showBool True = "T"
showBool False = "F"

-- | evaluation of sentences in a model
eval :: Model -> FORMULA -> Bool
eval m (Negation phi _) = not (eval m phi)
eval m (Conjunction phis _) = and (map (eval m) phis)
eval m (Disjunction phis _) = or (map (eval m) phis)
eval m (Implication phi1 phi2 _) = 
       not (eval m phi1) || (eval m phi2)
eval m (Equivalence phi1 phi2 _) = 
       (eval m phi1) == (eval m phi2)
eval m (True_atom _) = True
eval m (False_atom _) = False
eval m (Predication id) = Id.simpleIdToId id `Set.member` m

evalNamed :: Model -> AS_Anno.Named (FORMULA) -> Bool
evalNamed m phi = eval m (AS_Anno.sentence phi)


-- | generate all models for a signature
allModels :: Sign -> [Model]
allModels sig = allModels1 $ Set.toList $ items sig
  where allModels1 [] = [Set.empty]
        allModels1 (p:rest) = 
          let models = allModels1 rest
           in models ++ map (Set.insert p) models

data TTRow =
     TTRow { rprops :: [Bool],
             raxioms :: [Bool],
             rgoal :: Maybe Bool,
             rIsModel :: Bool,
             rIsOK :: Bool
           }

data TTHead = 
     TTHead { hprops :: [String],
              haxioms :: [String],
              hgoal :: Maybe String
            }

data TruthTable = 
     TruthTable { thead :: TTHead,
                  trows :: [TTRow] }

renderTT :: TruthTable -> Table String
renderTT tt = Table rowHeaders header table 
  where 
  header = Group DoubleLine
           ( [ Group SingleLine (map Header (hprops (thead tt)))
             , Group SingleLine (map Header (haxioms (thead tt)))]
             ++ case hgoal (thead tt) of
                 Nothing -> []
                 Just g -> [Header g])
  rowtype row =   (if rIsModel row then "M" else " ")
                ++(if rIsOK row then "+" else "-")
  rowHeaders = 
    Group NoLine (map (Header . rowtype) (trows tt))
  makeRow row = map showBool (rprops row) ++ 
                map showBool (raxioms row) ++ 
                case (rgoal row) of
                  Nothing -> []
                  Just g -> [showBool g]
  table = map makeRow (trows tt)


{- |
  The Prover implementation.

  Implemented are: a prover GUI.
-}
ttProver :: LP.Prover Sig.Sign FORMULA PropSL ProofTree
ttProver = (LP.mkProverTemplate ttS top ttProveGUI)
    { LP.proveCMDLautomatic = Nothing 
    , LP.proveCMDLautomaticBatch = Nothing }

{- |
   The Consistency Cheker.
-}
ttConsistencyChecker :: LP.ConsChecker Sig.Sign FORMULA PropSL
                                  PMorphism.Morphism ProofTree
ttConsistencyChecker = LP.mkProverTemplate ttS top consCheck

consCheck :: String -> LP.TheoryMorphism Sig.Sign FORMULA
             PMorphism.Morphism ProofTree
          -> IO([LP.Proof_status ProofTree])
consCheck thName tm =
    case LP.t_target tm of
      LP.Theory sig nSens -> do
            let axioms = getAxioms $ snd $ unzip $ OMap.toList nSens
            createInfoWindow "consistency checker" "test"
            return undefined
    where
        getAxioms :: [LP.SenStatus FORMULA (LP.Proof_status ProofTree)]
                  -> [AS_Anno.Named FORMULA]
        getAxioms f = map (AS_Anno.makeNamed "consistency" . AS_Anno.sentence) $ filter AS_Anno.isAxiom f

        searchResult :: Handle -> IO Bool
        searchResult hf = do
            eof <- hIsEOF hf
            if eof then
                return False
              else
               do
                line <- hGetLine hf
                putStrLn line
                if line == "RESULT:\tUNSAT" then
                      return True
                  else if line == "RESULT:\tSAT" then
                          return False
                         else searchResult hf

-- ** prover GUI

{- |
  Invokes the generic prover GUI.
-}
ttProveGUI :: String -- ^ theory name
          -> LP.Theory Sig.Sign FORMULA ProofTree
          -> IO([LP.Proof_status ProofTree]) -- ^ proof status for each goal
ttProveGUI thName th =
    genericATPgui (atpFun thName) True (LP.prover_name ttProver) thName th
                  emptyProofTree
{- |
  Parses a given default tactic script into a
  'GUI.GenericATPState.ATPTactic_script' if possible.
-}
parseTtTactic_script :: LP.Tactic_script
                        -> ATPState.ATPTactic_script
parseTtTactic_script =
    parseTactic_script batchTimeLimit

{- |
  Parses a given default tactic script into a
  'GUI.GenericATPState.ATPTactic_script' if possible. Otherwise a default
  prover's tactic script is returned.
-}
parseTactic_script :: Int -- ^ default time limit (standard:
                          -- 'Proofs.BatchProcessing.batchTimeLimit')
                   -> LP.Tactic_script
                   -> ATPState.ATPTactic_script
parseTactic_script tLimit (LP.Tactic_script ts) =
    maybe (ATPState.ATPTactic_script { ATPState.ts_timeLimit = tLimit,
                                       ATPState.ts_extraOpts = [] })
           id $ readMaybe ts

{- |
  Record for prover specific functions. This is used by both GUI and command
  line interface.
-}
atpFun :: String            -- Theory name
       -> ATPState.ATPFunctions Sig.Sign FORMULA ProofTree PState.PropProverState
atpFun thName = ATPState.ATPFunctions
                {
                  ATPState.initialProverState = PState.propProverState
                , ATPState.goalOutput         = goalProblem thName
                , ATPState.atpTransSenName    = PState.transSenName
                , ATPState.atpInsertSentence  = PState.insertSentence
                , ATPState.proverHelpText     = ttHelpText
                , ATPState.runProver          = runTt
                , ATPState.batchTimeEnv       = ""
                , ATPState.fileExtensions     = ATPState.FileExtensions{ATPState.problemOutput = ".tt",
                                                                        ATPState.proverOutput = ".tt",
                                                                        ATPState.theoryConfiguration = ".tt"}
                , ATPState.createProverOptions = createTtOptions
                }

defaultProof_status nGoal = 
  (LP.openProof_status (AS_Anno.senAttr nGoal) 
                       (LP.prover_name ttProver)
                       emptyProofTree)

{- |
  Runs tt. 
-}

runTt :: PState.PropProverState
           -- logical part containing the input Sign and
           -- axioms and possibly goals that have been proved
           -- earlier as additional axioms
           -> ATPState.GenericConfig ProofTree
           -- configuration to use
           -> Bool
           -- True means save DIMACS file
           -> String
           -- Name of the theory
           -> AS_Anno.Named FORMULA
           -- Goal to prove
           -> IO (ATPState.ATPRetval
                 , ATPState.GenericConfig ProofTree
                 )
           -- (retval, configuration with proof status and complete output)
runTt pState cfg _ thName nGoal =
  let sig = PState.initialSignature pState 
      size = Set.size $ items sig
   in if size >= maxSigSize then do
        createInfoWindow "Signature is too large" 
           ("Signature is too large. "++
            "It should contain < "++show maxSigSize++" symbols, "++
            "but it contains "++show size++" symbols.")
        return (ATPState.ATPTLimitExceeded, 
                cfg{ATPState.proof_status = defaultProof_status nGoal})
      else do
       let axs = PState.initialAxioms pState
           models = allModels sig
           sigList = Set.toList $ items sig
           heading = 
             TTHead { hprops = map show sigList,
                      haxioms = map AS_Anno.senAttr axs,
                      hgoal = Just $ AS_Anno.senAttr nGoal 
                    }
           row m = 
             let evalAx = map (evalNamed m) axs
                 evalGoal = evalNamed m nGoal
                 isModel = and evalAx
             in TTRow { rprops = map (`Set.member` m) sigList,
                        raxioms = evalAx,
                        rgoal = Just evalGoal,
                        rIsModel = isModel,
                        rIsOK = not isModel || evalGoal
                      }
           rows = map row models
           isOK = and (map rIsOK rows)
           table = TruthTable { thead = heading,
                                trows = rows
                              }
           title = if isOK then "Proof succeeded" else "Proof failed"
           legend = "Legend:\nM = model of the axioms\n"++
                    "+ = OK\n- = not OK, counterexample "++
                    "for logical consequence\n"
           body = legend++"\n"++render id (renderTT table)
--        createInfoWindow title body
       let status = (defaultProof_status nGoal)
                        { LP.goalStatus = if isOK then LP.Proved $ Nothing
                                                  else LP.Disproved,
                          LP.usedAxioms = map AS_Anno.senAttr axs 
                        }                          
       return (ATPState.ATPSuccess,
               cfg{ATPState.proof_status = status,
                   ATPState.resultOutput = [body]})
            
{- |
  Creates a list of all options the truth table prover runs with.
  Only Option is the timelimit
-}
createTtOptions :: ATPState.GenericConfig ProofTree -> [String]
createTtOptions cfg = []
   -- [(show $ configTimeLimit cfg)]

goalProblem :: String                   -- name of the theory
                  -> PState.PropProverState   -- initial Prover state
                  -> AS_Anno.Named FORMULA -- goal to prove
                  -> [String]                 -- Options (ignored)
                  -> IO String
goalProblem thName pState conjec _ =
  return ""
