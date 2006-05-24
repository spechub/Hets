{- |
Module      :  $Header$
Description :  Interface for the SPASS theorem prover using MathServ.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  not yet working, do not use
Portability :  needs POSIX

Interface for the SPASS theorem prover, uses GUI.GenericATP.
See <http://spass.mpi-sb.mpg.de/> for details on SPASS.

-}

{-
    To do:
      - XML parser for MathServOutput
      
      - update to do list and module description
      
      - check if the theorem is used in the proof;
        if not, the theory is inconsistent;
        mark goal as proved and emmit a warning...

      - Implement a consistency checker based on GUI
-}

module SPASS.ProveMathServ (mathServBroker,mathServBrokerGUI) where

import Logic.Prover

import SPASS.Sign
import SPASS.Conversions
import SPASS.ProveHelp
import SPASS.Translate
import SPASS.Print (genSPASSProblem)
import SPASS.PrintTPTP
import SPASS.MathServCommunication

import qualified Common.AS_Annotation as AS_Anno
import Common.ProofUtils
import Common.PrettyPrint

import Network.URI
import Network.Service
import Org.Xmlsoap.Schemas.Soap.Envelope as ENV

-- import Text.XML.HXT.XPath.XPathParser
import Text.Regex

import Data.List
import Data.Maybe

import HTk

import GUI.GenericATP
import GUI.GenericATPState

-- * Prover implementation

{- |
  The Prover implementation. First runs the batch prover (with graphical
  feedback), then starts the GUI prover.
-}
mathServBroker :: Prover Sign Sentence ()
mathServBroker =
  Prover { prover_name = "MSBroker (Exp)",
           prover_sublogic = "SoftFOL",
           prove = mathServBrokerGUI
         }

-- ** Data structures

data SPASSProverState = SPASSProverState
    { initialLogicalPart :: SPLogicalPart}


-- ** SPASS specific functions for prover GUI

{- |
  Creates an initial SPASS prover state with logical part.
-}
spassProverState :: Sign -- ^ SPASS signature
                 -> [AS_Anno.Named SPTerm] -- ^ list of named SPASS terms containing axioms
                 -> SPASSProverState
spassProverState sign oSens' = SPASSProverState{
    initialLogicalPart = foldl insertSentence
                               (signToSPLogicalPart sign)
                               (reverse axioms)}
  where nSens = prepareSenNames transSenName oSens'
        axioms = filter AS_Anno.isAxiom nSens

{- |
  Inserts a named SPASS term into SPASS prover state.
-}
insertSentenceGen :: SPASSProverState -- ^ prover state containing initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to add
                  -> SPASSProverState
insertSentenceGen pst s = pst{initialLogicalPart =
                                insertSentence (initialLogicalPart pst) s}

{- |
  Pretty printing SPASS goal in DFG format.
-}
showPrettyProblem :: String -- ^ theory name
                  -> SPASSProverState -- ^ prover state containing initial logical part
                  -> AS_Anno.Named SPTerm -- ^ goal to print
                  -> IO String -- ^ formatted output of the goal
showPrettyProblem thName pst nGoal = do
  prob <- genSPASSProblem thName (initialLogicalPart pst) $ Just nGoal
  return $ showPretty prob ""


-- * Main GUI

{- |
  Invokes the generic prover GUI. SPASS specific functions are omitted by
  data type ATPFunctions.
-}
mathServBrokerGUI :: String -- ^ theory name
                  -> Theory Sign Sentence () -- ^ theory consisting of a SPASS.Sign.Sign and a list of Named SPASS.Sign.Sentence
                  -> IO([Proof_status ()]) -- ^ proof status for each goal
mathServBrokerGUI thName th =
    genericATPgui atpFun False (prover_name mathServBroker) thName th ()

    where
      atpFun = ATPFunctions
        { initialProverState = spassProverState,
          atpTransSenName = transSenName,
          atpInsertSentence = insertSentenceGen,
          goalOutput = showPrettyProblem thName,
          proverHelpText = spassHelpText,
          batchTimeEnv = "HETS_SPASS_BATCH_TIME_LIMIT",
          fileExtensions = FileExtensions{problemOutput = ".dfg",
                                          proverOutput = ".spass",
                                          theoryConfiguration = ".spcf"},
          runProver = runMSBroker}


-- * MathServ Interfacing Code

-- testwise connection to MathServ

makeEndPoint :: String -> Maybe HTTPTransport
makeEndPoint uriStr = maybe Nothing 
                            (\ uri -> Just $ HTTPTransport 
                                      { httpEndpoint = uri
                                      , httpSOAPAction = Just nullURI})
                            (parseURI uriStr)

callMathServ :: String -- ^ Problem to prove in TPTP format
             -> Int -- ^ Time limit
             -> IO String -- ^ MathServ output or error message
callMathServ problem timeout =
    do 
       maybe (do
                return "Could not start MathServ.")
             (\ endPoint -> do
                 (res::Either SimpleFault MathServOutput) 
                     <- soapCall endPoint $
                        mkProveProblem Nothing service operation problem timeout
                 case res of
                  Left err -> do
                    return $ show err
                  Right resp -> do
                    return $ getResponse resp
             )
             (makeEndPoint $ 
                "http://"++server++':':port++"/axis/services/"++service)
    where
    -- server data
        server = "denebola.informatik.uni-bremen.de"
        port = "8080"
        service = "Broker"
        operation = "ProveProblemOpt"



{- |
  Reads and parses the output of SPASS or any other prover. If SPASS was used,
  more information about goal status and used axioms is available and will be parsed.
-}
parseProverOutput :: [String] -- ^ the prover output (maybe SPASS)
                  -> (Maybe GoalStatus, [String]) -- ^ previous goal status reported by MathServ, used axioms (initial empty)
                  -> (Maybe GoalStatus, [String]) -- ^ (result goal status, used axioms)
parseProverOutput [] result = result
parseProverOutput (line:ls) (res, usedAxs) =
    let spassMatch = matchRegex re_spass line
    in
       -- filter more information with parseSpassOutput if SPASS was used
      if isJust spassMatch then parseSpassOutput ls (res, usedAxs)
                           else (res, usedAxs)
    where
      re_spass = mkRegex "SPASS V.*$"
  

{- |
  Reads and parses the output of SPASS. The goal status will be updated (if possible),
  used axioms will be filtered and added.
-}
parseSpassOutput :: [String] -- ^ SPASS output, beginning with result line
                 -> (Maybe GoalStatus, [String])
                 -> (Maybe GoalStatus, [String]) -- ^ (current goal status, currently used axioms)
parseSpassOutput [] result = result
parseSpassOutput (line:ls) (res, usedAxs) =
    if null ls then (res', usedAxs') else parseSpassOutput ls (res', usedAxs')

    where
      resultMatch = matchRegex re_sb line
      res' = maybe res createGoalStatus resultMatch
      createGoalStatus resMatch
        | elem proved resMatch = Just $ Proved Nothing
        | elem disproved resMatch = Just Disproved
        | elem timelimit resMatch = Just Open
        | otherwise = res
      usedAxsMatch = matchRegex re_ua line
      usedAxs' = if isJust usedAxsMatch then (words $ head $ fromJust usedAxsMatch) else usedAxs

      re_sb = mkRegex "SPASS beiseite: (.*)$"
      re_ua = mkRegex "Formulae used in the proof.*:(.*)$"
      proved = "Proof found."
      disproved = "Completion found."
      timelimit = "Ran out of time."


{- |
  Runs the MathServ broker.
-}
runMSBroker :: SPASSProverState -- ^ logical part containing the input Sign and axioms and possibly goals that have been proved earlier as additional axioms
            -> GenericConfig () -- ^ configuration to use
            -> Bool -- ^ True means save DFG file
            -> String -- ^ name of the theory in the DevGraph
            -> AS_Anno.Named SPTerm -- ^ goal to prove
            -> IO (ATPRetval, GenericConfig ()) -- ^ (retval, configuration with proof status and complete output)
runMSBroker sps cfg saveDFG thName nGoal = do
    putStrLn ("running MathServ...")
    let lp = initialLogicalPart sps
    prob <- genSPASSProblem thName lp (Just nGoal)
    when saveDFG
         (writeFile (thName++'_':AS_Anno.senName nGoal++".dfg")
                    (showPretty prob ""))
    mathServOut <- callMathServ (show $ printTPTP prob) tLimit
   
    -- put XML parser in here 
    
    -- some fast results using RegExp
    let res = parseMSOutput mathServOut

    let timeout = False
    let output = []

      -- replace tabulators occuring in output with each 8 spaces
    let output' = lines $ foldr (\ch li ->
                                    if ch == '\x9' then "        "++li
                                                   else ch:li)
                                "" $ unlines output

    -- get some more infos if SPASS was used
    let (res', usedAxs) = parseProverOutput output (res, []) 
    let (err, retval) = proof_stat nGoal res' usedAxs timeout defaultPrStat
    return (err,
            cfg{proof_status = retval,
                resultOutput = output'})
    where
      tLimit = maybe (guiDefaultTimeLimit) id $ timeLimit cfg
      defaultPrStat = defaultProof_status nGoal tLimit
      

parseMSOutput :: String  -- ^ MathServ Output
              -> Maybe GoalStatus -- ^ final parsed goal status
parseMSOutput out =
    let matchTheorem = matchRegex re_theorem out
        matchCounter = matchRegex re_counter out
    in if isJust matchTheorem then Just $ Proved Nothing
          else if isJust matchCounter then Just Disproved
            else Just Open
    where
      re_theorem = mkRegex "status.owl#Theorem"
      re_counter = mkRegex "status.owl#Counter"


-- !! check the states, is defaultProof_status sufficient?
{- |
  Default proof status. Contains the goal name, prover name
  and the time limit option used by MathServ.
-}
defaultProof_status :: AS_Anno.Named SPTerm -- ^ goal to prove
                    -> Int -- ^ time limit
                    -> Proof_status ()
defaultProof_status nGoal tl =
  (openProof_status (AS_Anno.senName nGoal)
                    (prover_name mathServBroker) ())
  {tacticScript = Tactic_script $ show tl}
    

{- |
  Returns the value of a prover run used in GUI (Success, Error or TLimitExceeded),
  and the proof_status containing all prove information available.
-}
proof_stat :: AS_Anno.Named SPTerm -- ^ goal to prove
           -> Maybe GoalStatus -- ^ Nothing stands for prove error
           -> [String] -- ^ Used axioms in the proof
           -> Bool -- ^ Timeout status
           -> Proof_status () -- ^ default proof status
           -> (ATPRetval, Proof_status ()) -- ^ General return value of a prover run, used in GUI.
                                           --   Detailed proof status if information is available.
proof_stat nGoal res usedAxs timeOut defaultPrStat
  | (fromJust res == Proved Nothing) =
      (ATPSuccess, defaultPrStat
       { goalStatus = Proved $ if elem (AS_Anno.senName nGoal) usedAxs
                               then Nothing
                               else Just False
       , usedAxioms = filter (/=(AS_Anno.senName nGoal)) usedAxs })
  | (fromJust res == Disproved) =
      (ATPSuccess, defaultPrStat { goalStatus = Disproved } )
  | isJust res && timeOut =
      (ATPTLimitExceeded,
       defaultPrStat { goalStatus = fromJust res })
  | isNothing res =
      (ATPError "Internal error.", defaultPrStat)
  | otherwise = (ATPSuccess, defaultPrStat)
