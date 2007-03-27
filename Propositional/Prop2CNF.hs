{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Helper functions for the translation of propositional formulae to CNF. We are
using SPASS -Flotter=1 here
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
  2005.
-}

module Propositional.Prop2CNF
    where

import qualified SPASS.ProverState as PState
import qualified Comorphisms.Prop2CASL as P2C
import qualified Comorphisms.CASL2SPASS as C2S
import qualified Logic.Comorphism as Com
import qualified SPASS.Sign as Sig
import qualified Propositional.Sign as PSign
import qualified Common.Result as Result
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Common.AS_Annotation as AS_Anno
import qualified SPASS.Conversions as Conv

import ChildProcess
import ProcessClasses

import System

import Data.Maybe
import HTk
import qualified Control.Exception as Exception
import Common.DocUtils
import Text.Regex

prover_name :: String
prover_name = "SPASS"

-- | the used comorphism is an embedding
comp :: Com.CompComorphism P2C.Prop2CASL C2S.SuleCFOL2SoftFOL
comp = (Com.CompComorphism P2C.Prop2CASL C2S.SuleCFOL2SoftFOL)

-- | Shortcut for the translation of the theory
getTheory :: (PSign.Sign, [AS_Anno.Named PBasic.FORMULA]) 
             -> Result.Result (Sig.Sign, [AS_Anno.Named Sig.SPTerm])
getTheory = Com.map_theory comp

-- | Initial ProverState for Spass
createInitProverState :: PSign.Sign 
                      -> [AS_Anno.Named PBasic.FORMULA] 
                      -> PState.SPASSProverState
createInitProverState sign nForms =
    let (osig, oth) = 
            case Result.maybeResult $ getTheory  (sign, nForms) of
              Just (xs,ys) -> (xs,ys)
              Nothing    -> error "Should not happen... Error in Prop2CNF"
    in
      PState.spassProverState osig  oth

{- |
  Runs SPASS. SPASS is assumed to reside in PATH.
-}
runSpass :: PState.SPASSProverState -- Spass Prover state... Theory + Sig
         -> Bool -- ^ True means save DFG file
         -> IO String -- Placeholder
runSpass sps saveDFG = 
    do
      spass <- newChildProcess "SPASS" [ChildProcess.arguments allOptions]
      Exception.catch (runSpassReal spass)
                   (\ excep -> do
                      -- kill spass process
                      destroy spass
                      _ <- waitForChildProcess spass
                      return "SPASS not found... Bailing out!!!"
                   )
    where
      runSpassReal spass = do
        -- check if SPASS is running
        e <- getToolStatus spass
        if isJust e
           then error "Something is wrong"
           else do
             prob <- showDFGProblem "Translation" sps (filteredOptions)
             when saveDFG
                      (writeFile ("FlotterIn.dfg") prob)
             sendMsg spass prob
             flotterOut <- parseProtected spass
             when saveDFG
                      (writeFile ("FlotterOut.dfg") flotterOut)
             return flotterOut

      filteredOptions = ["-Stdin", "-Flotter"]
      allOptions = ["-Stdin", "-Flotter", "-CNFRenaming=0"]
      
{- |
  Pretty printing SPASS goal in DFG format.
-}
showDFGProblem :: String -- ^ theory name
                  -> PState.SPASSProverState -- ^ prover state containing
                                      -- initial logical part
                  -> [String] -- ^ extra options
                  -> IO String -- ^ formatted output of the goal
showDFGProblem thName pst opts = do
  prob <- Conv.genSPASSProblem thName (PState.initialLogicalPart pst) $ Nothing
  -- add SPASS command line settings and extra options
  let prob' = prob { Sig.settings = (Sig.settings prob) ++ 
                     (PState.parseSPASSCommands opts) }
  return $ showDoc prob' ""

parseProtected :: ChildProcess -> IO String
parseProtected spass = do
  e <- getToolStatus spass
  case e of 
    Nothing                   -> 
        do  
          dfg <- parseIt spass
          return dfg
    Just (ExitFailure retval) -> 
        do
          _ <- waitForChildProcess spass
          return "error"
    Just ExitSuccess          -> return "done"

parseIt :: ChildProcess -> IO String
parseIt spass = do
  line <- readMsg spass
  msg  <- parseItHelp spass $ return line
  return msg

parseItHelp :: ChildProcess -> IO String -> IO String
parseItHelp spass inp = do
  e <- getToolStatus spass
  inT <- inp
  case e of 
    Nothing
        -> 
          do
            line <- readMsg spass
            parseItHelp spass $ return (inT ++ " \n" ++ line)
    Just (ExitFailure retval)
        -- returned error
        -> do
           _ <- waitForChildProcess spass
           return $ "SPASS returned error: "++(show retval)
    Just ExitSuccess
         -- completed successfully. read remaining output.
         -> 
           do
             line <- readMsg spass
             case isEnd line of
               True ->
                   return inT
               _    ->
                   parseItHelp spass $ return (inT ++ " \n" ++ line)

spassEnd = mkRegex "(.*)FLOTTER needed(.*)"

isEnd :: String -> Bool
isEnd inS = 
    let out = matchRegex spassEnd inS in
    case out of
      Nothing -> False
      Just  _ -> True
