{- |
Module      :  ./CMDL/ProcessScript.hs
Description :  process script commands
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module CMDL.ProcessScript where

import Interfaces.Command
import Interfaces.DataTypes

import Driver.Options

import CMDL.DataTypes
import CMDL.DataTypesUtils
import CMDL.Commands
import CMDL.ParseProofScript as Parser

import Common.Utils

import Data.List

import Control.Monad
import System.IO
import System.Exit

import Static.GTheory
import qualified Data.HashMap.Lazy as Map
import Common.AS_Annotation
import Proofs.AbstractState
import qualified Common.OrderedMap as OMap
import Logic.Prover

isNotDisproved :: G_theory -> Bool
isNotDisproved G_theory {gTheorySens = el} =
  checkListDisproved . map
  (map snd . getThmStatus . senAttr . OMap.ele . snd) $ Map.toList el

checkList :: [BasicProof] -> Bool
checkList [] = False
checkList (l : ls) = case l of
            BasicProof _ (ProofStatus _ b _ _ _ _ _ _) -> case b of
              Disproved -> True
              _ -> checkList ls
            _ -> checkList ls

checkListDisproved :: [[BasicProof]] -> Bool
checkListDisproved = all (not . checkList)

cmdlProcessString :: FilePath -> Int -> String -> CmdlState
  -> IO (CmdlState, Maybe Command)
cmdlProcessString fp l ps st = case parseSingleLine fp l ps of
  Left err -> return (genMsgAndCode err 3 st, Nothing)
  Right c -> let cm = Parser.command c in
       fmap (\ nst -> (nst, Just $ cmdDescription cm)) $ execCmdlCmd cm st

-- sets the errorCode to 0 and then processes the string
resetErrorAndProcString :: FilePath -> Int -> String -> CmdlState
  -> IO (CmdlState, Maybe Command)
resetErrorAndProcString fp l ps st =
  cmdlProcessString fp l ps $ resetErrorCode st

execCmdlCmd :: CmdlCmdDescription -> CmdlState -> IO CmdlState
execCmdlCmd cm =
  case cmdFn cm of
    CmdNoInput f -> f
    CmdWithInput f -> f . cmdInputStr $ cmdDescription cm

cmdlProcessCmd :: Command -> CmdlState -> IO CmdlState
cmdlProcessCmd c = case find (eqCmd c . cmdDescription) getCommands of
  Nothing -> return . genMsgAndCode ("unknown command: " ++ cmdNameStr c) 3
  Just cm -> execCmdlCmd cm { cmdDescription = c }

printCmdResult :: CmdlState -> IO CmdlState
printCmdResult state = do
  let o = output state
      ms = outputMsg o
      ws = warningMsg o
      es = errorMsg o
  unless (null ms) $ putStrLn ms
  unless (null ws) . putStrLn $ "Warning:\n" ++ ws
  unless (null es) . putStrLn $ "Error:\n" ++ es
  hFlush stdout
  return state { output = emptyCmdlMessage }

cmdlProcessScriptFile :: Bool -> FilePath -> CmdlState -> IO CmdlState
cmdlProcessScriptFile doExit fp st = do
  str <- readFile fp
  s <- foldM (\ nst (s, n) -> do
      (cst, _) <- resetErrorAndProcString fp n s nst
      printCmdResult cst) st . number $ lines str
  when doExit $ exitWith $ case i_state $ intState s of
    Just x -> let hd : _ = elements x in case hd of
      Element list _ -> if isNotDisproved (currentTheory list)
          then getExitCode s
          else ExitFailure 4
    Nothing -> getExitCode s
  return s


-- | The function processes the file of instructions
cmdlProcessFile :: Bool -> HetcatsOpts -> FilePath -> IO CmdlState
cmdlProcessFile doExit opts file = do
  putIfVerbose opts 2 $ "Processing hets proof file: " ++ file
  s <- cmdlProcessScriptFile doExit file $ emptyCmdlState opts
  when doExit $ exitWith $ getExitCode s
  return s
