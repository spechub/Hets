{- |
Module      :  $Header$
Description :  process script commands
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module CMDL.ProcessScript where

import Interfaces.Command

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

cmdlProcessString :: FilePath -> Int -> String -> CmdlState
  -> IO (CmdlState, Maybe Command)
cmdlProcessString fp l ps st = case parseSingleLine fp l ps of
  Left err -> return (genMsgAndCode err 3 st, Nothing)
  Right c -> let cm = Parser.command c in
       fmap (\ nst -> (nst, Just $ cmdDescription cm)) $ execCmdlCmd cm st

--sets the errorCode to 0 and then processes the string
resetErrorAndProcString :: FilePath -> Int -> String -> CmdlState
  -> IO (CmdlState, Maybe Command)
resetErrorAndProcString fp l ps st = cmdlProcessString fp l ps $ resetErrorCode st

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
  unless (Data.List.null ms) $ putStrLn ms
  unless (Data.List.null ws) . putStrLn $ "Warning:\n" ++ ws
  unless (Data.List.null es) . putStrLn $ "Error:\n" ++ es
  hFlush stdout
  return state { output = emptyCmdlMessage }


cmdlProcessScriptFile :: FilePath -> CmdlState -> IO CmdlState
cmdlProcessScriptFile fp st = do
  str <- readFile fp
  s <- foldM (\ nst (s, n) -> do
      (cst, _) <- resetErrorAndProcString fp n s nst
      printCmdResult cst) st . number $ lines str
  exitWith $ getExitCode s
  return s


-- | The function processes the file of instructions
cmdlProcessFile :: HetcatsOpts -> FilePath -> IO CmdlState
cmdlProcessFile opts file = do
  putIfVerbose opts 2 $ "Processing hets proof file: " ++ file
  s <- cmdlProcessScriptFile file $ emptyCmdlState opts
  exitWith $ getExitCode s
  return s
