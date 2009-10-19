{- |
Module      :  $Header$
Description :  process script commands
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
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

import Data.Char
import Data.Either
import Data.List

import Control.Monad
import System.IO

cmdlProcessString :: FilePath -> Int -> String -> CmdlState
  -> IO (CmdlState, Maybe Command)
cmdlProcessString fp l ps st = case parseSingleLine fp l ps of
  Left err -> return (genErrorMsg err st, Nothing)
  Right c -> let cm = Parser.command c in
       fmap (\ nst -> (nst, Just $ cmdDescription cm)) $ execCmdlCmd cm st

execCmdlCmd :: CmdlCmdDescription -> CmdlState -> IO CmdlState
execCmdlCmd cm =
  case cmdFn cm of
    CmdNoInput f -> f
    CmdWithInput f -> f . cmdInputStr $ cmdDescription cm

cmdlProcessCmd :: Command -> CmdlState -> IO CmdlState
cmdlProcessCmd c = case find (eqCmd c . cmdDescription) getCommands of
  Nothing -> return . genErrorMsg ("unknown command: " ++ cmdNameStr c)
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

cmdlProcessScriptFile :: FilePath -> CmdlState -> IO CmdlState
cmdlProcessScriptFile fp st = do
  str <- readFile fp
  foldM (\ nst (s, n) -> do
      (cst, _) <- cmdlProcessString fp n s nst
      printCmdResult cst) st
    . number $ lines str

-- | The function processes the file of instructions
cmdlProcessFile :: HetcatsOpts -> FilePath -> IO CmdlState
cmdlProcessFile opts file = do
  putIfVerbose opts 2 $ "Processing hets proof file: " ++ file
  cmdlProcessScriptFile file $ emptyCmdlState opts
