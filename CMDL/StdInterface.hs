{- |
Module      : $Header$
Description : The definition of standard input\/output interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

CMDL.StdInterface describes the interface specific function
for standard input and file input
-}

module CMDL.StdInterface
       ( stdShellDescription
       , basicOutput
       , recursiveApplyUse
       )where

import System.Console.Shell(CommandStyle(OnlyCommands), ShellDescription(..),
                            initialShellDescription)
import System.Console.Shell.Backend(BackendOutput(..))
import System.IO(IO, putStr, stderr, stdin, hPutStr, hIsTerminalDevice)

import CMDL.DataTypesUtils(generatePrompter)
import CMDL.DataTypes(CmdlState)
import CMDL.DgCommands(cUse)
import CMDL.Commands(shellacCommands, shellacEvalFunc)


stdShellDescription :: IO (ShellDescription CmdlState)
stdShellDescription = do
 isTerm <- hIsTerminalDevice stdin
 let wbc = "\n\r\v\\"
 return initialShellDescription
          { shellCommands      = shellacCommands
          , commandStyle       = OnlyCommands
          , evaluateFunc       = shellacEvalFunc
          , wordBreakChars     = wbc
          , prompt             = if isTerm
                                   then return . generatePrompter
                                   else \_ -> return []
          , historyFile        = Just "consoleHistory.tmp"
          }


basicOutput :: BackendOutput -> IO ()
basicOutput (RegularOutput out) = putStr out
basicOutput (InfoOutput out)    = putStr out
basicOutput (ErrorOutput out)   = hPutStr stderr out


-- | Applies cUse to a list of input files
recursiveApplyUse::[String] -> CmdlState -> IO CmdlState
recursiveApplyUse ls state
 = case ls of
    []   -> return state
    l:ll -> cUse l state >>= recursiveApplyUse ll
