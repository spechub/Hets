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


import System.Console.Shell
import System.Console.Shell.Backend
import System.IO

import CMDL.DataTypes
import CMDL.DataTypesUtils
import CMDL.Commands
import CMDL.DgCommands


stdShellDescription :: ShellDescription CMDL_State
stdShellDescription =
 let wbc = "\n\r\v\\" in
      initialShellDescription
       { shellCommands      = shellacCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = shellacEvalFunc
       , wordBreakChars     = wbc
       , prompt             = return . generatePrompter
       , historyFile        = Just "consoleHistory.tmp"
       }


basicOutput :: BackendOutput -> IO ()
basicOutput (RegularOutput out) = putStr out
basicOutput (InfoOutput out)    = putStr out
basicOutput (ErrorOutput out)   = hPutStr stderr out


-- | Applies cUse to a list of input files
recursiveApplyUse::[String] -> CMDL_State -> IO CMDL_State
recursiveApplyUse ls state
 = case ls of
    []   -> return state
    l:ll -> do
             nwState <- cUse l state
             recursiveApplyUse ll nwState
