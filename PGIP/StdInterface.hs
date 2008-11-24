{- |
Module      : $Header$
Description : The definition of standard input\/output interface
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.StdInterface describes the interface specific function
for standard input and file input
-}

module PGIP.StdInterface
       ( stdShellDescription
       , basicOutput
       , recursiveApplyUse
       )where


import System.Console.Shell
import System.Console.Shell.Backend
import System.IO

import PGIP.DataTypes
import PGIP.DataTypesUtils
import PGIP.Commands
import PGIP.DgCommands


stdShellDescription :: ShellDescription CMDL_State
stdShellDescription =
 let wbc = "\n\r\v\\" in
      initialShellDescription
       { shellCommands      = shellacCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = shellacEvalFunc
       , wordBreakChars     = wbc
       , prompt             = \x -> return $ generatePrompter x
       , historyFile        = Just ("consoleHistory.tmp")
       }


basicOutput :: BackendOutput -> IO ()
basicOutput (RegularOutput out) = hPutStr stdout out
basicOutput (InfoOutput out)    = hPutStr stdout out
basicOutput (ErrorOutput out)   = hPutStr stderr out


-- | Applies cUse to a list of input files
recursiveApplyUse::[String] -> CMDL_State -> IO CMDL_State
recursiveApplyUse ls state
 = case ls of
    []   -> return state
    l:ll -> do
             nwState <- cUse l state
             recursiveApplyUse ll nwState
