{- |
Module      :$Header$
Description : The definition of CMDL interface for
              standard input and file input
Copyright   : uni-bremen and DFKI
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.CMDLStdin describes the interface specific function
for standard input and file input
-}

module PGIP.Interface where


import System.Console.Shell
import System.Console.Shell.Backend
import System.Console.Shell.Backend.Readline
import System.Console.Shell.ShellMonad
import System.IO

import PGIP.Shell
import PGIP.DataTypes
import PGIP.Commands
import PGIP.DgCommands


import qualified Control.Exception as Ex


shellacInp :: CMDL_CmdDescription -> String -> Sh CMDL_State ()
shellacInp descr inp
 = let inf = cmdInfo descr
   in shellacCmd descr {cmdInfo = inf {cmdInput = inp} }

-- | Generates the list of all the shell commands toghether
-- with a short description
cmdlCommands :: [ShellCommand CMDL_State]
cmdlCommands
 = let genCmds = concatMap (\x ->
              map (\y-> case cmdFn x of
                         CmdNoInput _ ->
                           cmd y (shellacCmd x) (cmdDescription x)
                         CmdWithInput _ ->
                           cmd y (shellacInp x) (cmdDescription x)
                             )$ cmdNames $ cmdInfo x) getCommands
   in
    -- different names for exit commands
      (exitCommand "exit")
    : (exitCommand "quit")
    -- also vi style
    : (exitCommand ":q")
    -- different name for help commands
    : (helpCommand "help")
    -- also ? for help
    : (helpCommand "?")
    : genCmds


-- | Creates the Backend for reading from files
fileBackend :: String -> ShellBackend Handle
fileBackend filename = ShBackend
  { initBackend = openFile filename ReadMode
  , shutdownBackend = hClose
  , outputString = \_ -> basicOutput
  , flushOutput = \_ -> hFlush stdout
  , getSingleChar = fileGetSingleChar
  , getInput = fileGetInput
  , addHistory = \_ _ -> return ()
  , setWordBreakChars = \_ _ -> return ()
  , getWordBreakChars = \_ -> return
                      " \t\n\r\v`~!@#$%^&*()=[]{};\\\'\",<>"
  , onCancel = \_ -> hPutStrLn stdout "canceled...\n"
  , setAttemptedCompletionFunction = \_ _ -> return ()
  , setDefaultCompletionFunction = \_ _ -> return ()
  , completeFilename = \_ _ -> return []
  , completeUsername = \_ _ -> return []
  , clearHistoryState = \_ -> return ()
  , getMaxHistoryEntries = \_ -> return 0
  , setMaxHistoryEntries = \_ _ -> return ()
  , readHistory = \_ _ -> return ()
  , writeHistory = \_ _ -> return ()
  }

-- | Used to get one char from a file open for reading
fileGetSingleChar :: Handle -> String -> IO (Maybe Char)
fileGetSingleChar file _
 = do
    Ex.bracket (hGetBuffering file) (hSetBuffering file) $
         \_ -> do
                hSetBuffering file NoBuffering
                c <- hGetChar file
                hPutStrLn stdout ""
                return (Just c)

-- | Used to get a line from a file open for reading
fileGetInput :: Handle -> String -> IO (Maybe String)
fileGetInput file _ = do
   x <- hGetLine file
   return (Just x)

basicOutput :: BackendOutput -> IO ()
basicOutput (RegularOutput out) = hPutStr stdout out
basicOutput (InfoOutput out)    = hPutStr stdout out
basicOutput (ErrorOutput out)   = hPutStr stderr out


cmdlShellDescription :: ShellDescription CMDL_State
cmdlShellDescription =
 let wbc = "\n\r\v\\" in
      initialShellDescription
       { shellCommands      = cmdlCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = shellacInp cmdlEvalFunc
       , wordBreakChars     = wbc
       , prompt             = \x -> return (prompter x)
       , historyFile        = Just ("consoleHistory.tmp")
       }

cmdlFileShellDescription :: ShellDescription CMDL_State
cmdlFileShellDescription =
 let wbc = "\t\n\r\v\\" in
      initialShellDescription
       { shellCommands      = cmdlCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = shellacInp cmdlEvalFunc
       , wordBreakChars     = wbc
       , prompt             = \_ -> return ""
       , historyFile        = Just ("consoleHistory.tmp")
       }


-- | Applies cUse to a list of input files
recursiveApplyUse::[String] -> CMDL_State -> IO CMDL_State
recursiveApplyUse ls state
 = case ls of
    []   -> return state
    l:ll -> do
             nwState <- cUse l state
             recursiveApplyUse ll nwState


emptyCMDL_State ::  CMDL_State
emptyCMDL_State =
   CMDL_State {
     devGraphState = Nothing,
     proveState = Nothing,
     prompter = " > ",
     output = CMDL_Output {
                 errorMsg   = [],
                 outputMsg  = [],
                 fatalError = False
                  },
     history = CMDL_History {
                 undoList      = [],
                 redoList      = [],
                 oldEnv        = Nothing,
                 undoInstances = [],
                 redoInstances = []
                 },
      openComment = False,
      connections = []
     }

-- | The function runs hets in a shell
cmdlRunShell :: [String] ->IO CMDL_State
cmdlRunShell files
   = do
      state <- recursiveApplyUse  files emptyCMDL_State
      runShell cmdlShellDescription
                {defaultCompletions= Just (cmdlCompletionFn getCommands) }
              readlineBackend
              state

-- | The function processes the file of instructions
cmdlProcessFile :: String -> IO CMDL_State
cmdlProcessFile filename =
        (runShell cmdlFileShellDescription
                 (fileBackend filename)
                 emptyCMDL_State) `catch`
                               (\_ -> return emptyCMDL_State )


