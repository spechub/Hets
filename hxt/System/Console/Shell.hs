{-
 -
 -  Copyright 2005-2006, Robert Dockins.
 -
 -}

{- | This module implements a framework for creating read-eval-print style
     command shells.  Shells are created by declaratively defining evaluation
     functions and \"shell commands\".  Input is read using a plugable backend.
     The shell framework handles command history and word completion if the
     backend supports it.

     The basic idea is for creating a shell is:

      (1) Create a list of shell commands and an evaluation function

      (2) Create a shell description (using 'mkShellDescription')

      (3) Set up the initial shell state

      (4) Run the shell (using 'runShell')
-}


module System.Console.Shell (

-- * Shell Descriptions
  ShellDescription (..)
, initialShellDescription
, mkShellDescription
, defaultExceptionHandler

-- * Executing Shells
, runShell

-- * Creating Shell Commands
, exitCommand
, helpCommand
, toggle
, cmd
, CommandFunction (..)
, File (..)
, Username (..)
, Completable (..)
, Completion (..)
, ShellCommand

-- * Subshells
, Subshell
, simpleSubshell

-- * Printing Help Messages
, showShellHelp
, showCmdHelp

-- * Generating text output
, shellPutStr
, shellPutStrLn
, shellPutInfo
, shellPutInfoLn
, shellPutErr
, shellPutErrLn

-- * Auxiliary Types
, CommandStyle (..)
, ShellSpecial (..)
, OutputCommand
, CommandResult
) where

import System.Console.Shell.Types
import System.Console.Shell.ShellMonad
import System.Console.Shell.Commands
import System.Console.Shell.RunShell


-- | A basic shell description with sane initial values
initialShellDescription :: ShellDescription st
initialShellDescription =
  let wbc = " \t\n\r\v`~!@#$%^&*()=[]{};\\\'\",<>" in
    ShDesc
       { shellCommands      = []
       , commandStyle       = CharPrefixCommands ':'
       , evaluateFunc       = \_ -> return ()
       , wordBreakChars     = wbc
       , beforePrompt       = return ()
       , prompt             = \_ -> return "> "
       , exceptionHandler   = defaultExceptionHandler
       , defaultCompletions = Just (\_ _ -> return [])
       , historyFile        = Nothing
       , maxHistoryEntries  = 100
       , historyEnabled     = True
       }


-- | Creates a simple shell description from a list of shell commmands and
--   an evalation function.
mkShellDescription :: [ShellCommand st]
                   -> (String -> Sh st ())
                   -> ShellDescription st

mkShellDescription cmds func =
   initialShellDescription
      { shellCommands = cmds
      , evaluateFunc  = func
      }
