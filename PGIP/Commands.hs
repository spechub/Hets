{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Function that executes the script commands together with the datatypes used.

 TODO :
      - add comments
      - implement the rest of the functions 
      - delete the test function
-} 

module PGIP.Commands where

import Syntax.AS_Library
import Static.AnalysisLibrary
import Static.DevGraph
import Driver.Options
import Common.Utils

data GOAL = 
   Node         LIB_ID
 | Edge         LIB_ID   LIB_ID
 | CountedEdge  LIB_ID   Int       LIB_ID
 deriving (Eq,Show)


data ScriptCommandParameters =
   Path                         [String] 
 | Formula                       LIB_ID 
 | Prover                        LIB_ID
 | Goals                         [GOAL]
 | ParsedComorphism             [LIB_ID]
 | AxiomSelectionWith           [LIB_ID]
 | AxiomSelectionExcluding      [LIB_ID]
 | Formulas                     [LIB_ID]
 | ProofScript                   String
 | ParamErr                      String
 | NoParam
 deriving (Eq,Show)

data CmdInterpreterStatus = 
   OutputErr  String
 | CmdInitialState
 | Env     LIB_NAME LibEnv


data CmdInterpreterStatusID =
   EnvID
 
data CommandFunctionsAndParameters=
   CommandIO             ([ScriptCommandParameters]->IO CmdInterpreterStatus) [ScriptCommandParameters] 
 | CommandIOParam        (([ScriptCommandParameters],CmdInterpreterStatus)-> IO CmdInterpreterStatus) [ScriptCommandParameters] CmdInterpreterStatusID 
 | CommandTest           ([ScriptCommandParameters]->IO())  [ScriptCommandParameters]
 | CommandError



test::([ScriptCommandParameters])->IO()
test (ls) = putStrLn $ show ls
               

commandUse::[ScriptCommandParameters]->IO CmdInterpreterStatus
commandUse ls 
            = case ls of
                (Path list):_ -> do
                                  let file = joinWith '/' list
                                  let opts = defaultHetcatsOpts
                                  result<- anaLib opts file
                                  case result of
                                      Just (name,env) ->  return (Env name env) 
                                      Nothing ->  return (OutputErr "Couldn't load the file specified")
                _ -> return (OutputErr "Wrong parameter") 

commandDgAuto::([ScriptCommandParameters],CmdInterpreterStatus) -> IO CmdInterpreterStatus
commandDgAuto ls x
                 = case ls of 
                        
           
