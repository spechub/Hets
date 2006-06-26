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
import Proofs.Automatic
import Proofs.Global
import Proofs.Local
import Proofs.Composition
import Proofs.HideTheoremShift
import Proofs.TheoremHideShift
--import Proofs.InferBasic


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
   CommandParam        ([ScriptCommandParameters]->IO CmdInterpreterStatus) [ScriptCommandParameters] 
 | CommandParamStatus  (([ScriptCommandParameters],CmdInterpreterStatus)-> IO CmdInterpreterStatus) [ScriptCommandParameters] CmdInterpreterStatusID 
 | CommandStatus       (CmdInterpreterStatus -> CmdInterpreterStatus) CmdInterpreterStatusID
 | CommandTest         ([ScriptCommandParameters]->IO())  [ScriptCommandParameters]
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

commandDgAllAuto::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllAuto arg
                 = case arg of
                      (Env x y) -> let result= (automatic x) y in
                                       (Env x result)
                      _ -> (OutputErr "Wrong parameter")


commandDgAllGlobSubsume::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllGlobSubsume arg
                          = case arg of
                               (Env x y) -> let result =(globSubsume x) y in
                                                (Env x result)
                               _ -> (OutputErr "Wrong parameters")

commandDgAllGlobDecomp::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllGlobDecomp arg 
                          = case arg of 
                               (Env x y) -> let result= (globDecomp x) y in
                                                (Env x result)
                               _ -> (OutputErr "Wrong parameters")

commandDgAllLocInfer::CmdInterpreterStatus -> CmdInterpreterStatus                        
commandDgAllLocInfer arg
                        = case arg of
                             (Env x y) -> let result= (localInference x) y in
                                              (Env x result)
                             _ -> (OutputErr "Wrong parameters")

commandDgAllLocDecomp::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllLocDecomp arg
                         = case arg of 
                               (Env x y) -> let result= (locDecomp x) y in
                                                (Env x result)
                               _-> (OutputErr "Wrong parameters")

commandDgAllComp::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllComp arg 
                    = case arg of
                           (Env x y) -> let result= (composition x) y in
                                            (Env x result)
                           _ -> (OutputErr "Wrong parameters")

commandDgAllCompNew::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllCompNew arg
                      = case arg of
                             (Env x y) -> let result=(compositionCreatingEdges x) y in
                                              (Env x result)
                             _ -> (OutputErr "Wrong parameters")

commandDgAllHideThm::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllHideThm arg
                      = case arg of
                             (Env x y) -> let result= (automaticHideTheoremShift x) y in
                                              (Env x result)
                             _-> (OutputErr "Wrong parameters")

commandDgAllThmHide::CmdInterpreterStatus -> CmdInterpreterStatus
commandDgAllThmHide arg
                       = case arg of
                              (Env x y) -> let result=(theoremHideShift x) y in
                                               (Env x result)
                              _-> (OutputErr "Wrong parameters")

  

