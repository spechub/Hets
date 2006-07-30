{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Parsing the comand line script.

  TODO :
          - add comments to the code
          - delete the test functions

-} 

module PGIP.Command_Parser where

import Syntax.AS_Library
import Syntax.Parse_AS_Library
import Static.DevGraph
import Static.AnalysisLibrary
import Common.AnnoState
import Common.Lexer
import Common.Token
import Common.Id
import Text.ParserCombinators.Parsec
import PGIP.Parser_Syntax
import PGIP.Commands
import PGIP.Common
import Data.Maybe
import IO (hFlush, stdout)

scanPathFile::CharParser st String
scanPathFile 
             = many1 ( oneOf (caslLetters ++ ['0'..'9'] ++ ['-','_','.']))


scanAnyWord::CharParser st String
scanAnyWord
        = many1 (oneOf (caslLetters ++ ['0'..'9'] ++ ['-','_','\'','.','/']))

-- |the 'getPath' function read a path as a a list of words
getPath::AParser st [String]
getPath 
        = try ( do  
                    v<-sepBy1 scanPathFile (string "/")
                    return v
              )
      <|> 
          try ( do  skip
                    v<-sepBy1 scanPathFile (string "/")
                    return v
              )
      <?> 
          "path"
-- |the 'getKeyWord' function accepts a string as argument and tries to read it
getKeyWord::String -> AParser st String
getKeyWord wd 
              =  try ( string wd
                     ) 
              <|> 
                 try ( do  skip 
                           string wd
                     )
              <?> ("keyword "++wd)
                       
getGoal::AParser st GOAL
getGoal        
       = try ( do  v1<-scanAnyWord
                   getKeyWord "-"
                   v2<-getNumber
                   getKeyWord "->"
                   v3<-scanAnyWord
                   return (LabeledEdge v1 (read v2::Int) v3)
             )       
      <|> 
         try ( do  v1<-scanAnyWord
                   getKeyWord "->"                                  
                   v2<-scanAnyWord
                   return (Edge  v1  v2)
             )
      <|> 
         try ( do  v<-scanAnyWord
                   return (Node  v)
             )   
      <?>
         "goal"    

getScript::AParser st String
getScript 
         = try ( do  getKeyWord "end-script"
                     return ""
               )
        <|> 
           try ( do  v<-scanAnyWord
                     vs <-getScript
                     return (v++" "++vs)
               )
        <|>
           try ( do  skip
                     v<-scanAnyWord
                     vs<-getScript
                     return (v++" "++vs)
               )
        <?> 
           "some prover script"
                                        
getComorphism::AParser st [String]
getComorphism 
             = try ( do  v<-scanAnyWord
                         getKeyWord ";"
                         vs <-getComorphism
                         return ( v:vs)
                   )
            <|>
               try ( do  v<-scanAnyWord
                         return [ v]
                   )
            <?>
               " list of ID's separated by semicolon"

scanCommand::[String] -> AParser st [ScriptCommandParameters]
scanCommand arg 
               = case arg of
                          []  ->  do 
                                 string ""
                                 return []
--- scanning a path
                          "PATH":ls  ->  do
                                 v <- getPath 
                                 vs<- scanCommand ls
                                 return ((Path v):vs)
--- scanning a prover
                          "PROVER":ls  ->  do
                                 v <- scanAnyWord 
                                 vs<- scanCommand ls
                                 return ((Prover v):vs)
--- scanning a formula
                          "FORMULA":ls  ->  do
                                 v <- scanAnyWord 
                                 vs<- scanCommand ls
                                 return ((Formula  v):vs)
--- scanning a comorphism
                          "COMORPHISM":ls  ->  do
                                 v <- getComorphism 
                                 vs<-scanCommand ls
                                 return ((ParsedComorphism v):vs)
--- scanning goals
                          "GOALS":ls  ->  do
                                 v<-many getGoal
                                 vs<- scanCommand ls
                                 return ((Goals v):vs)
--- scanning none or many formulas
                          "FORMULA-STAR":ls  ->  do
                                 v<- many ( do  tmp<-scanAnyWord
                                                return  tmp
                                          )
                                 vs<-scanCommand ls
                                 return  ((Formulas v):vs)
--- scanning one or more formula
                          "FORMULA-PLUS":ls  ->  do
                                 v<- many1 ( do  tmp<-scanAnyWord
                                                 return tmp
			                   )
			         vs<-scanCommand ls
			         return ((Formulas v):vs)
--- scanning proof script
                          "PROOF-SCRIPT":ls  ->  do
                                 v<- getScript
                                 vs <-scanCommand ls
                                 return ((ProofScript v):vs)
--- scanning keywords
                          keyword:ls  ->  do
                                 getKeyWord keyword
                                 vs<- scanCommand ls
                                 return vs

printSomething :: String -> IO()
printSomething y = putStr y

checkCommand::[([String], CommandFunctionsAndParameters)]->AParser st CommandFunctionsAndParameters
checkCommand arg
                = case arg of 
                        (command_description, (CommandParamStatus x _ )):command_list ->  do
                                      try ( do 
--                                               putStr ("CommandParamStatus with description " ++ (show command_description) ++ "\n")
                                               ls<-scanCommand command_description 
                                               try (skip) <|> try (eof)
                                               return (CommandParamStatus x ls )
                                          )
                                   <|>
                                      checkCommand command_list
                        (command_description, (CommandParam x _)):command_list ->  do
                                      try ( do
--                                               putStr ("CommandParam with description " ++ (show command_description) ++ "\n")
                                               ls<-scanCommand command_description
                                               try (skip) <|> try (eof)
                                               return (CommandParam x ls)
                                          )
                                   <|>
                                      checkCommand command_list
                        (command_description, (CommandStatus x )):command_list -> do
                                      try ( do 
--                                               putStr ("CommandStatus with description " ++ (show command_description) ++ "\n")
                                               scanCommand command_description
                                               try (skip) <|> try     (eof)
                                               return (CommandStatus x )
                                          )
                                   <|>
                                      checkCommand command_list
                        (command_description, (CommandTest x _)):command_list -> do
                                      try ( do 
--                                               putStr ("CommandTest with description "++ (show command_description) ++ "\n")
                                               ls<-scanCommand command_description
                                               try (skip) <|> try(eof)
                                               return (CommandTest x ls)
                                          )
                                   <|>
                                      checkCommand command_list
                        (command_description, (CommandShowStatus x)):command_list -> do
                                      try ( do 
                                              ls<-scanCommand command_description
                                              try (skip) <|> try (eof)
                                              return (CommandShowStatus x)
                                          )
                                   <|>
                                      checkCommand command_list
                        (_, (CommandError _)):command_list -> checkCommand command_list 
                        _:l -> checkCommand l 
                        []  -> do
                                      let ls = ""
                                      try (scanAnyWords ) <|> (do eof
                                                                  return "")
                                      return (CommandError ls)
                    


parseCommand::Int->AParser st CommandFunctionsAndParameters
parseCommand x
            = case x of 
                     0 -> checkCommand commands
                     _ -> do 
                           checkCommand commands
                           skip
                           x<- parseCommand (x-1)
                           return x

parseScript :: Int -> String -> IO (Maybe [CommandFunctionsAndParameters])
parseScript nb str
          = do 
            let x=runParser (parseCommand nb) (emptyAnnos()) "" str
            case x of
                Left _ -> do
                           putStr "An error has occured \n"
                           return Nothing
                Right (CommandError smt) -> do
--                                      putStr ("_"++smt++"_\n"++str ++ "\n\n"++(show nb)++ "\n\n")
                                      return (Just [])
                Right y            -> do
                                        
                                       z<-parseScript (nb+1) str
                                       case z of
                                            Nothing -> return Nothing
                                            Just zz -> return (Just (y:zz))


getLibEnv::[CmdInterpreterStatus]->Maybe (LIB_NAME,LibEnv)
getLibEnv ls =
          case ls of 
                 [] -> Nothing
                 (Env x y):_ -> let tmp = (x,y)
                                in  Just tmp
                 _:l  -> getLibEnv l
runScriptCommands::([CommandFunctionsAndParameters],[CmdInterpreterStatus]) -> IO (Maybe (LIB_NAME,LibEnv))
runScriptCommands (arg,status)
                     = case arg of
                              [] -> return $ getLibEnv status
                              (CommandParam fn x):ls -> do 
                                                       val<- fn x
                                                       let newStatus= addOrReplace (val,status)
--                                                       putStr ("Command parameters " ++ (show x) ++ "\n") 
                                                       runScriptCommands (ls,newStatus)
                              (CommandParamStatus fn x ):ls -> do
                                                       let val = fn (x,status)
                                                       let newStatus= addOrReplace (val,status)
--                                                       putStr ("Command parameters " ++ (show x) ++ "\n")
                                                       runScriptCommands (ls,newStatus)
                              (CommandStatus fn ):ls -> do
                                                       let val= fn status
                                                       let newStatus= addOrReplace(val,status)
                                                       runScriptCommands (ls, newStatus)
                              (CommandTest fn x):ls -> do
                                                       fn x
--                                                       putStr ("Command parameters "++ (show x) ++ "\n")
                                                       runScriptCommands (ls,status)
                              (CommandShowStatus fn ):ls -> do
                                                       fn status
--                                                       putStr "Command parameters : none \n"
                                                       runScriptCommands (ls, status)
                              (CommandStatusIO fn):ls  -> do 
                                                           val<-fn status
                                                           let newStatus = addOrReplace (val,status)
                                                           runScriptCommands (ls, newStatus)
                              CommandError _:_ -> return Nothing

runScriptLine :: [CommandFunctionsAndParameters]->[CmdInterpreterStatus] -> IO (Maybe [CmdInterpreterStatus])
runScriptLine arg status
           = case arg of
             [] -> return (Just status)
             (CommandParam fn x):ls -> do 
                                        val<- fn x
                                        let newStatus= addOrReplace (val,status)
--                                        putStr ("Command parameters " ++ (show x) ++ "\n") 
                                        runScriptLine ls newStatus
             (CommandParamStatus fn x ):ls -> do
                                               let val = fn (x,status)
                                               let newStatus= addOrReplace (val,status)
--                                               putStr ("Command parameters " ++ (show x) ++ "\n")
                                               runScriptLine ls newStatus 
             (CommandStatus fn ):ls -> do
                                        let val= fn status
                                        let newStatus= addOrReplace(val,status)
                                        runScriptLine ls newStatus
             (CommandTest fn x):ls -> do
                                       fn x
--                                       putStr ("Command parameters "++ (show x) ++ "\n")
                                       runScriptLine ls status
             (CommandShowStatus fn ):ls -> do
                                            fn status
--                                            putStr "Command parameters : none \n"
                                            runScriptLine ls status 
             (CommandStatusIO fn):ls    -> do 
                                             val <-fn status
                                             let newStatus = addOrReplace (val, status)
                                             runScriptLine ls newStatus
             CommandError _:_ -> return Nothing


parseScriptFile:: FilePath-> IO (Maybe (LIB_NAME,LibEnv))
parseScriptFile fileName
                        = do 
                            input<- readFile fileName
--                            let r=runParser (parseScript [])  (emptyAnnos()) "" input
                            r<-parseScript 0  input
                            case r of
                               Just out-> do
                                           putStr "File parsed.Executing...\n"
                                           x<-runScriptCommands (out,[])
                                           return x
                                             
                               Nothing -> do
                                          putStr "An error has occured\n"
                                          return Nothing 


						 					 


runInteractive :: [CmdInterpreterStatus] -> IO (Maybe (LIB_NAME, LibEnv))
runInteractive status =
                 do 
                   putStr "Hets> "
                   IO.hFlush IO.stdout
                   x<-getLine
                   if (x=="q") then return $ getLibEnv status
                               else do r<-parseScript 0 x
                                       case r of
                                          Just out ->do
                                                     tmp <-  runScriptLine out status
                                                     let nwStatus = fromJust tmp
                                                     runInteractive nwStatus
                                          Nothing -> do
                                                      putStr "Error, couldn't parse input \n"
                                                      runInteractive status


