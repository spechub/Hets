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
import Common.AnnoState
import Common.Lexer
import Common.Token
import Common.Id
import Text.ParserCombinators.Parsec
import PGIP.Parser_Syntax
import PGIP.Commands
import PGIP.Common


pgipKeywords::[String]
pgipKeywords = ["dg","dg-all","show-dg-goals","show-theory-goals","show-theory","node-info","show-taxonomy","show-concepts",
                "translate","prover","proof-script","cons-check","prove","prove-all","use","auto","glob-subsume","glob-decomp",
                "loc-infer","loc-decomp","comp","comp-new","hide-thm","thm-hide","basic","using","excluding","end-script"]

-- |the 'getPath' function read a path as a a list of words
getPath::AParser st [String]
getPath 
        = try ( do  v<-scanAnyWords `sepBy1` (string "/")
                    return v
              )
      <|> 
          try ( do  skip
                    v<- scanAnyWords `sepBy1` (string "/")
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
       = try ( do  v1<-sortId pgipKeywords
                   getKeyWord "-"
                   v2<-getNumber
                   getKeyWord "->"
                   v3<-sortId pgipKeywords
                   return (LabeledEdge v1 (read v2::Int) v3)
             )       
      <|> 
         try ( do  v1<-sortId pgipKeywords
                   getKeyWord "->"                                  
                   v2<-sortId pgipKeywords
                   return (Edge  v1  v2)
             )
      <|> 
         try ( do  v<-sortId pgipKeywords
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
           try ( do  v<-scanAnyWords
                     vs <-getScript
                     return (v++" "++vs)
               )
        <|>
           try ( do  skip
                     v<-scanAnyWords
                     vs<-getScript
                     return (v++" "++vs)
               )
        <?> 
           "some prover script"
                                        
getComorphism::AParser st [Id]
getComorphism 
             = try ( do  v<-sortId pgipKeywords
                         getKeyWord ";"
                         vs <-getComorphism
                         return ( v:vs)
                   )
            <|>
               try ( do  v<-sortId pgipKeywords
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
                                 v <- sortId pgipKeywords 
                                 vs<- scanCommand ls
                                 return ((Prover v):vs)
--- scanning a formula
                          "FORMULA":ls  ->  do
                                 v <- sortId pgipKeywords 
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
                                 v<- many ( do  tmp<-sortId pgipKeywords
                                                return  tmp
                                          )
                                 vs<-scanCommand ls
                                 return  ((Formulas v):vs)
--- scanning one or more formula
                          "FORMULA-PLUS":ls  ->  do
                                 v<- many1 ( do  tmp<-sortId pgipKeywords
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

checkCommand::[([String], CommandFunctionsAndParameters)]->AParser st CommandFunctionsAndParameters
checkCommand arg
                = case arg of 
                        (command_description, (CommandParamStatus x _ cmdID)):command_list ->  do
                                      try ( do 
                                               ls<-scanCommand command_description 
                                               try (skip) <|> try (eof)
                                               return (CommandParamStatus x ls cmdID)
                                          )
                                   <|>
                                      checkCommand command_list
                        (command_description, (CommandParam x _)):command_list ->  do
                                      try ( do
                                               ls<-scanCommand command_description
                                               try (skip) <|> try (eof)
                                               return (CommandParam x ls)
                                          )
                                   <|>
                                      checkCommand command_list
                        (command_description, (CommandStatus x cmdID)):command_list -> do
                                      try ( do 
                                               scanCommand command_description
                                               try (skip) <|> try     (eof)
                                               return (CommandStatus x cmdID)
                                          )
                                   <|>
                                      checkCommand command_list
                        (command_description, (CommandTest x _)):command_list -> do
                                      try ( do 
                                               ls<-scanCommand command_description
                                               try (skip) <|> try(eof)
                                               return (CommandTest x ls)
                                          )
                                   <|>
                                      checkCommand command_list
                        (_, CommandError):command_list -> checkCommand command_list   
                        []  -> do
                                      scanAnyWords 
                                      return CommandError 
                    

parseScript::AParser st [CommandFunctionsAndParameters]
parseScript 
            = do
                ls <-many (checkCommand commands)
                try (eof) <|> try  ( do skip 
                                        eof
                                   )
                return ls

runScriptCommands::([CommandFunctionsAndParameters],[CmdInterpreterStatus]) -> IO (Maybe ())
runScriptCommands (arg,status)
                     = case arg of
                              [] -> return (Just ())
                              (CommandParam fn x):ls -> do 
                                                       val<- fn x
                                                       let newStatus= addOrReplace (val,status)
                                                       runScriptCommands (ls,newStatus)
                              (CommandParamStatus fn x cmdID):ls -> do
                                                       let tmp = extractFrom (status,cmdID)
                                                       case tmp of
                                                            Nothing -> return Nothing
                                                            Just xx -> do
                                                                        let val = fn (x,xx)
                                                                        let newStatus= addOrReplace (val,status)
                                                                        runScriptCommands (ls,newStatus)
                              (CommandStatus fn cmdID):ls -> do
                                                       let tmp = extractFrom (status,cmdID)
                                                       case tmp of 
                                                            Nothing -> return Nothing
                                                            Just xx -> do
                                                                         let val= fn xx
                                                                         let newStatus= addOrReplace(val,status)
                                                                         runScriptCommands (ls, newStatus)
                              (CommandTest fn x):ls -> do
                                                       fn x
                                                       runScriptCommands (ls,status)
                              CommandError:_ -> return Nothing

parseScriptFile:: FilePath-> IO (Maybe())
parseScriptFile fileName
                        = do 
                            input<- readFile fileName
                            let r=runParser parseScript (emptyAnnos()) "" input
                            case r of
                               Right out-> do 
                                           runScriptCommands (out,[])
                                             
                               Left _ -> 
                                          return Nothing 


						 					 


