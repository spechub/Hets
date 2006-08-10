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
import Static.DevGraph
import Common.AnnoState
import Common.Lexer
import Text.ParserCombinators.Parsec
import PGIP.Parser_Syntax
import PGIP.Common
import Data.Maybe
import IO (hFlush, stdout)

scanPathFile::CharParser st String
scanPathFile 
     = many1 ( oneOf (caslLetters ++ ['0'..'9'] ++ ['-','_','.']))


scanAnyWord::CharParser st String
scanAnyWord
     = many1 (oneOf (caslLetters ++ ['0'..'9'] ++ ['_','\'','.','/']))

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

scanCommand::[String] -> AParser st [CmdParam]
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
                                 return ((UseProver v):vs)
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


checkCommand::[([String], InterpreterCmd)]->AParser st InterpreterCmd
checkCommand arg
 = case arg of 
    (descr, (CmdPS x _ )):list ->  
                   do
                      try ( do 
--                            putStr ("CmdPS with " ++ (show descr) ++ "\n")
                              ls<-scanCommand descr 
                              try (skip) <|> try (eof)
                              return (CmdPS x ls )
                          )
                    <|>
                      checkCommand list
    (descr, (CmdP x _)):list ->  
                   do
                      try ( do
--                            putStr ("CmdP with " ++ (show descr) ++ "\n")
                              ls<-scanCommand descr
                              try (skip) <|> try (eof)
                              return (CmdP x ls)
                          )
                    <|>
                      checkCommand list
    (descr, (CmdS x )):list -> 
                   do
                      try ( do 
--                            putStr ("CmdS with " ++ (show descr) ++ "\n")
                              scanCommand descr
                              try (skip) <|> try     (eof)
                              return (CmdS x )
                          )
                    <|>
                      checkCommand list
    (descr, (CmdT x _)):list -> 
                   do
                      try ( do 
--                            putStr ("CmdT with "++ (show descr) ++ "\n")
                              ls<-scanCommand descr
                              try (skip) <|> try(eof)
                              return (CmdT x ls)
                          )
                    <|>
                      checkCommand list
    (descr, (CmdSS x)):list -> 
                   do
                      try ( do 
                              scanCommand descr
                              try (skip) <|> try (eof)
                              return (CmdSS x)
                          )
                    <|>
                      checkCommand list
    (_, (CmdE _)):list -> checkCommand list 
    _:l                -> checkCommand l 
    []                 -> do
                             try (do 
                                    skip
                                    eof
                                    return EndOfCommands
                                 )
                           <|> 
                             try ( do
                                     eof
                                     return EndOfCommands
                                 )
                           <|>
                              try ( do
                                     let ls = ""
                                     scanAnyWords
                                     skip
                                     return (CmdE ls)
                                  )


parsingCommand::Int->AParser st InterpreterCmd
parsingCommand x
   = case x of 
       0 -> checkCommand commands
       _ -> do 
              checkCommand commands
              skip
              result<- parsingCommand (x-1)
              return result

parseScript :: Int -> String -> IO (Maybe [InterpreterCmd])
parseScript nb str
  = do 
     let x=runParser (parsingCommand nb) (emptyAnnos()) "" str
     case x of
       Left _  -> do
                   putStr "An error has occured \n"
                   return Nothing
       Right (CmdE _) -> 
                  do
--                 putStr ("_"++smt++"_\n"++str ++ "\n\n"++(show nb)++ "\n\n")
                   return (Nothing)
       Right EndOfCommands -> return (Just [])
       Right y -> do
                   z<-parseScript (nb+1) str
                   case z of
                      Nothing -> return Nothing
                      Just zz -> return (Just (y:zz))


getLibEnv::[Status]->Maybe (LIB_NAME,LibEnv)
getLibEnv ls 
      =  case ls of 
                 [] -> Nothing
                 (Env x y):_ -> let tmp = (x,y)
                                in  Just tmp
                 _:l  -> getLibEnv l


runScriptCommands::([InterpreterCmd],[Status]) -> IO  (Maybe (LIB_NAME,LibEnv))
runScriptCommands (arg,status)
  = case arg of
      [] -> return  $ getLibEnv status
      (CmdP fn x):ls -> do 
                         val<- fn x
                         let newStatus= update (val,status)
--                       putStr ("Command parameters " ++ (show x) ++ "\n") 
                         runScriptCommands (ls,newStatus)
      (CmdPS fn x):ls-> do
                         let val = fn (x,status)
                         let newStatus= update (val,status)
--                       putStr ("Command parameters " ++ (show x) ++ "\n")
                         runScriptCommands (ls,newStatus)
      (CmdS fn ):ls  -> do
                         let val= fn status
                         let newStatus= update(val,status)
                         runScriptCommands (ls, newStatus)
      (CmdT fn x):ls -> do
                         fn x
--                       putStr ("Command parameters "++ (show x) ++ "\n")
                         runScriptCommands (ls,status)
      (CmdSS fn ):ls -> do
                         fn status
--                       putStr "Command parameters : none \n"
                         runScriptCommands (ls, status)
      (CmdSIO fn):ls -> do 
                         val<-fn status
                         let newStatus = update (val,status)
                         runScriptCommands (ls, newStatus)
      (CmdE _):_     -> return Nothing
      EndOfCommands:_-> runScriptCommands ([], status)

runScriptLine :: [InterpreterCmd]->[Status] -> IO (Maybe [Status])
runScriptLine arg status
  = case arg of
      [] -> return (Just status)
      (CmdP fn x):ls  -> do 
                          val<- fn x
                          let newStatus= update (val,status)
--                        putStr ("Command parameters " ++ (show x) ++ "\n")
                          runScriptLine ls newStatus
      (CmdPS fn x):ls -> do
                          let val = fn (x,status)
                          let newStatus= update (val,status)
--                        putStr ("Command parameters " ++ (show x) ++ "\n")
                          runScriptLine ls newStatus 
      (CmdS fn ):ls   -> do
                          let val= fn status
                          let newStatus= update(val,status)
                          runScriptLine ls newStatus
      (CmdT fn x):ls  -> do
                          fn x
--                        putStr ("Command parameters "++ (show x) ++ "\n")
                          runScriptLine ls status
      (CmdSS fn ):ls  -> do
                          fn status
--                        putStr "Command parameters : none \n"
                          runScriptLine ls status 
      (CmdSIO fn):ls  -> do 
                          val <-fn status
                          let newStatus = update (val, status)
                          runScriptLine ls newStatus
      (CmdE _):_       -> return Nothing
      EndOfCommands:_  -> runScriptLine [] status


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

printHelp :: String
printHelp =
  "\n\n Hets Interactive mode. The available commads are \n\n"++
    "   use [PATH]\n" ++
   "   dg [DG-COMMAND] [GOAL*]\n" ++
   "   dg-all [DG-COMMAND]\n" ++
   "   show-dg-goals\n" ++
   "   show-theory-goals\n" ++
   "   show-theory\n" ++
   "   node-info\n" ++
   "   show-taxonomy\n" ++
   "   show-concepts\n" ++
   "   translate [COMORPHISM]\n" ++
   "   prover [PROVER]\n" ++
   "   proof-script [FORMULA] [PROOF-SCRIPT] end-script\n" ++
   "   cons-check PROVER\n" ++
   "   prove [FORMULA*] [AXIOM-SELECTION?]\n" ++
   "   prove-all [AXIOM-SELECTION?]\n" ++
   "   q/quit/exit\n\n" ++
   " AXIOM-SELECTION ::=\n" ++
   "   with FORMULA+\n" ++
   "   exlcuding FORMULA+\n\n" ++
   " DG-COMMAND ::=\n" ++
   "     auto\n" ++
   "     glob-subsume\n" ++
   "     glob-decomp\n"++
   "     loc-infer\n"++
   "     loc-decomp\n"++
   "     comp\n"++
   "     comp-new\n"++
   "     hide-thm\n"++
   "     thm-hide\n"++
   "     basic\n\n"++
   " For more information type details\n\n"

printDetails :: String 
printDetails =
   "\n\n Hets Interactive mode.The available gramma is\n\n" ++
--   " -- Commands for development graph mode\n" ++
   "   use [PATH]              -- open a file with a HetCASL library\n" ++
   "                           -- this will compute a development graph\n" ++
   "                           -- and a list of open proof obligations\n" ++
   "   dg [DG-COMMAND] [GOAL*] -- apply a proof step of the dg calculus\n" ++
   "   dg-all [DG-COMMAND]     -- same as dg, but for all open goals\n" ++
   "   show-dg-goals           -- display list of open dg goals\n" ++
--   " -- commands for theory mode\n" ++
   "   show-theory-goals       -- display list of theory goals\n" ++
   "   show-theory             -- show current theory and proof goals\n" ++
   "   node-info               -- show info about current\n" ++
   "                           -- dg node (name, origin, sublogic)\n"++
   "   show-taxonomy           -- show taxonomy graph\n" ++
   "   show-concepts           -- show conecpt graph\n" ++
   "   translate [COMORPHISM]  -- translate theory goals \n" ++
   "                           -- along comorphism\n" ++
   "   prover [PROVER]         -- select a prover\n" ++
   "   proof-script [FORMULA] [PROOF-SCRIPT] end-script\n" ++
   "                           -- process proof script for one goal\n" ++
   "   cons-check PROVER       -- check consistency\n" ++
--   " -- interactive commands for theory mode\n" ++
   "   prove [FORMULA*] [AXIOM-SELECTION?]\n" ++
   "   prove-all [AXIOM-SELECTION?]\n" ++
   "   q/quit/exit             -- exit hets\n\n" ++
   " AXIOM-SELECTION ::=\n" ++
   "   with FORMULA+           -- include only specified axioms\n" ++
   "   exlcuding FORMULA+      -- exlcude specified axioms\n\n" ++
   " PROOF-SCRIPT        -- can be anything (prover specific)\n" ++
   "                     -- the end is recognized with \"end-script\"\n\n" ++
   " DG-COMMAND ::= \n" ++
   "     auto          -- automatic tactic\n" ++
   "     glob-subsume -- global subsumption\n" ++
   "     glob-decomp  -- global decomposition\n"++
   "     loc-infer    -- local inference\n"++
   "     loc-decomp   -- local decomposition\n"++
   "     comp         -- composition\n"++
   "     comp-new     -- composition with speculation of new egdes\n"++
   "     hide-thm     -- Hide-Theorem-Shift\n"++
   "     thm-hide     -- Theorem-Hide-Shift\n"++
   "     basic        -- start proving at a particular node,\n"++
   "                  -- i.e. start local proving in a theory\n\n"++
   " GOAL ::=  \n"++
   "   NODE                   -- select local goals at a node\n"++
   "   NODE -> NODE           -- select all edges between two given nodes\n"++
   "   NODE - DIGIT* -> NODE  -- select specific edge between two nodes\n"++
   "\n NODE ::= \n"++
   "     ID         -- specify nodes with their names\n\n"++
   " COMORPHISM ::= ID ; ... ; ID    -- composite of basic comorphisms\n\n"++
   " PROVER ::= ID                   -- name of prover\n\n"++
   " FORMULA ::= ID                  -- label of formula\n\n"++
   " ID ::=                          -- identifier (String)\n\n"

	
takeName :: String -> String
takeName ls
  = case ls of
      '.':_ -> []
      x :l  -> x:(takeName l)
      _     -> []
					 					 
combine :: [String] -> String
combine ls
  = case ls of
     x:[]-> (takeName x) ++ (combine [])
     x:l -> x ++ "/" ++ (combine l)
     []  -> "> "


getFileUsed :: [Status] -> String
getFileUsed ls
 = case ls of
      (Address adr):_ -> combine adr
      _:l                -> getFileUsed l
      []                 -> "Hets>"

extractFirstWord :: String -> String
extractFirstWord ls
 = case ls of
     ' ':_ -> []
     x:l   -> x:(extractFirstWord l)
     _     -> []



runInteractive :: [Status] -> IO (Maybe (LIB_NAME, LibEnv))
runInteractive status =
    do
     let promter=getFileUsed status 
     putStr promter
     IO.hFlush IO.stdout
     line<-getLine
   
     let wd = extractFirstWord line
     case wd of
       "q"       -> return $ getLibEnv status
       ":q"      -> return $ getLibEnv status
       "exit"    -> return $ getLibEnv status
       "quit"    -> return $ getLibEnv status
       "details" -> do
                      putStr printDetails
                      runInteractive status
       "h"    -> do
                     putStr printHelp
                     runInteractive status
       "?"    -> do 
                     putStr printHelp
                     runInteractive status
       "help" -> do 
                     putStr printHelp
                     runInteractive status
       _ ->
         do r<-parseScript 0 line
            case r of
             Just out ->
               do
                tmp <-  runScriptLine out status
                let nwStatus = fromJust tmp
                runInteractive nwStatus
             Nothing -> 
               do
                putStr "Error, couldn't parse input \n"
                putStr "Please type help for more information\n"
                runInteractive status


