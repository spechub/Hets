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

import Common.AnnoState
import Common.Lexer
import Text.ParserCombinators.Parsec
import PGIP.Commands
import PGIP.Common
import Data.Maybe
import Shell.Backend.Readline
import Shell.ShellMonad
import Shell
import Control.Monad.Trans

data OutputScan = 
    Out CmdParam String


getFileUsed :: [Status] -> String
getFileUsed ls
 = case ls of
      (Address adr):_    -> takeName adr
      _:l                -> getFileUsed l
      []                 -> "Hets>"


takeName :: String -> String
takeName ls
  = case ls of
      '.':_ -> ['>']
      x :l  -> x:(takeName l)
      _     -> ['>']
	


shellUse :: File -> Sh [Status] ()
shellUse (File filename)
  = do
       val <- getShellSt >>= \state -> liftIO (cUse filename state)
       modifyShellSt (update val)


shellDgAutoAll ::  Sh [Status] ()
shellDgAutoAll 
  = do
      val <- getShellSt >>= \state -> liftIO(cDgAllAuto "" state)
      modifyShellSt (update val)

shellDgAuto :: String -> Sh [Status] ()
shellDgAuto input
  = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto input state)
     modifyShellSt (update val)

shellDgGlobSubsume :: String -> Sh [Status] ()
shellDgGlobSubsume input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgGlobSubsume input state)
     modifyShellSt (update val)

shellDgGlobDecomp :: String -> Sh [Status] ()
shellDgGlobDecomp input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgGlobDecomp input state)
     modifyShellSt (update val)


shellDgLocInfer :: String -> Sh [Status] ()
shellDgLocInfer input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgLocInfer input state)
     modifyShellSt (update val)


shellDgLocDecomp :: String -> Sh [Status] ()
shellDgLocDecomp input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgLocDecomp input state)
     modifyShellSt (update val)


shellDgComp :: String -> Sh [Status] ()
shellDgComp input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgComp input state)
     modifyShellSt (update val)

shellDgCompNew :: String -> Sh [Status] ()
shellDgCompNew input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgCompNew input state)
     modifyShellSt (update val)


shellDgHideThm :: String -> Sh [Status] ()
shellDgHideThm input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgHideThm input state)
     modifyShellSt (update val)


shellDgBasic :: String -> Sh [Status] ()
shellDgBasic input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgInferBasic input state)
     modifyShellSt (update val)

shellDgGlobSubsumeAll :: Sh [Status] ()
shellDgGlobSubsumeAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllGlobSubsume "" state)
     modifyShellSt (update val)


shellDgGlobDecompAll :: Sh [Status] ()
shellDgGlobDecompAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllGlobDecomp "" state)
     modifyShellSt (update val)


shellDgLocInferAll :: Sh [Status] ()
shellDgLocInferAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllLocInfer "" state)
     modifyShellSt (update val)


shellDgLocDecompAll :: Sh [Status] ()
shellDgLocDecompAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllLocDecomp "" state)
     modifyShellSt (update val)


shellDgCompAll :: Sh [Status] ()
shellDgCompAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllComp "" state)
     modifyShellSt (update val)


shellDgCompNewAll :: Sh [Status] ()
shellDgCompNewAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllCompNew "" state)
     modifyShellSt (update val)


shellDgHideThmAll :: Sh [Status] ()
shellDgHideThmAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllHideThm "" state)
     modifyShellSt (update val)


shellDgBasicAll :: Sh [Status] ()
shellDgBasicAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllInferBasic "" state)
     modifyShellSt (update val)

shellShowDgGoals :: Sh [Status] ()
shellShowDgGoals 
   = do
     val <- getShellSt >>= \state -> liftIO(cShowDgGoals "" state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cShowDgGoals ""].deleteExec)

shellShowTheoryGoals :: Sh [Status] ()
shellShowTheoryGoals
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto "" state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cShowTheory ""].deleteExec)

shellShowTheory :: Sh [Status] ()
shellShowTheory 
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto "" state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cShowNodeTheory ""].deleteExec)

shellNodeInfo :: Sh [Status] ()
shellNodeInfo
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto "" state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cShowNodeInfo ""].deleteExec)

shellShowTaxonomy :: Sh [Status] ()
shellShowTaxonomy
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto "" state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cShowNodeTaxonomy ""].deleteExec)

shellShowConcept :: Sh [Status] ()
shellShowConcept
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto "" state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cShowNodeConcept "" ].deleteExec)

shellTranslate :: String -> Sh [Status] ()
shellTranslate input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto input state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cTranslate input].deleteExec)

shellProver :: String -> Sh [Status] ()
shellProver input
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAuto input state)
     modifyShellSt (update val)

-- = modifyShellSt (update [Exec cProver input].deleteExec)

pgipEvalFunc :: String -> Sh [Status] ()
pgipEvalFunc str
  = case str of
     []   -> modifyShellSt deleteExec
     x    -> do 
              modifyShellSt deleteExec   
              (shellPutStr ("Unkown input :" ++ x ++ "\n"
                           ++ "Type \'help\' for more information\n"))

pgipShellCommands :: [ShellCommand [Status]]
pgipShellCommands 
                    = (exitCommand "exit")
                    : (helpCommand "help")
                    : (cmd "use" shellUse "open a file with HetCASL library")
                    : (cmd "dg auto" shellDgAuto 
                      "apply automatic tactic to a list of goals")
                    : (cmd "dg glob-subsume" shellDgGlobSubsume 
                      "apply global subsumption to a list of goals")
                    : (cmd "dg glob-decomp" shellDgGlobDecomp
                      "apply global decomposition to a list of goals")
                    : (cmd "dg loc-infer" shellDgLocInfer
                      "apply local inference to a list of goals")
                    : (cmd "dg loc-decomp" shellDgLocDecomp
                      "apply local decomposition to a list of goals")
                    : (cmd "dg comp" shellDgComp
                      "apply composition to a list of goals")
                    : (cmd "dg comp-new" shellDgCompNew
                       ("apply composition with speculation of new edges to"++
                      " a list of goals"))
                    : (cmd "dg hide-thm" shellDgHideThm
                      "apply hide theorem shift to a list of goals")
                    : (cmd "dg basic" shellDgBasic
                      "select a list of goals for proving")
                    : (cmd "dg-all auto" shellDgAutoAll 
                      "apply automatic tactic to all goals")
                    : (cmd "dg-all glob-subsume" shellDgGlobSubsumeAll 
                      "apply global subsumption to all goals")
                    : (cmd "dg-all glob-decomp" shellDgGlobDecompAll
                      "apply global decomposition to all goals")
                    : (cmd "dg-all loc-infer" shellDgLocInferAll
                      "apply local inference to all goals")
                    : (cmd "dg-all loc-decomp" shellDgLocDecompAll
                      "apply local decomposition to all goals")
                    : (cmd "dg-all comp" shellDgCompAll
                      "apply composition to all goals")
                    : (cmd "dg-all comp-new" shellDgCompNewAll
                       ("apply composition with speculation of new edges to"++
                      " all goals"))
                    : (cmd "dg-all hide-thm" shellDgHideThmAll
                      "apply hide theorem shift to all goals")
                    : (cmd "dg-all basic" shellDgBasicAll
                      "select all goals for proving")
                    : (cmd "show-dg-goals" shellShowDgGoals
                      "shows list of all open dg goals")
                    : (cmd "show-theory-goals" shellShowTheoryGoals
                      "shows list of theory goals")
                    : (cmd "show-theory" shellShowTheory
                      "shows current theory and proof goals")
                    : (cmd "node-info" shellNodeInfo
                      "shows info about current dg node")
                    : (cmd "show-taxonomy" shellShowTaxonomy
                      "shows taxonomy graph")
                    : (cmd "show-concept" shellShowConcept
                      "shows concept graph")
                    : (cmd "translate" shellTranslate
                      "translate theory goals along comorphism")
                    : (cmd "prover" shellProver
                      "selects a prover")
                    : [] 


deleteExec :: [Status] -> [Status]
deleteExec ls
   = case ls of 
        Exec _ _:l -> deleteExec l
        x:l      -> x:(deleteExec l)
        []       -> []

pgipExec :: [Status] -> [Status] -> IO [Status]
pgipExec ls status
  = case ls of 
      (Exec fn input):l  -> 
                  do 
                     val <-fn input status
                     let nwStatus = update val (deleteExec status)
                     pgipExec l nwStatus
                     pgipExec l nwStatus
      _:l                  -> pgipExec l status
      []                   -> return status

pgipProcessInput :: [Status] -> IO String
pgipProcessInput state
                     = do
                         val <- pgipExec state state
                         let _ =modifyShellSt (update val)
                         return (getFileUsed val) 

--pgipUpdateState :: [Status] -> [Status]
--pgipUpdateState state
--                    = let val = liftIO (pgipExec state state) 
--                      in  update val state

pgipShellDescription :: ShellDescription [Status]
pgipShellDescription =
 let wbc = "\t\n\r\v\\,;" in
      ShDesc
       { shellCommands      = pgipShellCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = pgipEvalFunc
       , wordBreakChars     = wbc
       , beforePrompt       = modifyShellSt (deleteExec) 
       , prompt             = pgipProcessInput 
       , exceptionHandler   = defaultExceptionHandler
       , defaultCompletions = Just (\_ _ -> return [])
       , historyFile        = Just ("consoleHistory.tmp")
       , maxHistoryEntries  = 100
       , historyEnabled     = True
       }


pgipRunShell :: IO [Status]
pgipRunShell = runShell pgipShellDescription 
                        readlineBackend 
                        []


{--
checkLetter :: Char -> String -> Bool
checkLetter x ls
    = case ls of 
            []   -> return False
            l:ll -> if (l == x) then True
                                else checkLetter x ll

scanAnyWord::String -> String -> [String]
scanAnyWord input tmp
     = case input  of 
         []  -> return tmp:[]
         x:l -> if (checkLetter x (caslLetters++['0'..'9']++['-','_']))
                                 then scanAnyWord l x:tmp
                                 else tmp:input:[]
                  
         
getKeyWord::String -> String -> [String ]
getKeyWord l1 l2 
  = case l1 of 
        []  -> l2:[]
        x:ll1 -> case l2 of
                  []    -> []
                  y:ll2 -> if (x == y) then getKeyWord ll1 ll2
                                       else []


getGoal::String -> [GOAL]
getGoal input       
  = let tmp1 = scanAnyWord input "" in
    case tmp1 of
     []         -> []
     v1:rest1:_ -> let tmp2 = getKeyWord "-" rest1 in
                   case tmp2 of 
                    []  -> (Node v1):getGoal rest1
                    x:_ -> let tmp2= getNumber rest1 in
                           case tmp2 of
                            []         -> []
                            v2:rest2:_ -> let tmp3=getKeyWord "->" rest2 in
                                          case tmp3 of
                                           []    ->                                         
                                      
          sw = getKeyWord "-"
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


 
scanPathFile::CharParser st String
scanPathFile 
     = many1 ( oneOf (caslLetters ++ ['0'..'9'] ++ ['-','_','.']))


scanAnyWord::CharParser st String
scanAnyWord
     = many1 (oneOf (caslLetters ++ ['0'..'9'] ++ ['_','\'','.','-']))

-- |the 'getPath' function read a path as a a list of words
getPath::AParser st String
getPath 
        = try ( do  
                    v<-sepBy1 scanPathFile (string "/")
                    let result = joinWith '/' v
                    return result
              )
      <|> 
          try ( do  skip
                    v<-sepBy1 scanPathFile (string "/")
                    let result = joinWith '/' v
                    return result
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
--                                 v<- getGoal
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
--}

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


--parsingCommand::Int->AParser st InterpreterCmd
--parsingCommand x
--   = case x of 
--       0 -> checkCommand commands
--       _ -> do 
--              checkCommand commands
--              skip
--              result<- parsingCommand (x-1)
--              return result
--
--parseScript :: Int -> String -> IO (Maybe [InterpreterCmd])
--parseScript nb str
--  = do 
--     let x=runParser (parsingCommand nb) (emptyAnnos()) "" str
--     case x of
--       Left _  -> do
--                   putStr "An error has occured \n"
--                   return Nothing
--       Right (CmdE _) -> 
--                  do
----                 putStr ("_"++smt++"_\n"++str ++ "\n\n"++(show nb)++ "\n\n")
--                   return (Nothing)
--       Right EndOfCommands -> return (Just [])
--       Right y -> do
--                   z<-parseScript (nb+1) str
--                   case z of
--                      Nothing -> return Nothing
--                      Just zz -> return (Just (y:zz))

{--
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
                         let newStatus= update val status 
--                       putStr ("Command parameters " ++ (show x) ++ "\n") 
                         runScriptCommands (ls,newStatus)
      (CmdPS fn x):ls-> do
                         let val = fn (x,status)
                         let newStatus= update val status
--                       putStr ("Command parameters " ++ (show x) ++ "\n")
                         runScriptCommands (ls,newStatus)
      (CmdS fn ):ls  -> do
                         let val= fn status
                         let newStatus= update val status 
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
                         let newStatus = update val status 
                         runScriptCommands (ls, newStatus)
      (CmdE _):_     -> return Nothing
      EndOfCommands:_-> runScriptCommands ([], status)

runScriptLine :: [InterpreterCmd]->[Status] -> IO (Maybe [Status])
runScriptLine arg status
  = case arg of
      [] -> return (Just status)
      (CmdP fn x):ls  -> do 
                          val<- fn x
                          let newStatus= update  val status 
--                        putStr ("Command parameters " ++ (show x) ++ "\n")
                          runScriptLine ls newStatus
      (CmdPS fn x):ls -> do
                          let val = fn (x,status)
                          let newStatus= update val status 
--                        putStr ("Command parameters " ++ (show x) ++ "\n")
                          runScriptLine ls newStatus 
      (CmdS fn ):ls   -> do
                          let val= fn status
                          let newStatus= update val status 
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
                          let newStatus = update val status
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

	
-- takeName :: String -> String
-- takeName ls
--   = case ls of
--      '.':_ -> ['>']
--      x :l  -> x:(takeName l)
--      _     -> ['>']
--					 					 


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
                putStr "\nError, couldn't parse input \n"
                putStr "Please type help for more information\n\n"
                runInteractive status

--}
