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

import PGIP.Commands
import PGIP.Common
import Data.Maybe
import System.Console.Shell.Backend.Readline
import System.Console.Shell.ShellMonad
import System.Console.Shell
import System.Console.Shell.Backend
import Control.Monad.Trans
import IO
import qualified Control.Exception as Ex

-- Checks the status to see if any library was loaded and generates the
-- corresponding prompter
getFileUsed :: [Status] -> String
getFileUsed ls
 = case ls of
      (Address adr):_    -> takeName adr
      _:l                -> getFileUsed l
      []                 -> "Hets> "

-- Removes any file extension from the name of the file
takeName :: String -> String
takeName ls
  = case ls of
      ".casl" -> "> "
      x :l    -> x:(takeName l)
      _       -> "> "
	

-- implements the command use for shellac
shellUse :: File -> Sh [Status] ()
shellUse (File filename)
  = do
       val <- getShellSt >>= \state -> liftIO (cUse filename state)
       modifyShellSt (update val)

-- implements the command dg-all auto for shellac
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

shellShowTheoryGoals :: Sh [Status] ()
shellShowTheoryGoals
   = do
     val <- getShellSt >>= \state -> liftIO(cShowTheory "" state)
     modifyShellSt (update val)

shellShowTheory :: Sh [Status] ()
shellShowTheory 
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeTheory "" state)
     modifyShellSt (update val)

shellInfo :: Sh [Status] ()
shellInfo
   = do
     val <- getShellSt >>= \state -> liftIO(cShowInfo "" state)
     modifyShellSt (update val)

shellShowTaxonomy :: Sh [Status] ()
shellShowTaxonomy
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeTaxonomy "" state)
     modifyShellSt (update val)

shellShowConcept :: Sh [Status] ()
shellShowConcept
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeConcept "" state)
     modifyShellSt (update val)

shellTranslate :: String -> Sh [Status] ()
shellTranslate input
   = do
     val <- getShellSt >>= \state -> liftIO(cTranslate input state)
     modifyShellSt (update val)

shellProver :: String -> Sh [Status] ()
shellProver input
   = do
     val <- getShellSt >>= \state -> liftIO(cProver input state)
     modifyShellSt (update val)

shellNodeNumber :: String -> Sh [Status] ()
shellNodeNumber input
   = do
     val <- getShellSt >>= \state -> liftIO(cViewNodeNumber input state)
     modifyShellSt (update val)

shellShowTheoryP :: String -> Sh [Status] ()
shellShowTheoryP input
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeTheory input state)
     modifyShellSt (update val)

shellInfoP :: String -> Sh [Status] ()
shellInfoP input
   = do
     val <- getShellSt >>= \state -> liftIO(cShowInfo input state)
     modifyShellSt (update val)

shellShowTaxonomyP ::String -> Sh [Status] ()
shellShowTaxonomyP input
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeTaxonomy input state)
     modifyShellSt (update val)

shellShowConceptP :: String -> Sh [Status] ()
shellShowConceptP input
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeConcept input state)
     modifyShellSt (update val)

shellEdges :: Sh [Status] ()
shellEdges
  = do 
    val <-getShellSt >>= \state -> liftIO(cEdges "" state)
    modifyShellSt (update val)

shellNodes :: Sh [Status] ()
shellNodes
  = do
    val <-getShellSt >>= \state -> liftIO(cNodes "" state)
    modifyShellSt (update val)

shellDetails :: Sh [Status] ()
shellDetails 
    = shellPutStr printDetails

-- The evaluation function is called when the input could not be parsed
-- as a command. If the input is an empty string do nothing, otherwise 
-- print the error message
pgipEvalFunc :: String -> Sh [Status] ()
pgipEvalFunc str
  = case str of
     []   -> return () 
     x    ->  
              (shellPutStr ("Unkown input :" ++ x ++ "\n"
                           ++ "Type \'help\' for more information\n"))

-- The evaluation function in case shellac reads from a file.
pgipFileEvalFunc :: String -> Sh [Status] ()
pgipFileEvalFunc str
  = case str of
     []   -> return () 
     x    ->  
              (shellPutStr ("\n\nUnkown input :" ++ x ++ "\n\n"))
                           


-- Generates the list of all the shell commands toghether with a small help
-- message
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
--                    : (cmd "show-theory" shellShowTheoryP
--                      "shows theory of the provided node")
                    : (cmd "info" shellInfo
                      "shows info about current dg node or edge")
--                    : (cmd "info" shellInfoP
--                      "shows info about the provided dg node")
                    : (cmd "show-taxonomy" shellShowTaxonomy
                      "shows taxonomy graph")
--                    : (cmd "show-taxonomy" shellShowTaxonomyP
--                      "shows taxonomy graph of the provided node")
                    : (cmd "show-concept" shellShowConcept
                      "shows concept graph")
--                    : (cmd "show-concept" shellShowConceptP
--                      "shows concept graph of the provided node")
                    : (cmd "translate" shellTranslate
                      "translate theory goals along comorphism")
                    : (cmd "prover" shellProver
                      "selects a prover")
                    : (cmd "details" shellDetails
                     "view details about the gramma of this interactive mode")
                    : (cmd "node-number" shellNodeNumber
                      " view node number")
                    : (cmd "nodes" shellNodes
                     "show all nodes of the development graph")
                    : (cmd "edges" shellEdges
                     "show all edges of the development graph")
                    : [] 


-- Creates the Backend for reading from files
fileBackend :: String -> ShellBackend Handle
fileBackend filename = 
 let handle = openFile filename ReadMode in
 ShBackend
  { initBackend                      =  handle 
  , outputString                     = \_ -> basicOutput
  , flushOutput                      = \_ -> hFlush stdout
  , getSingleChar                    = \x -> fileGetSingleChar x
  , getInput                         = \x -> fileGetInput x
  , addHistory                       = \_ _ -> return ()
  , setWordBreakChars                = \_ _ -> return ()
  , getWordBreakChars                = \_ -> return " \t\n\r\v`~!@#$%^&*()=[]{};\\\'\",<>"
  , onCancel                         = \_ -> hPutStrLn stdout "canceled...\n"
  , setAttemptedCompletionFunction   = \_ _ -> return ()
  , setDefaultCompletionFunction     = \_ _ -> return ()
  , completeFilename                 = \_ _ -> return []
  , completeUsername                 = \_ _ -> return []
  , clearHistoryState                = \_ -> return ()
  , getMaxHistoryEntries             = \_ -> return 0
  , setMaxHistoryEntries             = \_ _ -> return ()
  , readHistory                      = \_ _ -> return ()
  , writeHistory                     = \_ _ -> return ()
  }

-- Used to get one char from a file open for reading
fileGetSingleChar :: Handle -> String -> IO (Maybe Char)
fileGetSingleChar file _ = do
   Ex.bracket (hGetBuffering file) (hSetBuffering file) $ \_ -> do
      hSetBuffering file NoBuffering
      c <- hGetChar file
      hPutStrLn stdout ""
      return (Just c)

-- Used to get a line from a file open for reading
fileGetInput :: Handle -> String -> IO (Maybe String)
fileGetInput file _ = do
   x <- hGetLine file
   return (Just x)

basicOutput :: BackendOutput -> IO ()
basicOutput (RegularOutput out) = hPutStr stdout out
basicOutput (InfoOutput out)    = hPutStr stdout out
basicOutput (ErrorOutput out)   = hPutStr stderr out
                                                                 



pgipInteractiveShellDescription :: ShellDescription [Status]
pgipInteractiveShellDescription =
 let wbc = "\t\n\r\v\\,;" in
      ShDesc
       { shellCommands      = pgipShellCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = pgipEvalFunc
       , wordBreakChars     = wbc
       , beforePrompt       = return () 
       , prompt             = \x -> return (getFileUsed x)
       , exceptionHandler   = defaultExceptionHandler
       , defaultCompletions = Just (\_ _ -> return [])
       , historyFile        = Just ("consoleHistory.tmp")
       , maxHistoryEntries  = 100
       , historyEnabled     = True
       }


pgipFileShellDescription :: ShellDescription [Status]
pgipFileShellDescription =
 let wbc = "\t\n\r\v\\,;" in
      ShDesc
       { shellCommands      = pgipShellCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = pgipFileEvalFunc
       , wordBreakChars     = wbc
       , beforePrompt       = return () 
       , prompt             = \_ -> return ""
       , exceptionHandler   = defaultExceptionHandler
       , defaultCompletions = Just (\_ _ -> return [])
       , historyFile        = Nothing
       , maxHistoryEntries  = 100
       , historyEnabled     = False
       }



pgipRunShell :: [String] ->IO [Status]
pgipRunShell files 
   = do
      state <- getStatus files []
      runShell pgipInteractiveShellDescription {defaultCompletions = Just pgipCompletionFn}
              readlineBackend  
              state

pgipProcessFile :: String -> IO [Status]
pgipProcessFile filename = 
        (runShell pgipFileShellDescription
                 (fileBackend filename)
                 []) `catch` (\_ -> return [])

         

printDetails :: String 
printDetails =
   "\n\n Hets Interactive mode.The available grammar is\n\n" ++
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

	
