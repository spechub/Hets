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

shellNodeInfo :: Sh [Status] ()
shellNodeInfo
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeInfo "" state)
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

pgipEvalFunc :: String -> Sh [Status] ()
pgipEvalFunc str
  = case str of
     []   -> return () 
     x    ->  
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



pgipProcessInput :: [Status] -> IO String
pgipProcessInput state
                     = 
                         return (getFileUsed state) 


pgipShellDescription :: ShellDescription [Status]
pgipShellDescription =
 let wbc = "\t\n\r\v\\,;" in
      ShDesc
       { shellCommands      = pgipShellCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = pgipEvalFunc
       , wordBreakChars     = wbc
       , beforePrompt       = return () 
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

	
