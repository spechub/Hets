{- |
Module      :$Header$
Description : parser for Hets command line interface
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
import System.IO
import qualified Control.Exception as Ex

-- | Checks the status to see if any library was loaded and generates the
-- corresponding prompter
getFileUsed :: [Status] -> String
getFileUsed ls
 = case ls of
      (Address adr):_    -> takeName adr
      _:l                -> getFileUsed l
      []                 -> "Hets> "

-- | Removes any file extension from the name of the file
takeName :: String -> String
takeName ls
  = case ls of
      ".casl" -> "> "
      x :l    -> x:(takeName l)
      _       -> "> "


-- | implements the command use for shellac
shellUse :: File -> Sh [Status] ()
shellUse (File filename)
  = do
       let f_str=stripComments filename
       val <- getShellSt >>= \state -> liftIO (cUse f_str state)
       st <- getShellSt
       nwSt <- liftIO (update val st)
       putShellSt nwSt

-- | implements the command dg-all auto for shellac
shellDgAutoAll ::  Sh [Status] ()
shellDgAutoAll
  = do
      val <- getShellSt >>= \state -> liftIO(cDgAllAuto "" state)
      st <- getShellSt
      nwSt <- liftIO (update val st)
      putShellSt nwSt

shellDgAuto :: String -> Sh [Status] ()
shellDgAuto input
  = do
     let f_str= stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgAuto f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt

   

shellDgGlobSubsume :: String -> Sh [Status] ()
shellDgGlobSubsume input
   = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgGlobSubsume f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellDgGlobDecomp :: String -> Sh [Status] ()
shellDgGlobDecomp input
   = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgGlobDecomp f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgLocInfer :: String -> Sh [Status] ()
shellDgLocInfer input
   = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgLocInfer f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgLocDecomp :: String -> Sh [Status] ()
shellDgLocDecomp input
   = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgLocDecomp f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgComp :: String -> Sh [Status] ()
shellDgComp input
   = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgComp f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellDgCompNew :: String -> Sh [Status] ()
shellDgCompNew input
   = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgCompNew f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgHideThm :: String -> Sh [Status] ()
shellDgHideThm input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgHideThm f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgBasic :: String -> Sh [Status] ()
shellDgBasic input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cDgInferBasic f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellDgGlobSubsumeAll :: Sh [Status] ()
shellDgGlobSubsumeAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllGlobSubsume "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgGlobDecompAll :: Sh [Status] ()
shellDgGlobDecompAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllGlobDecomp "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgLocInferAll :: Sh [Status] ()
shellDgLocInferAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllLocInfer "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgLocDecompAll :: Sh [Status] ()
shellDgLocDecompAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllLocDecomp "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgCompAll :: Sh [Status] ()
shellDgCompAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllComp "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgCompNewAll :: Sh [Status] ()
shellDgCompNewAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllCompNew "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgHideThmAll :: Sh [Status] ()
shellDgHideThmAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllHideThm "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDgBasicAll :: Sh [Status] ()
shellDgBasicAll
   = do
     val <- getShellSt >>= \state -> liftIO(cDgAllInferBasic "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt

shellShowDgGoals :: Sh [Status] ()
shellShowDgGoals
   = do
     val <- getShellSt >>= \state -> liftIO(cShowDgGoals "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellShowTheoryGoals :: Sh [Status] ()
shellShowTheoryGoals
   = do
     val <- getShellSt >>= \state -> liftIO(cShowTheory "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellShowTheory :: Sh [Status] ()
shellShowTheory
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeTheory "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellInfo :: Sh [Status] ()
shellInfo
   = do
     val <- getShellSt >>= \state -> liftIO(cShowInfo "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellShowTaxonomy :: Sh [Status] ()
shellShowTaxonomy
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeTaxonomy "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt

shellShowConcept :: Sh [Status] ()
shellShowConcept
   = do
     val <- getShellSt >>= \state -> liftIO(cShowNodeConcept "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellTranslate :: String -> Sh [Status] ()
shellTranslate input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cTranslate f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellProver :: String -> Sh [Status] ()
shellProver input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cProver f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt

shellNodeNumber :: String -> Sh [Status] ()
shellNodeNumber input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cViewNodeNumber f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellShowTheoryP :: String -> Sh [Status] ()
shellShowTheoryP input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cShowNodeTheory f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt

shellInfoP :: String -> Sh [Status] ()
shellInfoP input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cShowInfo f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt

shellShowTaxonomyP ::String -> Sh [Status] ()
shellShowTaxonomyP input
   = do
     let f_str=stripComments input
     val <- getShellSt >>= \state -> liftIO(cShowNodeTaxonomy f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellShowConceptP :: String -> Sh [Status] ()
shellShowConceptP input
   = do
     let f_str= stripComments input
     val <- getShellSt >>= \state -> liftIO(cShowNodeConcept f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt

shellEdges :: Sh [Status] ()
shellEdges
  = do
    val <-getShellSt >>= \state -> liftIO(cEdges "" state)
    st <- getShellSt
    nwSt <- liftIO (update val st)
    putShellSt nwSt


shellNodes :: Sh [Status] ()
shellNodes
  = do
    val <-getShellSt >>= \state -> liftIO(cNodes "" state)
    st <- getShellSt
    nwSt <- liftIO (update val st)
    putShellSt nwSt


shellDetails :: Sh [Status] ()
shellDetails
    = shellPutStr printDetails

nothing :: [Status]->IO [Status]
nothing x
  = return x

shellComment :: String -> Sh [Status] ()
shellComment _
  =
   do
     val<- getShellSt >>= \state -> liftIO (nothing state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellProve :: Sh [Status] ()
shellProve
  = do
     val <-getShellSt >>= \state -> liftIO(cDummy "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellProveMix :: String -> Sh [Status] ()
shellProveMix input
  = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO (cDummy f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellProveAllMix :: String -> Sh [Status] ()
shellProveAllMix input
  = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO (cDummy f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellProveAll :: Sh [Status] ()
shellProveAll
  = do
     val <-getShellSt >>= \state -> liftIO(cDummy "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellSetAxioms :: String -> Sh [Status] ()
shellSetAxioms input
  = do
      let f_str = stripComments input
      val <-getShellSt >>= \state -> liftIO(cDummy f_str state)
      st <- getShellSt
      nwSt <- liftIO (update val st)
      putShellSt nwSt


shellSetIncludeTheoremsTrue :: Sh [Status] ()
shellSetIncludeTheoremsTrue
  = do
      val <- getShellSt >>= \state -> liftIO (cDummy "" state)
      st <- getShellSt
      nwSt <- liftIO (update val st)
      putShellSt nwSt


shellSetIncludeTheoremsFalse :: Sh [Status] ()
shellSetIncludeTheoremsFalse
  = do
     val <- getShellSt >>= \state-> liftIO (cDummy "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellSetTimeLimit :: String -> Sh [Status] ()
shellSetTimeLimit input
  = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO (cDummy f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellSetAxiomsAll ::Sh [Status] ()
shellSetAxiomsAll
  = do
     val <- getShellSt >>= \state -> liftIO (cDummy "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellAddAxioms :: String -> Sh [Status] ()
shellAddAxioms input
  = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO (cDummy f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellAddAxiomsAll :: Sh [Status] ()
shellAddAxiomsAll
  = do
     val <- getShellSt >>= \state -> liftIO (cDummy "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


shellDelAxioms :: String -> Sh [Status] ()
shellDelAxioms input
  = do
     let f_str = stripComments input
     val <- getShellSt >>= \state -> liftIO (cDummy f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt



shellDelAxiomsAll :: Sh [Status] ()
shellDelAxiomsAll
  = do
     val <- getShellSt >>= \state -> liftIO (cDummy "" state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt




shellDisplayGraph :: Sh [Status] ()
shellDisplayGraph
  = do
    val <-getShellSt >>= \state -> liftIO(cShowGraph "" state)
    st <- getShellSt
    nwSt <- liftIO (update val st)
    putShellSt nwSt


-- | the 'doEvaluation' function evaluates an input which is not a command
doEvaluation :: String -> [Status] -> IO [Status]
doEvaluation str state
  = case str of
     []     -> return []
     _      -> case state of
                 []  -> do putStr ("Unkown input :"++str++"\n"
                               ++ "Type \'help\' for more information\n")
                           return []
                 LoadScript:_-> return ([More str])
                 _:l  -> doEvaluation str l

-- | the 'doFileEval' function evaluates an input which is not a command
-- in the case the input is provided as a file
doFileEval :: String -> [Status] -> IO [Status]
doFileEval str state
  = case str of
      []        -> return []
      _         -> case state of
                     [] -> do
                            putStr ("\n Unkown input :" ++ str ++ "\n")
                            return []
                     LoadScript:_ -> return ([More str])
                     _:l   -> doFileEval str l

-- | The evaluation function is called when the input could not be parsed
-- as a command. If the input is an empty string do nothing, otherwise
-- print the error message
pgipEvalFunc :: String -> Sh [Status] ()
pgipEvalFunc str
    = do
       let f_str= stripComments str
       val <-getShellSt >>= \state -> liftIO(doEvaluation f_str state)
       st <- getShellSt
       nwSt <- liftIO (update val st)
       putShellSt nwSt


-- | The evaluation function in case shellac reads from a file.
pgipFileEvalFunc :: String -> Sh [Status] ()
pgipFileEvalFunc str
  = do
     let f_str= stripComments str
     val <- getShellSt >>= \state -> liftIO (doFileEval f_str state)
     st <- getShellSt
     nwSt <- liftIO (update val st)
     putShellSt nwSt


stripComments :: String -> String
stripComments input
    = case input of
           '#':_ -> []
           []    -> []
           l:ls  -> l:(stripComments ls)


-- | Generates the list of all the shell commands toghether with a small help
-- message
pgipShellCommands :: [ShellCommand [Status]]
pgipShellCommands
                    = (exitCommand "exit")
		    : (exitCommand "quit")
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
                    : (cmd "select" shellDgBasic
		      "select a list of goals for proving")
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
                    : (cmd "show-theory-current" shellShowTheory
                      "shows current theory and proof goals")
                    : (cmd "show-theory" shellShowTheoryP
                      "shows theory of the provided node")
                    : (cmd "info-current" shellInfo
                      "shows info about current dg node or edge")
                    : (cmd "info" shellInfoP
                      "shows info about the provided dg node")
                    : (cmd "show-taxonomy-current" shellShowTaxonomy
                      "shows taxonomy graph")
                    : (cmd "show-taxonomy" shellShowTaxonomyP
                      "shows taxonomy graph of the provided node")
                    : (cmd "show-concept-current" shellShowConcept
                      "shows concept graph")
                    : (cmd "show-concept" shellShowConceptP
                      "shows concept graph of the provided node")
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
                    : (cmd "show-graph" shellDisplayGraph
                     "displays the current dg graph")
                    : (cmd "#" shellComment
                     "comments")
                    : (cmd "prove" shellProve
                     "Applies a theorem prover")
                    : (cmd "prove-all" shellProveAll
                     "Applies a theorem prover to all theorems")
                    : (cmd "prove {" shellProveMix
                     "Applies a theorem prove with a block of rules")
                    : (cmd "prove-all {" shellProveAllMix
                     "Applies a theorem prover to all nodes")
                    : (cmd "set axioms" shellSetAxioms
                     " A set of axioms to be used")
                    : (cmd "set axioms-all" shellSetAxiomsAll
                     " All axioms should be used")
                    : (cmd "set include-theorems true"
                        shellSetIncludeTheoremsTrue
                     "Include previous proved theorems")
                    : (cmd "set include-theorems false"
                        shellSetIncludeTheoremsFalse
                     "Do not include previous proved theorems")
                    : (cmd "set time-limit" shellSetTimeLimit
                     "Time limit for the prover to run before abortion")
                    : (cmd "add axioms" shellAddAxioms
                     "Axioms to be considered by the prover")
                    : (cmd "add axioms-all" shellAddAxiomsAll
                     "Axioms to be considered by the prover")
                    : (cmd "del axioms" shellDelAxioms
                     "Axioms that will not be considered by the prover")
                    : (cmd "del axioms-all" shellDelAxiomsAll
                     "Axioms that will not be considered by the prover")
                    : []


-- | Creates the Backend for reading from files
fileBackend :: String -> ShellBackend Handle
fileBackend filename = ShBackend
  { initBackend                      = openFile filename ReadMode
  , shutdownBackend                  = hClose
  , outputString                     = \_ -> basicOutput
  , flushOutput                      = \_ -> hFlush stdout
  , getSingleChar                    = fileGetSingleChar
  , getInput                         = fileGetInput
  , addHistory                       = \_ _ -> return ()
  , setWordBreakChars                = \_ _ -> return ()
  , getWordBreakChars                = \_ -> return
    " \t\n\r\v`~!@#$%^&*()=[]{};\\\'\",<>"
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

-- | Used to get one char from a file open for reading
fileGetSingleChar :: Handle -> String -> IO (Maybe Char)
fileGetSingleChar file _ = do
   Ex.bracket (hGetBuffering file) (hSetBuffering file) $ \_ -> do
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


pgipInteractiveShellDescription :: ShellDescription [Status]
pgipInteractiveShellDescription =
 let wbc = "\n\r\v\\" in
      initialShellDescription
       { shellCommands      = pgipShellCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = pgipEvalFunc
       , wordBreakChars     = wbc
       , prompt             = \x -> return (getFileUsed x)
       , historyFile        = Just ("consoleHistory.tmp")
       }

pgipFileShellDescription :: ShellDescription [Status]
pgipFileShellDescription =
 let wbc = "\t\n\r\v\\" in
      initialShellDescription
       { shellCommands      = pgipShellCommands
       , commandStyle       = OnlyCommands
       , evaluateFunc       = pgipFileEvalFunc
       , wordBreakChars     = wbc
       , prompt             = \_ -> return ""
       , historyEnabled     = False
       }

-- | The function runs hets in a shell
pgipRunShell :: [String] ->IO [Status]
pgipRunShell files
   = do
      state <- getStatus files []
      runShell pgipInteractiveShellDescription
                   { defaultCompletions = Just pgipCompletionFn }
              readlineBackend
              state
-- | The function processes the file of instruction
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
