module System.Console.Shell.RunShell (
  runShell
, defaultExceptionHandler
, simpleSubshell
) where

import Maybe                       ( isJust )
import Data.Char                   ( isSpace )
import Data.List                   ( isPrefixOf, find )
import Data.IORef                  ( IORef, newIORef, readIORef, writeIORef )
import Control.Monad               ( when, MonadPlus(..) )
import Control.Monad.Error         ()
import Control.Concurrent          ( ThreadId, threadDelay, killThread, forkIO )
import Control.Concurrent.STM      ( atomically, retry )
import Control.Concurrent.STM.TVar ( newTVar, readTVar, writeTVar, TVar )
import System.Directory            ( doesFileExist )
import qualified Control.Exception as Ex

import System.Console.Shell.Backend
import System.Console.Shell.ShellMonad
import System.Console.Shell.Types
import System.Console.Shell.Commands
import System.Console.Shell.PPrint
import System.Console.Shell.Regex (runRegex)
import System.Console.Shell.ConsoleHandler

-------------------------------------------------------------------
-- A record to hold some of the internal muckety-muck needed
-- to make the shell go.  This is mostly concurrency variables
-- needed to handle keyboard interrupts.

data InternalShellState st bst
   = InternalShellState
     { evalTVar         :: TVar (Maybe (st,Maybe (ShellSpecial st)))
     , evalThreadTVar   :: TVar (Maybe ThreadId)
     , evalCancelTVar   :: TVar Bool
     , cancelHandler    :: IO ()
     , backendState     :: bst
     }


-------------------------------------------------------------------
-- Main entry point for the shell.  Sets up all the internal state
-- needed to run shell commands and evaluation in a separate thread and 
-- initializes the backend.


-- | Run a shell.  Given a shell description, a shell backend to use
--   and an initial state this function runs the shell until it exits,
--   and then returns the final state.

runShell :: ShellDescription st
         -> ShellBackend bst
         -> st
         -> IO st

runShell desc backend init = Ex.bracket setupShell exitShell (\iss -> shellLoop desc backend iss init)

  where setupShell = do
            evalVar   <- atomically (newTVar Nothing)
            thVar     <- atomically (newTVar Nothing)
            cancelVar <- atomically (newTVar False)
            bst       <- initBackend backend

            when (historyEnabled desc) (do
   	       setMaxHistoryEntries backend bst (maxHistoryEntries desc)
               loadHistory desc backend bst)

            return InternalShellState
                   { evalTVar       = evalVar
                   , evalThreadTVar = thVar
                   , evalCancelTVar = cancelVar
                   , cancelHandler  = handleINT evalVar cancelVar thVar
                   , backendState = bst
                   }

        exitShell iss = do
            when (historyEnabled desc) (do
               saveHistory desc backend (backendState iss)
	       clearHistoryState backend (backendState iss))
	    flushOutput backend (backendState iss)

        handleINT evalVar cancelVar thVar = do
            maybeTid <- atomically (do
 	    	         result <- readTVar evalVar
	                 if isJust result
                            then return Nothing
                            else do writeTVar cancelVar True
                                    writeTVar evalVar Nothing
                                    tid <- readTVar thVar
	                            case tid of
                                       Nothing  -> retry
                                       Just tid -> return (Just tid))


            case maybeTid of
               Nothing  -> return ()
               Just tid -> killThread tid


-------------------------------------------------------------------------
-- This function is installed as the attempted completion function.
-- It attempts to match the prefix of the input buffer against a
-- command.  If it matches, it supplies the completions appropriate
-- for that point in the command.  Otherwise it returns Nothing; in
-- that case, the backend will fall back on the default completion function
-- set in the shell description.

completionFunction :: ShellDescription st
                   -> ShellBackend bst
                   -> bst
                   -> st
                   -> (String,String,String)
                   -> IO (Maybe (String,[String]))

completionFunction desc backend bst st line@(before,word,after) = do
   if all isSpace before
     then completeCommands desc line
     else case runRegex (commandsRegex desc) before of
         [((_,cmdParser,_,_),before')] -> do
                let completers  = [ z | IncompleteParse (Just z) <- cmdParser before' ]
                strings <- case completers of
                              FilenameCompleter:_  -> completeFilename backend bst word >>= return . Just
                              UsernameCompleter:_  -> completeUsername backend bst word >>= return . Just
                              (OtherCompleter f):_ -> f st word >>= return . Just
                              _ -> return Nothing
                case strings of
                   Nothing -> return Nothing
                   Just [] -> return Nothing
                   Just xs -> return (Just (maximalPrefix xs,xs))

         _ -> return Nothing



completeCommands :: ShellDescription st
                 -> (String,String,String)
                 -> IO (Maybe (String,[String]))

completeCommands desc (before,word,after) =
    case matchingNames of
       [] -> return $ Nothing
       xs -> return $ Just (maximalPrefix xs,xs)

  where matchingNames = filter (word `isPrefixOf`) cmdNames
        cmdNames      = map (\ (n,_,_,_) -> (maybePrefix desc)++n) (getShellCommands desc)

maximalPrefix :: [String] -> String
maximalPrefix [] = []
maximalPrefix (x:xs) = f x xs
  where f p [] = p
        f p (x:xs) = f (fst $ unzip $ takeWhile (\x -> fst x == snd x) $ zip p x) xs



-----------------------------------------------------------
-- Deal with reading and writing history files.

loadHistory :: ShellDescription st
            -> ShellBackend bst
            -> bst
            -> IO ()

loadHistory desc backend bst =
  case historyFile desc of
     Nothing   -> return ()
     Just path -> do
        fexists <- doesFileExist path
        when fexists $
           Ex.handle
             (\ex -> (outputString backend bst) (ErrorOutput $
                 concat ["could not read history file '",path,"'\n   ",show ex]))
             (readHistory backend bst path)

saveHistory :: ShellDescription st
            -> ShellBackend bst
            -> bst
            -> IO ()

saveHistory desc backend bst =
  case historyFile desc of
    Nothing   -> return ()
    Just path ->
       Ex.handle 
          (\ex -> (outputString backend bst) (ErrorOutput $
                 concat ["could not write history file '",path,"'\n    ",show ex]))
          (writeHistory backend bst path)


-----------------------------------------------------------
-- The real meat.  We setup backend stuff, call the backend
-- to get the input string, and then handle the input.


shellLoop :: forall st bst
           . ShellDescription st
          -> ShellBackend bst
          -> InternalShellState st bst
          -> st
          -> IO st

shellLoop desc backend iss init = loop init
 where
   bst = backendState iss

   loop :: st -> IO st

   loop st =
     do flushOutput backend bst
        runSh st (outputString backend bst) (beforePrompt desc)
        setAttemptedCompletionFunction backend bst
	      (completionFunction desc backend bst st)

        case defaultCompletions desc of
           Nothing -> setDefaultCompletionFunction backend bst $ Nothing
           Just f  -> setDefaultCompletionFunction backend bst $ Just (f st)

        setWordBreakChars backend bst (wordBreakChars desc)

        pr  <- prompt desc st

        inp <- case commandStyle desc of

                 SingleCharCommands -> do
                      c <- getSingleChar backend bst pr
                      return (fmap (:[]) c)

                 _ -> getInput backend bst pr


        case inp of
           Nothing   -> return st
           Just inp' -> handleInput inp' st


   handleInput :: String -> st -> IO st
   handleInput inp st = do
     when (historyEnabled desc && (isJust (find (not . isSpace) inp)))
          (addHistory backend bst inp)

     let inp' = inp++" " -- hack, makes commands unambiguous

     case runRegex (commandsRegex desc) inp' of
       (x,inp''):_ -> executeCommand x inp'' st
       []          -> evaluateInput inp st


   executeCommand :: (String,CommandParser st,Doc,Doc) -> String -> st -> IO st
   executeCommand (cmdName,cmdParser,_,_) inp st =
      let parses  = cmdParser inp
          parses' = concatMap (\x -> case x of CompleteParse z -> [z]; _ -> []) parses
      in case parses' of
          f:_ -> do
              r <- handleExceptions desc (\x -> runSh x (outputString backend bst) f) st
              case r of
                  (st',Just spec) -> handleSpecial st' spec
                  (st',Nothing)   -> loop st'

          _   -> (outputString backend bst) (InfoOutput $ showCmdHelp desc cmdName) >> loop st

   handleSpecial :: st -> ShellSpecial st -> IO st
   handleSpecial st ShellExit               = return st
   handleSpecial st ShellNothing            = loop st
   handleSpecial st (ShellHelp Nothing)     = (outputString backend bst) (InfoOutput $ showShellHelp desc)   >> loop st
   handleSpecial st (ShellHelp (Just cmd))  = (outputString backend bst) (InfoOutput $ showCmdHelp desc cmd) >> loop st
   handleSpecial st (ExecSubshell subshell) = runSubshell desc subshell backend bst st >>= loop

   handleExceptions :: ShellDescription st 
                    -> (st -> IO (st,Maybe (ShellSpecial st))) 
                    -> st 
                    -> IO (st,Maybe (ShellSpecial st))
   handleExceptions desc f st = Ex.catch (f st) $ \ex ->
      runSh st (outputString backend bst) (exceptionHandler desc ex)

   runThread :: (String -> Sh st ())
             -> String
             -> InternalShellState st bst 
             -> st 
             -> IO ()

   runThread eval inp iss st = do
      val <- handleExceptions desc (\x -> runSh x (outputString backend bst) (eval inp)) st
      atomically (do
         cancled <- readTVar (evalCancelTVar iss)
	 if cancled then return () else do
           writeTVar (evalTVar iss) (Just val))

   evaluateInput :: String
                 -> st
                 -> IO st

   evaluateInput inp st =
     let eVar = evalTVar iss
         cVar = evalCancelTVar iss
         tVar = evalThreadTVar iss
     in do atomically (writeTVar cVar False >> writeTVar eVar Nothing >> writeTVar tVar Nothing)
           tid <- forkIO (runThread (evaluateFunc desc) inp iss st)
	   atomically (writeTVar tVar (Just tid))
           result <- withControlCHandler (cancelHandler iss) $ atomically (do
                       canceled <- readTVar cVar
                       if canceled then return Nothing else do
                         result <- readTVar eVar
                         case result of
                            Nothing -> retry
                            Just r  -> return (Just r))

           case result of
             Nothing              -> onCancel backend bst >> loop st
             Just (st',Just spec) -> handleSpecial st' spec
             Just (st',Nothing)   -> loop st'

-------------------------------------------------------------------------
-- | The default shell exception handler.  It simply prints the exception
--   and returns the shell state unchanged.  (However, it specificaly
--   ignores the thread killed exception, because that is used to
--   implement execution canceling)

defaultExceptionHandler :: Ex.Exception -> Sh st ()

defaultExceptionHandler (Ex.AsyncException Ex.ThreadKilled) = return ()
defaultExceptionHandler ex = do
  shellPutErrLn $ concat ["The following exception occurred:\n   ",show ex]

----------------------------------------------------------------------------
-- | Creates a simple subshell from a state mapping function
--   and a shell description.
simpleSubshell :: (st -> IO st')       -- ^ A function to generate the initial subshell
                                       --   state from the outer shell state
               -> ShellDescription st' -- ^ A shell description for the subshell
               -> IO (Subshell st st')

simpleSubshell toSubSt desc = do
  ref <- newIORef undefined
  let toSubSt' st     = writeIORef ref st >> toSubSt st
  let fromSubSt subSt = readIORef ref
  let mkDesc _        = return desc
  return (toSubSt',fromSubSt,mkDesc)


----------------------------------------------------------------------------
-- | Execute a subshell, suspending the outer shell until the subshell exits.
runSubshell :: ShellDescription desc -- ^ the description of the outer shell
            -> Subshell st st'       -- ^ the subshell to execute
            -> ShellBackend bst      -- ^ the shell backend to use
            -> bst                   -- ^ the backendstate
            -> st                    -- ^ the current state
            -> IO st                 -- ^ the modified state


runSubshell desc (toSubSt, fromSubSt, mkSubDesc) backend bst st = do
  subSt   <- toSubSt st
  subDesc <- mkSubDesc subSt
  subSt'  <- runShell subDesc backend subSt
  st'     <- fromSubSt subSt'
  return st'
