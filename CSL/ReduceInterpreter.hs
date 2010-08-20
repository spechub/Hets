{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Reduce instance for the CalculationSystem class
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

Reduce as CalculationSystem
-}

module CSL.ReduceInterpreter where

import Common.ProverTools (missingExecutableInPath)
import Common.Utils (getEnvDef)
import Common.IOS

import CSL.Reduce_Interface ( evalString, exportExp, connectCAS, disconnectCAS
                            , redOutputToExpression, lookupRedShellCmd, Session (..))
import CSL.AS_BASIC_CSL (mkOp, EXPRESSION (..))
import CSL.Interpreter

-- the process communication interface
import qualified Interfaces.Process as PC

import Control.Monad (forM_)
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (MonadState (..))

import Data.Maybe
import System.IO (Handle)
import System.Process (ProcessHandle)
import System.Exit (ExitCode)


-- ----------------------------------------------------------------------
-- * Reduce Calculator Instances
-- ----------------------------------------------------------------------

data ReduceInterpreter = ReduceInterpreter { inh :: Handle
                                           , outh ::Handle
                                           , ph :: ProcessHandle }

-- Types for two alternative reduce interpreter
type RedIO = IOS ReduceInterpreter

-- also a synonym for PC.Command !
type RedcIO = IOS PC.CommandState

instance CalculationSystem RedIO where
    assign  = redAssign
    clookup = redClookup
    eval = redEval
    check = redCheck
    names = error "ReduceInterpreter as CS: names are unsupported"

instance CalculationSystem RedcIO where
    assign  = redcAssign
    clookup = redcClookup
    eval = redcEval
    names = error "ReduceInterpreter as CS: names are unsupported"

-- ----------------------------------------------------------------------
-- * Reduce syntax functions
-- ----------------------------------------------------------------------

printAssignment :: String -> EXPRESSION -> String
printAssignment n e = concat [n, ":=", exportExp e, ";"]

printEvaluation :: EXPRESSION -> String
printEvaluation e = exportExp e ++ ";"

printLookup :: String -> String
printLookup n = n ++ ";"

-- As reduce does not support boolean expressions as first class citizens
-- we encode them in an if-stmt and transform the numeric response back.
printBooleanExpr :: EXPRESSION -> String
printBooleanExpr e = concat ["if ", exportExp e, " then 1 else 0;"]

getBooleanFromExpr :: EXPRESSION -> Bool
getBooleanFromExpr (Int 1 _) = True
getBooleanFromExpr (Int 0 _) = False
getBooleanFromExpr e =
    error $ "getBooleanFromExpr: can't translate expression to boolean: "
              ++ show e

-- ----------------------------------------------------------------------
-- * The Standard Communication Interface
-- ----------------------------------------------------------------------

instance Session ReduceInterpreter where
    inp = inh
    outp = outh
    proch = Just . ph

redInit :: IO ReduceInterpreter
redInit = do
  putStr "Connecting CAS.."
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  -- check that prog exists
  noProg <- missingExecutableInPath reducecmd
  if noProg
   then error $ "Could not find reduce under " ++ reducecmd
   else do
     (inpt, out, _, pid) <- connectCAS reducecmd
     return $ ReduceInterpreter { inh = inpt, outh = out, ph = pid }

redExit :: ReduceInterpreter -> IO ()
redExit = disconnectCAS

redAssign :: String -> EXPRESSION -> RedIO ()
redAssign n e = do
  r <- get
  liftIO $ evalString r $ printAssignment n e
  return ()

redClookup :: String -> RedIO (Maybe EXPRESSION)
redClookup n = do
  r <- get
  [e] <- liftIO $ evalString r $ printLookup n
  if e == mkOp n [] then return Nothing else return $ Just e

redEval :: EXPRESSION -> RedIO EXPRESSION
redEval e = do
  r <- get
  el <- liftIO $ evalString r $ printEvaluation e
  if null el
   then error $ "redEval: expression " ++ show e ++ " couldn't be evaluated"
   else return $ head el

redCheck :: EXPRESSION -> RedIO Bool
redCheck e = do
  r <- get
  el <- liftIO $ evalString r $ printBooleanExpr e
  if null el
   then error $ "redEval: expression " ++ show e ++ " couldn't be evaluated"
   else return $ getBooleanFromExpr $ head el

-- ----------------------------------------------------------------------
-- * An alternative Communication Interface
-- ----------------------------------------------------------------------

-- | A direct way to communicate with Reduce
redcDirect :: PC.CommandState -> String -> IO String
redcDirect cs s = do
  (res, _) <- runIOS cs (PC.call 0.1 s)
  return res

evalRedcString :: String -> RedcIO [EXPRESSION]
evalRedcString s = do
  PC.call 0.1 s >>= return . maybeToList . redOutputToExpression


redcAssign :: String -> EXPRESSION -> RedcIO ()
redcAssign n e = do
  evalRedcString $ printAssignment n e
  return ()

redcClookup :: String -> RedcIO (Maybe EXPRESSION)
redcClookup n = do
  [e] <- evalRedcString $ printLookup n
  if e == mkOp n [] then return Nothing else return $ Just e

redcEval :: EXPRESSION -> RedcIO EXPRESSION
redcEval e = do
  el <- evalRedcString $ printEvaluation e
  if null el
   then error $ "redEval: expression " ++ show e ++ " couldn't be evaluated"
   else return $ head el

-- | init the reduce communication
redcInit :: Int -- ^ Verbosity level
         -> IO PC.CommandState
redcInit v = do
  rc <- lookupRedShellCmd
  case rc of
    Left redcmd ->
        PC.runProgInit redcmd v
              $ forM_ [ "off nat;", "load redlog;", "rlset reals;" ] PC.send
    _ -> error "Could not find reduce shell command!"

redcExit :: RedcIO (Maybe ExitCode)
redcExit = PC.close $ Just "quit;"

