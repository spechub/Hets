{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Reduce instance for the CalculationSystem class
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
                            , redOutputToExpression, lookupRedShellCmd)
import CSL.AS_BASIC_CSL (mkOp, EXPRESSION)
import CSL.Interpreter

-- the process communication interface
import qualified Interfaces.Process as PC

import Control.Monad (forM_)
import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (MonadState (..))

import Data.Maybe
import System.IO (Handle)
import System.Exit (ExitCode)


-- * Reduce Calculator Instances

data ReduceInterpreter = ReduceInterpreter { inh :: Handle
                                           , outh ::Handle }

-- Types for two alternative reduce interpreter
type RedIO = IOS ReduceInterpreter
type RedcIO = PC.Command

instance CalculationSystem RedIO where
    assign  = redAssign
    clookup = redClookup
    eval = redEval
    names = error "ReduceInterpreter as CS: names are unsupported"

instance CalculationSystem RedcIO where
    assign  = redcAssign
    clookup = redcClookup
    eval = redcEval
    names = error "ReduceInterpreter as CS: names are unsupported"

-- * The Standard Communication Interface

initReduce :: IO ReduceInterpreter
initReduce = do
  putStr "Connecting CAS.."
  reducecmd <- getEnvDef "HETS_REDUCE" "redcsl"
  -- check that prog exists
  noProg <- missingExecutableInPath reducecmd
  if noProg
   then error $ "Could not find reduce under " ++ reducecmd
   else do
     (inp, out, _, _) <- connectCAS reducecmd
     return $ ReduceInterpreter { inh = inp, outh = out }

exitReduce :: ReduceInterpreter -> IO ()
exitReduce r = disconnectCAS (inh r, outh r)

evalRedString :: ReduceInterpreter -> String -> IO [EXPRESSION]
evalRedString r = evalString (inh r, outh r)

redAssign :: String -> EXPRESSION -> RedIO ()
redAssign n e = do
  r <- get
  liftIO $ evalRedString r $ concat [n, ":=", exportExp e, ";"]
  return ()

redClookup :: String -> RedIO (Maybe EXPRESSION)
redClookup n = do
  r <- get
  [e] <- liftIO $ evalRedString r $ n ++ ";"
  if e == mkOp n [] then return Nothing else return $ Just e

redEval :: EXPRESSION -> RedIO EXPRESSION
redEval e = do
  r <- get
  el <- liftIO $ evalRedString r $ exportExp e ++ ";"
  if null el
   then error $ "redEval: expression " ++ show e ++ " couldn't be evaluated"
   else return $ head el


-- * An alternative Communication Interface


evalRedcString :: String -> RedcIO [EXPRESSION]
evalRedcString s = do
  PC.call 0.1 s >>= return . maybeToList . redOutputToExpression


redcAssign :: String -> EXPRESSION -> RedcIO ()
redcAssign n e = do
  evalRedcString $ concat [n, ":=", exportExp e, ";"]
  return ()

redcClookup :: String -> RedcIO (Maybe EXPRESSION)
redcClookup n = do
  [e] <- evalRedcString $ n ++ ";"
  if e == mkOp n [] then return Nothing else return $ Just e

redcEval :: EXPRESSION -> RedcIO EXPRESSION
redcEval e = do
  el <- evalRedcString $ exportExp e ++ ";"
  if null el
   then error $ "redEval: expression " ++ show e ++ " couldn't be evaluated"
   else return $ head el


start :: IO PC.CommandState
start = do
  rc <- lookupRedShellCmd
  case rc of
    Left redcmd ->
          do
            cs <- PC.start redcmd
            PC.runProg cs
                  $ forM_ [ "off nat;", "load redlog;", "rlset reals;" ] PC.send
    _ -> error "Could not find reduce shell command!"

close :: RedcIO ExitCode
close = PC.close $ Just "quit;"



