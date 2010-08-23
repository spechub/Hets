{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Test environment for the ReduceInterpreter
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  portable

This file is for experimenting with the ReduceInterpreters
-}

module CSL.ReduceTest where

import CSL.ReduceInterpreter
import CSL.Reduce_Interface
import CSL.Interpreter
import CSL.Logic_CSL
import CSL.AS_BASIC_CSL
import CSL.Sign

import Common.Utils (getEnvDef)
import Common.IOS
import Common.Result (diags, printDiags)
import Common.ResultT (runResultT)

-- the process communication interface
import qualified Interfaces.Process as PC

-- README: in order to work correctly link the Test.hs in the Hets-Root Dir to Main.hs (ln -s Test.hs Main.hs)
import Main (getSigSens)

import System.Exit (ExitCode)


l1 :: Int -> IO (Sign, [(String, CMD)])
l1 i = do
  hlib <- getEnvDef "HETS_LIB" $ error "Missing HETS_LIB environment variable"
  getSigSens CSL (hlib ++ "/CSL/Tests.het") $ "Test" ++ show i

sig :: Int -> IO Sign
sig = fmap fst . l1

-- Check if the order is broken or not!
sens :: Int -> IO [(String, CMD)]
sens = fmap snd . l1

cmds :: Int -> IO [CMD]
cmds = fmap (map snd) . sens



-- for testing Booleans or Assignments
boolAssignEval :: CalculationSystem m => CMD -> m (Either String Bool)
boolAssignEval cmd =
    case destructureConstraint cmd of
      Just be -> check be >>= return . Right
      _ -> case destructureAssignment cmd of
             Just (n, e) -> assign n e >> return (Left n)
             _ -> return $ Left ""

{-
-- booleans and assignments are returned
redsBA :: Int -- ^ Test-spec
      -> IO ([Either String Bool], ReduceInterpreter)
redsBA i = do
  r <- redsInit
  cl <- cmds i
  runIOS r (mapM boolAssignEval cl)


-- first reduce interpreter
reds :: Int -- ^ Test-spec
    -> IO ReduceInterpreter
reds i = do
  r <- redsInit
  sendToReduce r "on rounded; precision 30;"
  cl <- cmds i
  runIOS r (evaluateList cl)
  return r

-}


-- use "redsExit r" to disconnect where "r <- red"

{- 
-- many instances (connection/disconnection tests)

l <- mapM (const reds 1) [1..20]
mapM redsExit l


-- BA-test:
(l, r) <- redsBA 2

'l' is a list of response values for each sentence in spec Test2
'r' is the reduce connection
-}



-- * second reduce interpreter

-- run the assignments from the spec
redc :: Int -- ^ verbosity level
     -> Int -- ^ Test-spec
     -> IO PC.CommandState
redc v i = do
  r <- redcInit v
  cl <- cmds i
  res <- PC.runProg r (runResultT $ evaluateList cl)
  printDiags v (diags res)
  return r


-- disconnect from reduce
-- redcX :: PC.CommandState -> IO (Maybe ExitCode)
-- redcX r = do
--   PC.runProg r redcExit


--- Testing with many instances
{-
-- c-variant
lc <- mapM (const $ redc 1 1) [1..20]
mapM redcX lc

-}
