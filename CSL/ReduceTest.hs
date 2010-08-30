{-# LANGUAGE FlexibleContexts #-}
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

import CSL.MapleInterpreter

import CSL.ReduceInterpreter
import CSL.Reduce_Interface
import CSL.Interpreter
import CSL.Logic_CSL
import CSL.AS_BASIC_CSL
import CSL.Sign

import Common.Utils (getEnvDef)
import Common.IOS
import Common.Result (diags, printDiags, resultToMaybe)
import Common.ResultT

-- the process communication interface
import qualified Interfaces.Process as PC

-- README: in order to work correctly link the Test.hs in the Hets-Root Dir to Main.hs (ln -s Test.hs Main.hs)
import Main (getSigSens)

import Data.Maybe (fromJust)
import Data.Time.Clock
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

destructureAssignment :: CMD -> Maybe (String, EXPRESSION)
destructureAssignment (Cmd ":=" [Op n [] [] _, e]) = Just (n, e)
destructureAssignment _ = Nothing

destructureConstraint :: CMD -> Maybe EXPRESSION
destructureConstraint (Cmd "constraint" [e]) = Just e
destructureConstraint _ = Nothing


-- for testing Booleans or Assignments
boolAssignEval :: CalculationSystem m => CMD -> m (Either String Bool)
boolAssignEval cmd =
    case destructureConstraint cmd of
      Just be -> check be >>= return . Right
      _ -> case destructureAssignment cmd of
             Just (n, e) -> assign n e >> return (Left n)
             _ -> return $ Left ""



runTest :: ResultT (IOS b) a -> b -> IO a
runTest cmd r = fmap fromJust $ runTestM cmd r

runTestM :: ResultT (IOS b) a -> b -> IO (Maybe a)
runTestM cmd r = fmap (resultToMaybe . fst) $ runIOS r $ runResultT cmd

-- time measurement, pendant of the time shell command
time :: IO a -> IO a
time p = do
  t <- getCurrentTime
  res <- p
  t' <- getCurrentTime
  putStrLn $ show $ diffUTCTime t' t
  return res

evalL :: CalculationSystem (ResultT (IOS b)) => b
      -> Int -- ^ Test-spec
      -> IO b
evalL s i = do
  cl <- cmds i
  (_, s') <- runIOS s (runResultT $ evaluateList cl)
  return s'


-- ----------------------------------------------------------------------
-- * Maple interpreter
-- ----------------------------------------------------------------------













-- ----------------------------------------------------------------------
-- * First reduce interpreter
-- ----------------------------------------------------------------------


-- booleans and assignments are returned
redsBA :: Int -- ^ Test-spec
      -> IO ([Either String Bool], ReduceInterpreter)
redsBA i = do
  r <- redsInit
  cl <- cmds i
  (res, r') <- runIOS r (runResultT $ mapM boolAssignEval cl)
  return (fromJust $ resultToMaybe res, r')


-- first reduce interpreter
reds :: Int -- ^ Test-spec
    -> IO ReduceInterpreter
reds i = do
  r <- redsInit
  sendToReduce r "on rounded; precision 30;"
  evalL r i



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


-- ----------------------------------------------------------------------
-- * second reduce interpreter
-- ----------------------------------------------------------------------

-- run the assignments from the spec
redc :: Int -- ^ verbosity level
     -> Int -- ^ Test-spec
     -> IO RITrans
redc v i = do
  r <- redcInit v
  evalL r i

redcNames :: RITrans -> IO [String]
redcNames = runTest names

redcValues :: RITrans -> IO [(String, EXPRESSION)]
redcValues = runTest values

-- run the assignments from the spec
redcCont :: Int -- ^ Test-spec
         -> RITrans
         -> IO RITrans
redcCont i r = do
  cl <- cmds i
  (res, r') <- runIOS r (runResultT $ evaluateList cl)
  printDiags (PC.verbosity $ getRI r') (diags res)
  return r'


-- disconnect from reduce
redcX :: RITrans -> IO (Maybe ExitCode)
redcX = runTest redcExit


--- Testing with many instances
{-
-- c-variant
lc <- time $ mapM (const $ redc 1 1) [1..20]
mapM redcX lc

-- to communicate directly with reduce use:

let r = head lc   OR    r <- redc x y

let ri = getRI r

redcDirect ri "some command;"

-}
