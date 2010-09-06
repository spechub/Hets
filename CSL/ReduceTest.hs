{-# LANGUAGE FlexibleContexts #-}
{- |
Module      :  $Header$
Description :  Test environment for the ReduceInterpreter
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

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
import CSL.Transformation
import CSL.Logic_CSL
import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic (parseResult)
import CSL.Sign

import Common.Utils (getEnvDef)
import Common.IOS
import Common.Result (diags, printDiags, resultToMaybe)
import Common.ResultT

-- the process communication interface
import qualified Interfaces.Process as PC

-- README: IN ORDER TO WORK CORRECTLY LINK THE Test.hs IN THE HETS-ROOT DIR TO Main.hs (ln -s Test.hs Main.hs)
import Main (getSigSens)

import Control.Monad.State (StateT(..))
import Control.Monad (liftM)
import Data.Maybe (fromJust)
import Data.Time.Clock


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

runTest_ :: ResultT (IOS b) a -> b -> IO (a, b)
runTest_ cmd r = do
  (res, r') <- runIOS r $ runResultT cmd
  return (fromJust $ resultToMaybe res, r')

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



toE :: String -> EXPRESSION
toE = fromJust . parseResult

-- ----------------------------------------------------------------------
-- * MAPLE INTERPRETER
-- ----------------------------------------------------------------------

-- just call the methods in MapleInterpreter: mapleInit, mapleExit, mapleDirect
-- , the CS-interface functions and evalL



-- ----------------------------------------------------------------------
-- * FIRST REDUCE INTERPRETER
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
-- * SECOND REDUCE INTERPRETER
-- ----------------------------------------------------------------------

-- run the assignments from the spec
redc :: Int -- ^ verbosity level
     -> Int -- ^ Test-spec
     -> IO RITrans
redc v i = do
  r <- redcInit v
  evalL r i

redcNames :: RITrans -> IO [String]
redcNames = runTest $ liftM toList names

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


--- Testing with many instances
{-
-- c-variant
lc <- time $ mapM (const $ redc 1 1) [1..20]
mapM redcExit lc

-- to communicate directly with reduce use:

let r = head lc   OR    r <- redc x y

let ri = getRI r

redcDirect ri "some command;"

-}




-- ----------------------------------------------------------------------
-- * TRANSFORMATION TESTS
-- ----------------------------------------------------------------------

data WithAB a b c = WithAB a b c

instance Show c => Show (WithAB a b c) where
    show (WithAB _ _ c) = show c

getA (WithAB a _ _) = a
getB (WithAB _ b _) = b
getC (WithAB _ _ c) = c

-- tt = transformation tests (normally Calculationsystem monad result)

-- tte = tt with evaluation (normally gets a cs-state and has IO-result)

runTT c s vcc = do
  (res, s') <- runIOS s $ runResultT $ runStateT c vcc
  let (r, vcc') = fromJust $ resultToMaybe res
  return $ WithAB vcc' s' r

runTTi c s = do
  (res, s') <- runIOS s (runResultT $ do vcc <- csVCCache
                                         runStateT c vcc)
  let (r, vcc') = fromJust $ resultToMaybe res
  return $ WithAB vcc' s' r

--s -> t -> t1 -> IO (Common.Result.Result a, s)
ttesd :: ( VarGen (ResultT (IOS s))
         , VariableContainer a VarRange
         , CalculationSystem (ResultT (IOS s))
         , Cache (ResultT (IOS s)) a String EXPRESSION) =>
        EXPRESSION -> s -> a -> IO (WithAB a s EXPRESSION)
ttesd e = runTT (substituteDefined e)

ttesdi e = runTTi (substituteDefined e)

-- -- substituteDefined with init
--ttesdi s e = ttesd s vc e


