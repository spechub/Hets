{-# LANGUAGE FlexibleContexts #-}
{- |
Module      :  $Header$
Description :  Test environment for CSL
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (uses type-expression in type contexts)

This file is for experimenting with the Interpreter instances
and general static analysis tools
-}

module CSL.InteractiveTests where

import CSL.MapleInterpreter 

import CSL.ReduceInterpreter
import CSL.Reduce_Interface
import CSL.Interpreter
import CSL.Transformation
import CSL.ExtendedParameter
import CSL.Logic_CSL
import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic (parseResult, extparam, pComma, pSemi)
import CSL.Sign

import Common.Utils (getEnvDef)
import Common.IOS
import Common.Result (diags, printDiags, resultToMaybe)
import Common.ResultT
import Common.Lexer as Lexer
import Common.Parsec
import Text.ParserCombinators.Parsec

-- the process communication interface
import qualified Interfaces.Process as PC

-- README: In order to work correctly link the Test.hs in the Hets-root dir to Main.hs (ln -s Test.hs Main.hs)
import Main (getSigSens)

import Control.Monad.State (StateT(..))
import Control.Monad (liftM)
import Data.Maybe (fromJust, fromMaybe)
import Data.Time.Clock


-- ----------------------------------------------------------------------
-- * general test functions
-- ----------------------------------------------------------------------

testspecs =
    [ (44, ("/CSL/EN1591.het", "EN1591"))
    ]

l1 :: Int -> IO (Sign, [(String, CMD)])
l1 i = do
  let (lb, sp) = fromMaybe ("/CSL/Tests.het", "Test" ++ show i)
                 $ Prelude.lookup i testspecs
  hlib <- getEnvDef "HETS_LIB" $ error "Missing HETS_LIB environment variable"
  getSigSens CSL (hlib ++ lb) sp

sig :: Int -> IO Sign
sig = fmap fst . l1

-- Check if the order is broken or not!
sens :: Int -> IO [(String, CMD)]
sens = fmap snd . l1

cmds :: Int -> IO [CMD]
cmds = fmap (map snd) . sens


-- time measurement, pendant of the time shell command
time :: IO a -> IO a
time p = do
  t <- getCurrentTime
  res <- p
  t' <- getCurrentTime
  putStrLn $ show $ diffUTCTime t' t
  return res




-- ----------------------------------------------------------------------
-- * calculator test functions
-- ----------------------------------------------------------------------

runTest :: ResultT (IOS b) a -> b -> IO a
runTest cmd r = fmap fromJust $ runTestM cmd r

runTestM :: ResultT (IOS b) a -> b -> IO (Maybe a)
runTestM cmd r = fmap (resultToMaybe . fst) $ runIOS r $ runResultT cmd

runTest_ :: ResultT (IOS b) a -> b -> IO (a, b)
runTest_ cmd r = do
  (res, r') <- runIOS r $ runResultT cmd
  return (fromJust $ resultToMaybe res, r')


evalL :: CalculationSystem (ResultT (IOS b)) => b
      -> Int -- ^ Test-spec
      -> IO b
evalL s i = do
  cl <- cmds i
  (_, s') <- runIOS s (runResultT $ evaluateList cl)
  return s'


-- ----------------------------------------------------------------------
-- * different parser
-- ----------------------------------------------------------------------

toE :: String -> EXPRESSION
toE = fromJust . parseResult

-- parses a single extparam range such as: "I>0, J=1"
toEP :: String -> [EXTPARAM]
toEP [] = []
toEP inp = case runParser (Lexer.separatedBy extparam pComma >-> fst) "" "" inp of
             Left e -> error $ show e
             Right s -> s


-- parses lists of extparam ranges such as: "I>0, J=1; ....; I=10, J=1"
toEPL :: String -> [[EXTPARAM]]
toEPL [] = []
toEPL inp = case runParser
             (Lexer.separatedBy
              (Lexer.separatedBy extparam pComma >-> fst) pSemi >-> fst) "" "" inp of
              Left e -> error $ show e
              Right s -> s

toEP1 :: String -> EPExp
toEP1 inp = case runParser extparam "" "" inp of
             Left e -> error $ show e
             Right s -> snd $ fromJust $ toEPExp s

toEPs :: String -> EPExps
toEPs = toEPExps . toEP

toEPLs :: String -> [EPExps]
toEPLs = map toEPExps . toEPL

-- ----------------------------------------------------------------------
-- * static analysis functions
-- ----------------------------------------------------------------------


-- let al = filter ( \ x -> case x of Cmd ":=" _ -> True ; _ -> False) l


-- ----------------------------------------------------------------------
-- * Extended Parameter tests
-- ----------------------------------------------------------------------

printOrdEPs :: String -> IO ()
printOrdEPs s = let ft = forestFromEPs (flip makeEPLeaf ()) $ toEPLs s
                in putStrLn $ showEPForest show ft
--forestFromEPs :: (a -> EPTree b) -> [a] -> EPForest b


compareEPgen :: Show a => (String -> a) -> (a -> a -> EPCompare) -> String -> String -> IO EPCompare
compareEPgen p c a b =
    let epA = p a
        epB = p b
    in do
      putStrLn $ show epA
      putStrLn $ show epB
      return $ c epA epB

compareEP' = compareEPgen toEP1 compareEP
compareEPs' = compareEPgen toEPs compareEPs

-- ----------------------------------------------------------------------
-- * MAPLE INTERPRETER
-- ----------------------------------------------------------------------

-- just call the methods in MapleInterpreter: mapleInit, mapleExit, mapleDirect
-- , the CS-interface functions and evalL



-- ----------------------------------------------------------------------
-- * FIRST REDUCE INTERPRETER
-- ----------------------------------------------------------------------



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
  (res, s') <- runIOS s (runResultT $ runStateT c emptyVCCache)
  let (r, vcc') = fromJust $ resultToMaybe res
  return $ WithAB vcc' s' r

--s -> t -> t1 -> IO (Common.Result.Result a, s)
-- ttesd :: ( VarGen (ResultT (IOS s))
--          , VariableContainer a VarRange
--          , CalculationSystem (ResultT (IOS s))
--          , Cache (ResultT (IOS s)) a String EXPRESSION) =>
--         EXPRESSION -> s -> a -> IO (WithAB a s EXPRESSION)
ttesd e = runTT (substituteDefined e)

ttesdi e = runTTi (substituteDefined e)

-- -- substituteDefined with init
--ttesdi s e = ttesd s vc e

{-
r <- mapleInit 1
r <- redcInit 3
r' <- evalL r 3
let e = toE "sin(x) + 2*cos(y) + x^2"
w <- ttesdi e r'
let vss = getA w

w' <- ttesd e r' vss
w' <- ttesd e r' vss

mapleExit r


y <- fmap fromJust $ runTest (CSL.Interpreter.lookup "y") r'
runTest (verificationCondition y $ toE "cos(x)") r'
pretty it

r <- mapleInit 4
r <- redcInit 4
r' <- evalL r 301
let t = toE "cos(z)^2 + cos(z ^2) + sin(y) + sin(z)^2"
t' <- runTest (eval t) r'
vc <- runTest (verificationCondition t' t) r'
pretty vc
-}

{-
-- exampleRun
r <- mapleInit 4
let t = toE "factor(x^5-15*x^4+85*x^3-225*x^2+274*x-120)"
t' <- runTest (eval t) r
vc <- runTest (verificationCondition t' t) r
pretty vc


-- exampleRun2

r <- mapleInit 4
r' <- evalL r 1011
let t = toE "factor(x^5-z4*x^4+z3*x^3-z2*x^2+z1*x-z0)"
t' <- runTest (eval t) r'
vc <- runTest (verificationCondition t' t) r'
pretty vc

let l = ["z4+z3+20", "z2 + 3*z4 + 4", "3 * z3 - 30", "5 * z4 + 10", "15"]
let tl = map toE l
tl' <- mapM (\x -> runTest (eval x) r') tl
vcl <- mapM (\ (x, y) -> runTest (verificationCondition x y) r') $ zip tl' tl
mapM_ putStrLn $ map pretty vcl
-}
