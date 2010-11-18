{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
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
import CSL.EPBasic
import CSL.TreePO
import CSL.ExtendedParameter
import CSL.SMTComparison
import CSL.EPRelation -- (compareEP, EPExp, toEPExp, compareEPs, EPExps, toEPExps, forestFromEPs, makeEPLeaf, showEPForest)
import CSL.Logic_CSL
import CSL.Analysis
import CSL.AS_BASIC_CSL
import CSL.Parse_AS_Basic (parseResult, extparam, pComma, pSemi)
import CSL.Sign

import Common.Utils (getEnvDef)
import Common.IOS
import Common.Result (diags, printDiags, resultToMaybe)
import Common.ResultT
import Common.Lexer as Lexer
import Common.Parsec
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel
import Text.ParserCombinators.Parsec

-- the process communication interface
import qualified Interfaces.Process as PC

-- README: In order to work correctly link the Test.hs in the Hets-root dir to Main.hs (ln -s Test.hs Main.hs)
import Main (getSigSens)

import Control.Monad.State.Class
import Control.Monad.State (StateT(..))
import Control.Monad.Trans (MonadIO (..), lift)
import Control.Monad (liftM)
import Data.Maybe
import Data.Time.Clock
import qualified Data.Map as Map
import qualified Data.Set as Set

-- ----------------------------------------------------------------------
-- * general test functions
-- ----------------------------------------------------------------------

-- TODO: check with inherited sentences (flange2)!
-- TODO: build a new OpString entry for elim constants (see Analysis.hs)
testspecs =
    [ (44, ("/CSL/EN1591.het", "EN1591"))
    , (45, ("/CSL/flange2.het", "Flange2"))
    ]

l1 :: Int -> IO (Sign, [Named CMD])
l1 i = do
  let (lb, sp) = fromMaybe (if i > 0 then ("/CSL/Tests.het", "Test" ++ show i)
                            else ("/CSL/ExtParamExamples.het", "E" ++ show (- i)))
                 $ Prelude.lookup i testspecs
  hlib <- getEnvDef "HETS_LIB" $ error "Missing HETS_LIB environment variable"
  getSigSens CSL (hlib ++ lb) sp

sig :: Int -> IO Sign
sig = fmap fst . l1

-- Check if the order is broken or not!
sens :: Int -> IO [Named CMD]
sens = fmap snd . l1

cmds :: Int -> IO [CMD]
cmds = fmap (map sentence) . sens

-- time measurement, pendant of the time shell command
time :: MonadIO m => m a -> m a
time p = do
  t <- liftIO getCurrentTime
  res <- p
  t' <- liftIO getCurrentTime
  liftIO $ putStrLn $ show $ diffUTCTime t' t
  return res


{-
show guarded assignments:

:m +CSL.Analysis
sl <- sens 3
fst $ splitAS s
-}

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


evalL :: AssignmentStore (ResultT (IOS b)) => b
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
toEP s = case runParser (Lexer.separatedBy extparam pComma >-> fst) "" "" s of
             Left e -> error $ show e
             Right s' -> s'


-- parses lists of extparam ranges such as: "I>0, J=1; ....; I=10, J=1"
toEPL :: String -> [[EXTPARAM]]
toEPL [] = []
toEPL s = case runParser
             (Lexer.separatedBy
              (Lexer.separatedBy extparam pComma >-> fst) pSemi >-> fst) "" "" s of
              Left e -> error $ show e
              Right s' -> s'

toEP1 :: String -> EPExp
toEP1 s = case runParser extparam "" "" s of
             Left e -> error $ show e
             Right s' -> snd $ fromJust $ toEPExp s'

toEPs :: String -> EPExps
toEPs = toEPExps . toEP

toEPLs :: String -> [EPExps]
toEPLs = map toEPExps . toEPL

-- ----------------------------------------------------------------------
-- * Extended Parameter tests
-- ----------------------------------------------------------------------

{-
smtEQScript vMap (boolRange vMap $ epList!!0) (boolRange vMap $ epList!!1)
test for smt-export
let m = varMapFromList ["I", "J", "K"]

let be = boolExps m $ toEPs "I=0"
smtBoolExp be

compare-check for yices
let l2 = [(x,y) | x <- epList, y <- epList]
let l3 = map (\ (x, y) -> smtCompareUnsafe vEnv (boolRange vMap x) (boolRange vMap y)) l2
putStrLn $ unlines $ map show $ zip l3 l2

:l CSL/InteractiveTests.hs
:m +CSL.Analysis
sl <- sens (-82)
let grdm = fst $ splitAS sl
let sgm = dependencySortAS grdm

let grdd = snd $ Map.elemAt 0 grdm
let sgm = dependencySortAS grdm

getDependencyRelation grdm

:l CSL/InteractiveTests.hs
:m +CSL.Analysis

gm <- fmap grddMap $ sens (-3)

let (_, xg) = Map.elemAt 1 gm
let (_, yg) = Map.elemAt 2 gm

let f grd = (grd, toEPExps $ range grd)
let frst = forestFromEPs f $ guards xg

putStrLn $ showEPForest show frst

foldForest (\ x y z -> x ++ [(y, length z)]) [] frst 


-}

crossprod l [] = map (:[]) l
crossprod l l' = concatMap (\ x -> map (:x) l) l'

{-
let a = [(-5)..5]
let b = [[]]
let b = []
crossprod a b
[x : y | x <- a, y <- b]
-}
 

-- irreflexive triangle of a list l: for i < j . (l_i, l_j)
irrTriang :: [a] -> [(a,a)]
irrTriang [] = []
irrTriang (x:l) = map ((,) x) l ++ irrTriang l

-- * Model Generation
frmAround "" = ""
frmAround s = let l = lines s
                  hd = "--" ++ map (const '-') (head l)
              in unlines $ hd : map (('|':) . (++"|")) l ++ [hd]

modelRg1 :: Map.Map String (Int, Int)
modelRg1 = Map.fromList [("I", (-5, 5))]
modelRg2 :: Map.Map String (Int, Int)
modelRg2 = Map.fromList [("I", (-5, 5)), ("J", (-5, 5))]
modelRg3 :: Map.Map String (Int, Int)
modelRg3 = Map.fromList [("I", (-5, 5)), ("J", (-5, 5)), ("K", (-5, 5))]

printModel :: Map.Map String (Int, Int) -> EPRange -> String
printModel x y = modelToString boolModelChar $ modelOf x y

pM1::EPRange -> IO ()
pM2::EPRange -> IO ()
pM1s::[EPRange] -> IO ()
pM2s::[EPRange] -> IO ()

pM2 = putStr . frmAround . printModel modelRg2
pM1 = putStr . frmAround . printModel modelRg1
pM1s = mapM_ pM1
pM2s = mapM_ pM2

toEPR :: String -> EPRange
toEPR = Atom . toEPs

-- Test for partitioning taken from E82 in CSL/ExtParamExamples.het
el11 :: [EPRange]
el11 = let x1 = toEPR "I>=0" in [x1, Complement x1]

el12 :: [EPRange]
el12 = let l = map toEPR ["I=1", "I>1"] in Complement (Union l) : l

el13 :: [EPRange]
el13 = let x1 = toEPR "I>0" in [x1, Complement x1]


el21 :: [EPRange]
el21 = let x1 = toEPR "I>=0" in [x1, Complement x1]

el22 :: [EPRange]
el22 = let l = map toEPR ["I>=0, J>=0", "I<4, J<=4"]
           inter = Intersection l
           uni = Union l
       in uni : inter : Intersection [uni, Complement inter] : l

el23 :: [EPRange]
el23 = let x1 = toEPR "I>0" in [x1, Complement x1]


-- * Partition tests

checkForPartition :: [EPRange] -> IO Bool
checkForPartition l = execSMTComparer vEnv1 $ f g l where
    f a [] = return True
    f a (x:l') = do
      res <- mapM (a x) l'
      res' <- f a l'
      return $ and $ res' : res
    g x y = fmap (Incomparable Disjoint ==) $ rangeCmp x y


part1 :: Partition Int
part1 = AllPartition 10

part2 :: Partition Int
part2 = Partition $ zip el11 [33 ..]

part3 :: Partition Int
part3 = Partition $ zip el12 [1 ..]

part4 :: Partition Int
part4 = Partition $ zip el13 [91 ..]

parts = [part1, part2, part3, part4]

refinePart a b = execSMTComparer vEnv1 $ refinePartition a b

allRefin = do
  m1 <- mapM (uncurry refinePart) $ irrTriang parts
  m2 <- mapM (uncurry refinePart) $ irrTriang m1
  return (m1, m2)

allRShow = do
  (a, b) <- allRefin
  showPart1s a
  putStrLn "=============================================="
  showPart1s b

allRCmp = do
  (a, b) <- allRefin
  cmpRg1s a
  putStrLn "=============================================="
  cmpRg1s b


showPart1s :: Show a => [Partition a] -> IO ()
showPart1s = let f x = showPart1 x >> putStrLn "==="
             in  mapM_ f

showPartX :: Show a => (EPRange -> IO ()) -> Partition a -> IO ()
showPart1 :: Show a => Partition a -> IO ()
showPart2 :: Show a => Partition a -> IO ()

showPartX _ (AllPartition x) = do
  putStrLn $ show x
  putStrLn "All\n\n"

showPartX fM (Partition l) =
  let f (re, x) = do
        putStrLn $ show x
        fM re
        putStrLn "\n"
  in mapM_ f l

showPart1 = showPartX pM1
showPart2 = showPartX pM2

class HasRanges a where
    getRanges :: a -> [EPRange]

instance HasRanges (Partition a) where
    getRanges (AllPartition x) = []
    getRanges (Partition l) = map fst l

instance HasRanges a => HasRanges [a] where
    getRanges = concatMap getRanges

instance HasRanges (Guarded EPRange) where
    getRanges = map range . guards

instance HasRanges (String, Guarded EPRange) where
    getRanges = map range . guards . snd

cmpRg1 :: HasRanges a => a -> IO ()
cmpRg1 = putStrLn . concat . map (printModel modelRg1) . getRanges

cmpRg1s :: HasRanges a => [a] -> IO ()
cmpRg1s = let f = putStrLn . concat . map (printModel modelRg1) . getRanges
              g x = f x >> putStrLn "==="
          in mapM_ g

-- * elim proc testing

{-
:l CSL/InteractiveTests.hs
:m +CSL.Analysis
sl <- sens (-82)
let grdm = fst $ splitAS sl
let sgm = dependencySortAS grdm
-}


data TestEnv = TestEnv { counter :: Int
                       , varenv :: VarEnv }


teFromVE :: VarEnv -> TestEnv
teFromVE ve = TestEnv { counter = 0, varenv = ve }

type SmtTester = StateT TestEnv IO

execSMTTester :: VarEnv -> SmtTester a -> IO (a, Int)
execSMTTester ve smt = do
  (x, s) <- runStateT smt $ teFromVE ve
  return (x, counter s)

instance CompareIO SmtTester where
    rangeFullCmp r1 r2 = do
      env <- get
      let f x = x{counter = counter x + 1}
          ve = varenv env
          vm = varmap ve
      modify f
      lift $ smtCompare ve (boolRange vm r1) $ boolRange vm r2


-- elimTestInit :: Int -> [(String, Guarded EPRange)] -> IO [Guard EPRange]
elimTestInit i gl = do
  let grd = (guards $ snd $ head gl)!!i
  (a, i) <- execSMTTester vEnv $ eliminateGuard Map.empty grd
  putStrLn $ "SMT-Checks: " ++ show i
  return a

pgX :: (EPRange -> IO a) -> Guard EPRange -> IO ()
pgX fM grd = do
  fM $ range grd
  putStr "Def: "
  putStrLn $ show $ pretty $ definition grd
  putStrLn ""

pg1 :: Guard EPRange -> IO ()
pg1 = pgX pM1

pg2 :: Guard EPRange -> IO ()
pg2 = pgX pM2

pgrddX :: (EPRange -> IO a) -> Guarded EPRange -> IO ()
pgrddX fM grdd = mapM_ (pgX fM) $ guards grdd
  
pgrdd2 :: Guarded EPRange -> IO ()
pgrdd2 = pgrddX pM2

printASX :: (EPRange -> IO a) -> [(String, Guarded EPRange)] -> IO ()
printASX fM l = mapM_ f l where
    f (s, grdd) = do
      putStr s
      putStrLn ":"
      pgrddX fM grdd
      putStrLn ""

printAS1 :: [(String, Guarded EPRange)] -> IO ()
printAS1 = printASX pM1

printAS2 :: [(String, Guarded EPRange)] -> IO ()
printAS2 = printASX pM2

testElim :: Int -> IO [(String, Guarded EPRange)]
testElim i = prepareAS i >>= elimEPs

prepareAS :: Int -> IO [(String, Guarded EPRange)]
prepareAS = liftM (dependencySortAS . fmap analyzeGuarded . fst . splitAS) . sens

-- get the first guarded-entry from the AS
-- grdd <- fmap (snd . head) $ getAS (-821)

getAS :: Int -> IO [(String, Guarded [EXTPARAM])]
getAS = liftM (Map.toList . fst . splitAS) . sens

getASana :: Int -> IO [(String, Guarded EPRange)]
getASana = liftM (Map.toList . fmap analyzeGuarded . fst . splitAS) . sens

elimEPs :: [(String, Guarded EPRange)] -> IO [(String, Guarded EPRange)]
elimEPs l = do
  -- execSMTComparer vEnv $ epElimination l
  (a, i) <- execSMTTester vEnv $ epElimination l
  putStrLn $ "SMT-Checks: " ++ show i
  return a


grddMap :: [Named CMD] -> GuardedMap [EXTPARAM]
grddMap = foldr (uncurry $ addAssignment "?") Map.empty . assignments

assignments :: [Named CMD] -> [(EXPRESSION, EXPRESSION)]
assignments = assignments' . map sentence

assignments' :: [CMD] -> [(EXPRESSION, EXPRESSION)]
assignments' = mapMaybe getAss

getAss (Ass c def) = Just (c,def)
getAss _ = Nothing

varEnvFromList :: [String] -> VarEnv
varEnvFromList l = error ""

-- | Generates from a list of Extended Parameter names an id-mapping
varMapFromList :: [String] -> VarMap
varMapFromList l = Map.fromList $ zip l $ [1 .. length l]

-- | Generates from a list of Extended Parameter names an id-mapping
varMapFromSet :: Set.Set String -> VarMap
varMapFromSet = varMapFromList . Set.toList


epList :: [EPRange]
epList =
    let l = map (Atom . toEPs)
            ["", "I=1,J=0", "I=0,J=0", "I=0", "I=1", "J=0", "I>0", "I>2", "I>0,J>2"]
    in Intersection l : Union l : l

epDomain :: [(String, EPExps)]
epDomain = zip ["I", "J"] $ map toEPs ["I>=0", "J>=0"]

vMap :: Map.Map String Int
vMap = varMapFromSet $ namesInList epList

-- vTypes = Map.map (const Nothing) vMap
vTypes = Map.fromList $ map (\ (x,y) -> (x, boolExps vMap y)) epDomain

vEnv = VarEnv { varmap = vMap, vartypes = Map.empty }

vEnv1 = VarEnv { varmap = Map.fromList [("I", 1)], vartypes = Map.empty }

vEnvX = VarEnv { varmap = vMap, vartypes = vTypes }


printOrdEPs :: String -> IO ()
printOrdEPs s = let ft = forestFromEPs ((,) ()) $ toEPLs s
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

redcNames :: RITrans -> IO [ConstantName]
redcNames = runTest $ liftM toList names

redcValues :: RITrans -> IO [(ConstantName, EXPRESSION)]
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
--          , AssignmentStore (ResultT (IOS s))
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

-- show value for const x
runTest (CSL.Interpreter.lookup "x") r' >>= return . pretty

runTest (CSL.Interpreter.eval $ toE "cos(x-x)") r' >>= return . pretty

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

-- ----------------------------------------------------------------------
-- * Utilities
-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- ** Operator extraction
-- ----------------------------------------------------------------------

addOp :: Map.Map String Int -> String -> Map.Map String Int
addOp mp s = Map.insertWith (+) s 1 mp

class OpExtractor a where
    extr :: Map.Map String Int -> a -> Map.Map String Int

instance OpExtractor EXPRESSION where
    extr m (Op op _ l _) = extr (addOp m $ show op) l
    extr m (Interval _ _ _) = addOp m "!Interval"
    extr m (Int _ _) = addOp m "!Int"
    extr m (Double _ _) = addOp m "!Double"
    extr m (List l _) = extr (addOp m "!List") l
    extr m (Var _) = addOp m "!Var"

instance OpExtractor [EXPRESSION] where
    extr = foldl extr

instance OpExtractor (EXPRESSION, [CMD]) where
    extr m (e,l) = extr (extr m e) l

instance OpExtractor CMD where
    extr m (Ass c def) = extr m [c, def]
    extr m (Cmd _ l) = extr m l
    extr m (Sequence l) = extr m l
    extr m (Cond l) = foldl extr m l
    extr m (Repeat e l) = extr m (e,l)

instance OpExtractor [CMD] where
    extr = foldl extr

extractOps :: OpExtractor a => a -> Map.Map String Int
extractOps = extr Map.empty

-- -- ----------------------------------------------------------------------
-- -- ** Assignment extraction
-- -- ----------------------------------------------------------------------

-- addOp :: Map.Map String Int -> String -> Map.Map String Int
-- addOp mp s = Map.insertWith (+) s 1 mp

-- class OpExtractor a where
--     extr :: Map.Map String Int -> a -> Map.Map String Int

-- instance OpExtractor EXPRESSION where
--     extr m (Op op _ l _) = extr (addOp m op) l
--     extr m (Interval _ _ _) = addOp m "!Interval"
--     extr m (Int _ _) = addOp m "!Int"
--     extr m (Double _ _) = addOp m "!Double"
--     extr m (List l _) = extr (addOp m "!List") l
--     extr m (Var _) = addOp m "!Var"

-- instance OpExtractor [EXPRESSION] where
--     extr = foldl extr

-- instance OpExtractor (EXPRESSION, [CMD]) where
--     extr m (e,l) = extr (extr m e) l

-- instance OpExtractor CMD where
--     extr m (Cmd _ l) = extr m l
--     extr m (Sequence l) = extr m l
--     extr m (Cond l) = foldl extr m l
--     extr m (Repeat e l) = extr m (e,l)

-- instance OpExtractor [CMD] where
--     extr = foldl extr

-- extractOps :: OpExtractor a => a -> Map.Map String Int
-- extractOps = extr Map.empty

-- -- ----------------------------------------------------------------------
-- -- * static analysis functions
-- -- ----------------------------------------------------------------------


