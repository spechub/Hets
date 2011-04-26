{-# LANGUAGE TypeSynonymInstances, FlexibleContexts #-}
{- |
Module      :  $Header$
Description :  The AnEven-Tool: an (An)alyzer and (Ev)aluator for (En)CL
               specifications
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (uses type-expression in type contexts)

The AnEven-Tool: an (An)alyzer and (Ev)aluator for (En)CL specifications.
Provides functionality for interactive experimenting with EnCL specifications.
-}


module CSL.AnEvenTool where

import Interfaces.Process as PC

import Control.Monad.State (StateT(..))
import Control.Monad.Error (MonadError(..))

import Static.SpecLoader (getSigSensComplete, SigSens(..))


import CSL.MathematicaInterpreter
import CSL.MapleInterpreter 
import CSL.Interpreter
import CSL.Logic_CSL

--import CSL.Analysis
import CSL.DependencyGraph
import CSL.GuardedDependencies
import CSL.EPElimination

import CSL.AS_BASIC_CSL
import CSL.Sign
import CSL.Parse_AS_Basic
import CSL.Verification

import Common.Utils (getEnvDef)
import Common.DocUtils
import Common.Doc
import Common.AS_Annotation

import Driver.Options

import Control.Monad.State.Class
import Control.Monad.Reader
import Data.Char
import Data.Maybe
import Data.Time.Clock

import qualified CSL.SMTComparison as CMP
import CSL.EPRelation
import System.IO
import System.Directory
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List

instance Pretty Bool where
    pretty = text . show


data CAS = Maple | Mathematica deriving (Show, Read, Eq)

data CASState = MapleState MITrans | MathematicaState MathState

-- ----------------------------------------------------------------------
-- * AnEven-Tool
-- ----------------------------------------------------------------------













-- ----------------------------------------------------------------------
-- * The functionality for the EvalSpec-Tool
-- ----------------------------------------------------------------------

-- TODO: clean this part, replace it with the AnEven functionality
-- when finished.

--------------------------- Shortcuts --------------------------

initFlags :: (StepDebugger m, SymbolicEvaluator m) => Bool -> Bool -> m ()
initFlags sm dm = do
  setSymbolicMode sm
  setDebugMode dm
    
evalWithVerification :: Bool -- ^ auto-close connection
                     -> CAS -> Maybe FilePath -> Maybe String -> Bool -> Bool
                     -> DTime -> Int -> String -> String -> IO CASState
evalWithVerification cl c mFp mN smode dmode to v lb sp =
  let -- exitWhen s = null s || s == "q" || take 4 s == "quit" || take 4 s == "exit"
      -- program for initialization
        
      p prog = do
         prettyInfo $ text ""
         prettyInfo $ text "****************** Assignment store loaded ******************"
         prettyInfo $ text ""
         mE <- verifyProg prog
         when (isJust mE) $ prettyInfo $ pretty $ fromJust mE
         -- readEvalPrintLoop stdin stdout ">" exitWhen
  in case c of
       Maple -> do
              (mit, _) <- testWithMapleGen v to (initFlags smode dmode) p lb sp
              when cl $ mapleExit mit >> return ()
              return $ MapleState mit
       Mathematica -> do
              (mst, _) <- testWithMathematicaGen v mFp mN (initFlags smode dmode) p lb sp
              when cl $ mathematicaExit mst
              return $ MathematicaState mst



{-
mapleLoop :: MITrans -> IO ()
mapleLoop mit = do
  x <- getLine
  if x == "q" then mapleExit mit >> return ()
              else mapleDirect False mit x >>= putStrLn >> mapleLoop mit
                  
-}       

-- ----------------------------------------------------------------------
-- ** Gluing the Analysis and Evaluation together
-- ----------------------------------------------------------------------



test :: (Pretty a, MonadIO m) => Int -> ([Named CMD] -> m a) -> m ()
test i f = testResult i f >>= liftIO . putStrLn . show . pretty

testResult :: (Pretty a, MonadIO m) => Int -> ([Named CMD] -> m a) -> m a
testResult i f = liftIO (sens i) >>= f

-- | Returns sorted assignment store and program after EP elimination
assStoreAndProgElim :: [Named CMD] -> IO ([(ConstantName, AssDefinition)], [Named CMD])
assStoreAndProgElim ncl = do
  let (asss, prog) = splitAS ncl
      gm = fmap analyzeGuarded asss
      sgl = dependencySortAS gm
      ve = CMP.VarEnv { CMP.varmap = Map.fromList $ zip ["I", "F"] [1..]
                      , CMP.vartypes = Map.empty
                      , CMP.loghandle = Just stdout
                      --, CMP.loghandle = Nothing
                      }
      -- ve = emptyVarEnv $ Just stdout
  el <- execSMTTester' ve $ epElimination sgl
  return (getElimAS el, prog)



-- | Returns sorted assignment store and program without EP elimination
assStoreAndProgSimple :: [Named CMD] -> IO ([(ConstantName, AssDefinition)], [Named CMD])
assStoreAndProgSimple ncl = do
  let (asss, prog) = splitAS ncl
      gm = fmap analyzeGuarded asss
      sgl = dependencySortAS gm
  return (getSimpleAS sgl, prog)



loadAssignmentStore :: (MonadState (ASState st) m, AssignmentStore m, MonadIO m) => Bool -> [Named CMD]
                -> m ([(ConstantName, AssDefinition)], [Named CMD])
loadAssignmentStore b ncl = do
  let f = if b then assStoreAndProgElim else assStoreAndProgSimple
  res@(asss, _) <- liftIO $ f ncl
  loadAS asss
  return res


stepProg :: (MessagePrinter m, MonadIO m, MonadError ASError m) =>
            [Named CMD] -> m (Maybe ASError)
stepProg ncl = stepwiseSafe interactiveStepper $ Sequence $ map sentence ncl

verifyProg :: (MessagePrinter m, StepDebugger m, VCGenerator m, MonadIO m, MonadError ASError m) =>
              [Named CMD] -> m (Maybe ASError)
verifyProg ncl = do
  stepwiseSafe verifyingStepper $ Sequence $ map sentence ncl

testWithMapleGen :: Int -> DTime -> MapleIO b -> ([Named CMD] -> MapleIO a) -> String -> String
                 -> IO (MITrans, a)
testWithMapleGen v to = testWithCASGen rf where
    rf adg prog =
        runWithMaple adg v to
           [ "EnCLFunctions"
           -- , "intpakX" -- Problems with the min,max functions, they are remapped by this package!
           ] prog


testWithMathematicaGen :: Int -> Maybe FilePath -> Maybe String
                       -> MathematicaIO b -> ([Named CMD] -> MathematicaIO a) -> String -> String
                       -> IO (MathState, a)
testWithMathematicaGen v mFp mN = testWithCASGen rf where
    rf adg prog =
        runWithMathematica adg v mFp mN
           [ "/home/ewaryst/Hets/CSL/CAS/Mathematica.m" ] prog




testWithMaple :: Int -> DTime -> ([Named CMD] -> MapleIO a) -> Int -> IO (MITrans, a)
testWithMaple verb to f = uncurry (testWithMapleGen verb to (return ()) f) . libFP





getMathState :: Maybe CASState -> MathState
getMathState (Just (MathematicaState mst))  = mst
getMathState _ = error "getMathState: no MathState"

getMapleState :: Maybe CASState -> MITrans
getMapleState (Just (MapleState mst))  = mst
getMapleState _ = error "getMapleState: no Maple state"


testWithCASGen :: ( AssignmentStore as, MonadState (ASState st) as, MonadIO as) =>
                  (AssignmentDepGraph () -> as a -> IO (ASState st, a))
                      -> as b -> ([Named CMD] -> as a)
                      -> String -> String -> IO (ASState st, a)
testWithCASGen rf ip f lb sp = do
  ncl <- fmap sigsensNamedSentences $ sigsensGen lb sp
  -- get ordered assignment store and program
  (as, prog) <- assStoreAndProgSimple ncl
  vchdl <- openFile "/tmp/vc.out" WriteMode
  -- build the dependency graph
  let gr = assDepGraphFromDescList (const $ const ()) as
      -- make sure that the assignment store is loaded into maple before
      -- the execution of f
      g x = ip >> loadAS as >> modify (\ mit -> mit {vericondOut = Just vchdl}) >> f x

  -- start maple and run g
  res <- rf gr $ (withLogFile "/tmp/evalWV.txt" . g) prog
  hClose vchdl
  return res



-- ----------------------------------------------------------------------
-- ** Temp tools
-- ----------------------------------------------------------------------







-- | Returns all constants where the given constants depend on
depClosure :: [String] -> [Named CMD] -> IO [[String]]
depClosure l ncl = do
  let (asss, _) = splitAS ncl
      gm = fmap analyzeGuarded asss
      dr = getDependencyRelation gm
  return $ relLayer dr l

-- | mark final
markFinal :: [String] -> [Named CMD] -> IO [String]
markFinal l ncl = do
  let (asss, _) = splitAS ncl
      gm = fmap analyzeGuarded asss
      dr = getDependencyRelation gm
      f x = case Map.lookup x dr of
              Just s -> if Set.null s then x ++ " *" else x
              _ -> x ++ " *"
  return $ map f l


-- | definedIn
definedIn :: [String] -> [Named CMD] -> IO [String]
definedIn l ncl = return $ map g l where
      g s = intercalate ", " (mapMaybe (f s) ncl) ++ ":" ++ s
      f s nc = case sentence nc of
                 Ass (Op oi _ _ _) _ ->
                     if simpleName oi == s then Just $ senAttr nc else Nothing
                 _ -> Nothing

inDefinition :: [String] -> [Named CMD] -> IO [String]
inDefinition l ncl =
  let (asss, _) = splitAS ncl
      gm = fmap analyzeGuarded asss
      dr = getDependencyRelation gm
      allDefs = allDefinitions ncl
      br = Map.filterWithKey (\k _ -> elem k l) $ getBackRef dr
      f m l' = map (g m) l'
      g m x = Map.findWithDefault "" x m
      h = f allDefs
      f' (x,y) = x ++ ": " ++ intercalate ", " y
  in return $ map f' $ Map.toList $ fmap h br


allDefinitions :: [Named CMD] -> (Map.Map String String)
allDefinitions ncl = Map.fromList $ mapMaybe f ncl where
    f nc = case sentence nc of
             Ass (Op oi _ _ _) _ -> Just (simpleName oi, senAttr nc)
             _ -> Nothing

undef :: [Named CMD] -> [String]
undef ncl = Set.toList $ undefinedConstants $ fst $ splitAS ncl

-- printSetMap Common.Doc.empty Common.Doc.empty dr

relLayer :: Ord a => Rel2 a -> [a] -> [[a]]
relLayer _ [] = []
relLayer r l = l : relLayer r succs where
    succs = Set.toList $ Set.unions $ mapMaybe (flip Map.lookup r) l


-- emptyVarEnv
-- execSMTComparer :: VarEnv -> SmtComparer a -> IO a
-- splitAS :: [Named CMD] -> (GuardedMap [EXTPARAM], [Named CMD])
-- getElimAS :: [(String, Guarded EPRange)] -> [(ConstantName, AssDefinition)]
-- dependencySortAS :: GuardedMap EPRange -> [(String, Guarded EPRange)]
-- epElimination :: CompareIO m => [(String, Guarded EPRange)] -> m [(String, Guarded EPRange)]

casConst :: ASState a -> String -> String
casConst mit s =
    fromMaybe "" $ rolookup (getBMap mit) $ SimpleConstant s


enclConst :: ASState a -> String -> OPID
enclConst mit s =
    fromMaybe (error $ "enclConst: no mapping for " ++ s) $ revlookup (getBMap mit) s


-- ----------------------------------------------------------------------
-- ** general test functions
-- ----------------------------------------------------------------------


-- Testing of keyboard-input
charInfo :: IO ()
charInfo = do
  c <- getChar
--  when (c /= 'e') $ putStrLn "" >> putStrLn (c:[]) >> putStrLn (show $ ord c) >> charInfo
  -- Escape-button = 27
  when (ord c /= 27) $ putStrLn "" >> putStrLn (c:[]) >> putStrLn (show $ ord c) >> charInfo


testspecs :: [(Int, ([Char], [Char]))]
testspecs =
    [ (44, ("EnCL/EN1591.het", "EN1591"))
    , (45, ("EnCL/flange.het", "Flange"))
    , (46, ("EnCL/flange.het", "FlangeComplete"))
    , (54, ("EnCL/EN1591S.het", "EN1591"))
    , (55, ("EnCL/flangeS.het", "Flange"))
    , (56, ("EnCL/flangeS.het", "FlangeComplete"))
    , (65, ("EnCL/flangeDefault.het", "FlangeDefault"))
    , (66, ("EnCL/flangeExported.het", "FlangeComplete"))
    ]


sigsensGen :: String -> String -> IO (SigSens Sign CMD)
sigsensGen lb sp = do
  hlib <- getEnvDef "HETS_LIB" $ error "Missing HETS_LIB environment variable"
  b <- doesFileExist lb
  let fp = if b then lb else hlib ++ "/" ++ lb
      ho = defaultHetcatsOpts { libdirs = [hlib]
                              , verbose = 0 }

  res <- getSigSensComplete True ho CSL fp sp
  putStrLn "\n"
  return res

siggy :: Int -> IO (SigSens Sign CMD)
siggy = uncurry sigsensGen . libFP

libFP :: Int -> (String, String)
libFP i = fromMaybe (if i >= 0 then ("EnCL/Tests.het", "Test" ++ show i)
                            else ("EnCL/ExtParamExamples.het", "E" ++ show (- i)))
          $ Prelude.lookup i testspecs

sigsens :: Int -> IO (Sign, [Named CMD])
sigsens i = do
  res <- siggy i
  return ( sigsensSignature res, sigsensNamedSentences res )

sig :: Int -> IO Sign
sig = fmap fst . sigsens

-- Check if the order is broken or not!
sens :: Int -> IO [Named CMD]
sens = fmap snd . sigsens

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


toE :: String -> EXPRESSION
toE = fromJust . parseExpression operatorInfoMap

toCmd :: String -> CMD
toCmd = fromJust . parseCommand



-- ----------------------------------------------------------------------
-- ** Smt testing instances
-- ----------------------------------------------------------------------


data TestEnv = TestEnv { counter :: Int
                       , varenv :: CMP.VarEnv
                       , loghdl :: Handle }

logf :: FilePath
logf = "/tmp/CSL.log"

teFromVE :: CMP.VarEnv -> IO TestEnv
teFromVE ve = do
  hdl <- openFile logf WriteMode
  let ve' = ve{ CMP.loghandle = Just hdl }
  return TestEnv { counter = 0, varenv = ve', loghdl = hdl }

type SmtTester = StateT TestEnv IO

execSMTTester :: CMP.VarEnv -> SmtTester a -> IO (a, Int)
execSMTTester ve smt = do
  (x, s) <- teFromVE ve >>= runStateT smt
  hClose $ loghdl s
  return (x, counter s)

execSMTTester' :: CMP.VarEnv -> SmtTester a -> IO a
execSMTTester' ve smt = do
  (x, i) <- execSMTTester ve smt
  putStrLn $ "SMT-Checks: " ++ show i
  return x

instance CompareIO SmtTester where
    logMessage x = do
      hdl <- gets loghdl
      liftIO $ hPutStrLn hdl x
    rangeFullCmp r1 r2 = do
      env <- get
      let f x = x{counter = counter x + 1}
          ve = varenv env
          vm = CMP.varmap ve
          hdl = loghdl env
      modify f
      lift $ writeRangesToLog hdl r1 r2
      liftIO $ hPutStrLn hdl ""
      res <- lift $ CMP.smtCompare ve (boolRange vm r1) $ boolRange vm r2
      lift $ writeRangesToLog hdl r1 r2 >> hPutStrLn hdl ("=" ++ show res)
      return res

writeRangesToLog :: Handle -> EPRange -> EPRange -> IO ()
writeRangesToLog hdl r1 r2= do
  let [d1, d2] = map diagnoseEPRange [r1, r2]
  hPutStr hdl $ show $ text "Cmp" <> parens (d1 <> comma <+> d2)

