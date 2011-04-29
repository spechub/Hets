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


module CSL.AnEvenTool
    -- (evalWithVerification, CAS (..), CASState(..))
        where

import qualified Interfaces.Process as PC

import Control.Monad.Error (MonadError (..))

import Static.SpecLoader (getSigSensComplete, SigSens (..))


import CSL.MathematicaInterpreter
import CSL.MapleInterpreter 
import CSL.Interpreter
import CSL.Logic_CSL

import CSL.DependencyGraph
import CSL.GuardedDependencies
import CSL.EPElimination

import CSL.AS_BASIC_CSL
import CSL.Sign
import CSL.Verification

import Common.Utils (getEnvDef)
import Common.DocUtils
import Common.Doc
import Common.AS_Annotation

import Driver.Options

import Control.Monad.State.Class
import Control.Monad.Reader
import Data.Maybe

import System.IO
import System.Directory


-- Shell handling/building imports
import System.Console.Readline

import System.Console.Shell
import System.Console.Shell.ShellMonad

-- memory access error in runShell when using readline-backend
-- , hence I prefer haskeline!

-- import System.Console.Shell.Backend.Readline
import System.Console.Shell.Backend.Haskeline
-- ----------------------------------------------------------------------

instance Pretty Bool where
    pretty = text . show


data CAS = Maple | Mathematica deriving (Show, Read, Eq)

data CASState = MapleState MITrans | MathematicaState MathState

-- ----------------------------------------------------------------------
-- * AnEven-Tool
-- ----------------------------------------------------------------------

versionInfo :: String
versionInfo = unlines
  [ ""
  , "The AnEven-Tool: an (An)alyzer and (Ev)aluator for"
  , "(En)CL specifications. Version 0.1"
  , "Copyright Ewaryst Schulz, DFKI Bremen 2010"
  , ""
  ]

shellMessage :: String
shellMessage = unlines
  [ "This is free software, and you are welcome to"
  , "redistribute it under certain conditions (GPLv2)."
  ]

-- ----------------------------------------------------------------------
-- ** Basic Datatypes
-- ----------------------------------------------------------------------

data AnEvenConfig = AnEvenConfig

defaultConfig :: AnEvenConfig
defaultConfig = AnEvenConfig

data AnEvenState = 
    AnEvenState
    { stSpec :: Maybe (SigSens Sign CMD) -- current hets environment
    , stConfig :: AnEvenConfig -- the global settings
    , stProg :: Maybe [Named CMD] -- the current program (derived from spec)
    , stDS :: Maybe (GuardedMap [EXTPARAM]) -- the current dependency store
                                            -- (derived from spec)
    }


emptyState :: AnEvenState
emptyState =
    AnEvenState
    { stSpec = Nothing
    , stProg = Nothing
    , stDS = Nothing
    , stConfig = defaultConfig }


-- ----------------------------------------------------------------------
-- ** Basic Interface Functions
-- ----------------------------------------------------------------------

{-

1. loads the spec and translates it to signature and sentences
sigsensGen :: String -> String -> IO (SigSens Sign CMD)

2. sentences are split into guarded dependency store and program
splitAS :: [Named CMD] -> (GuardedMap [EXTPARAM], [Named CMD])

3. guarded dependency is analyzed and made disjoint, to apply it to a dependency store use 'fmap'
analyzeGuarded :: Guarded [EXTPARAM] -> Guarded EPRange

4. the dependency store is sorted by the dependency relation
dependencySortAS :: GuardedMap EPRange -> [(String, Guarded EPRange)]

5. we apply extended parameter elimination to the dependency store
epElimination :: CompareIO m => [(String, Guarded EPRange)] -> m [(String, Guarded EPRange)]

6. the guarded dependency store is flattened to an ordinary one
getElimAS :: [(String, Guarded EPRange)] -> [(ConstantName, AssDefinition)]

6'. as 6, but this one returns in addition a mapping of elim-constants to ranges
getElimAS' :: [(String, Guarded EPRange)] -> ([(ConstantName, AssDefinition)], Map.Map ConstantName EPRange)

-}

-- 1. 
loadSpecEnv :: String -> String -> Sh AnEvenState ()
loadSpecEnv lfn spn = do
  sigs <- liftIO $ sigsensGen lfn spn
  let f st = st { stSpec = Just sigs }
  modifyShellSt f

-- ??. 
stateInfo :: Sh AnEvenState ()
stateInfo = do
  st <- getShellSt
  case stSpec st of
    Just (SigSens { sigsensLibname = ln}) ->
        shellPutInfoLn $ show $ text "Library" <+> pretty ln <+> text "loaded."
    _ -> shellPutInfoLn "System not initialized."



rEPL :: IO ()
rEPL = do
   maybeLine <- readline "% "
   case maybeLine of 
    Nothing     -> return () -- EOF / control-d
    Just "exit" -> return ()
    Just line -> do addHistory line
                    putStrLn $ "The user input: " ++ (show line)
                    rEPL


-- Another repl based on Shellac

-- defaultBackend = readlineBackend
defaultBackend = haskelineBackend

runToolREPL :: AnEvenState -> IO AnEvenState
runToolREPL st = do
    let
      desc =
         (mkShellDescription cmds evalFun)
         { defaultCompletions = Just completeUndefault
         , greetingText       = Just (versionInfo ++ shellMessage)
         , commandStyle       = OnlyCommands
         }
    runShell desc defaultBackend st

runTool :: IO AnEvenState
runTool = runToolREPL emptyState

-- ----------------------------------------------------------------------
-- ** commands
-- ----------------------------------------------------------------------

evalFun :: String -> Sh AnEvenState ()
evalFun s = shellPutInfoLn $ "evaluate " ++ s ++ "!"


completeUndefault :: AnEvenState -> String -> IO [String]
completeUndefault _ s = return $
                        if length s > 2 then [] else
                            map (\x -> s++"Undefault"++show x) [0..length s]

cmds :: [ShellCommand AnEvenState]
cmds =
  [ exitCommand "q"
  , helpCommand "h"

  , cmd "load"       loadSpecEnv    "Loads an EnCL spec from the given file- and specname"
  , cmd "info"       stateInfo      "Show information on the current state"
  ]




-- ----------------------------------------------------------------------
-- * The functionality for the EvalSpec-Tool
-- ----------------------------------------------------------------------

-- TODO: replace it with the AnEven functionality when finished.

--------------------------- Shortcuts --------------------------

initFlags :: (StepDebugger m, SymbolicEvaluator m) => Bool -> Bool -> m ()
initFlags sm dm = do
  setSymbolicMode sm
  setDebugMode dm
    
evalWithVerification :: Bool -- ^ auto-close connection
                     -> CAS -> Maybe FilePath -> Maybe String -> Bool -> Bool
                     -> PC.DTime -> Int -> String -> String -> IO CASState
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




-- | Returns sorted assignment store and program without EP elimination
assStoreAndProgSimple :: [Named CMD] -> IO ([(ConstantName, AssDefinition)], [Named CMD])
assStoreAndProgSimple ncl = do
  let (asss, prog) = splitAS ncl
      gm = fmap analyzeGuarded asss
      sgl = dependencySortAS gm
  return (getSimpleAS sgl, prog)


verifyProg :: (MessagePrinter m, StepDebugger m, VCGenerator m, MonadIO m, MonadError ASError m) =>
              [Named CMD] -> m (Maybe ASError)
verifyProg ncl = do
  stepwiseSafe verifyingStepper $ Sequence $ map sentence ncl

testWithMapleGen :: Int -> PC.DTime -> MapleIO b -> ([Named CMD] -> MapleIO a) -> String -> String
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
