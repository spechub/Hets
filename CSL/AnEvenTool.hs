{-# LANGUAGE TypeSynonymInstances, FlexibleContexts,
             FlexibleInstances, MultiParamTypeClasses #-}
{- |
Module      :  ./CSL/AnEvenTool.hs
Description :  The AnEven-Tool: an (An)alyzer and (Ev)aluator for (En)CL
               specifications
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (uses type-expression in type contexts)

The AnEven-Tool: an (An)alyzer and (Ev)aluator for (En)CL specifications.
Provides functionality for interactive experimenting with EnCL specifications.

Usage: Load this module with 'make ghci' in order to run the commands
-}

{- TODO:

 * complete the pretty printing stuff
   - add visualization functions and bind them to commands
 * implement the cmpenv creation
   - get the corresponding data from the signature
   - implement the global settings for logfiles etc...
 * implement the output of the elim-const to eprange mapping

-}

{-
REMARK:
I removed a complicated autoload program logic.
To see the autoload version see this module-version 15007.

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
import CSL.EPRelation
import qualified CSL.SMTComparison as CMP

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

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List

import Data.IORef

import System.IO
import System.Directory
import System.FilePath

import Text.Regex

-- Shell handling/building imports
import System.Console.Readline

import System.Console.Shell
import qualified System.Console.Shell.Backend as ShBE
import System.Console.Shell.ShellMonad

{- PROBLEMS with Shellac:

   1. When using the readline-backend and load this module in a "make ghci"
   session, there is a segfault after invoking runShell. When running a compiled
   program then this does not happen anymore!

   2. With all backends, when explicitly calling initBackend then there are
   segfaults after exiting from the REPL or even during completion...


-}

-- import System.Console.Shell.Backend.Readline
import System.Console.Shell.Backend.Haskeline
{- FIXME: It seems this module is sometimes (in newer versions?) located
          in System.Console.Haskeline -}

-- ----------------------------------------------------------------------

instance Pretty Bool where
    pretty = text . show


data CAS = Maple | Mathematica deriving (Show, Read, Eq)

data CASState = MapleState MITrans | MathematicaState MathState

{- ----------------------------------------------------------------------
AnEven-Tool
---------------------------------------------------------------------- -}

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

{- ----------------------------------------------------------------------
Utils for Completion
---------------------------------------------------------------------- -}


{-
  Given a relation ~ represented by M through
  a ~ b <=> b elem (lookup a in M)
  we compute the strict set of elements S transitively related to a, i.e.,
  S is the smallest set satisfying:
  b elem S <=> a /= b /\ (a ~ b \/ (EX a' elem S. a' ~ b))
-}
terminalSeg :: Ord a => Map.Map a [a] -- the relation
            -> a             -- the element
            -> Set.Set a     -- the terminalSegment of the element
terminalSeg rel el = snd $ terminalSegEx rel (Set.singleton el) el

terminalSegEx :: Ord a => Map.Map a [a] -- the relation
          -> Set.Set a         -- the cache
          -> a                 -- the element
          -> ( Set.Set a       -- the updated cache
             , Set.Set a       -- the terminalSegment of the element
             )
terminalSegEx rel cache el =
    case Map.lookup el rel of
      Nothing -> (cache, Set.empty)
      Just l ->
          let l' = filter (`Set.notMember` cache) l
              cache' = foldr Set.insert cache l'
              (cache'', iss) = mapAccumL (terminalSegEx rel) cache' l'
          in (cache'', Set.unions $ Set.fromList l' : iss)

predecessorsOf :: Ord a => Map.Map a [a] -- the relation
            -> a       -- the element
            -> [a]     -- the predecessors
predecessorsOf rel el = Map.keys $ Map.filter (elem el) rel


matchCands :: [String] -> String -> [String]
matchCands l str = filter (isPrefixOf str) l

-- spec extraction from source files
specNameRE :: Regex
specNameRE = mkRegex "^\\s*spec\\W+(\\w+)"

getSpecNames :: String -> [String]
getSpecNames txt = sort $ concat $ mapMaybe (matchRegex specNameRE) $ lines txt

getSpecNamesFromFile :: Maybe FilePath -> IO [String]
getSpecNamesFromFile Nothing = return []
getSpecNamesFromFile (Just fp) = do
  fe <- doesFileExist fp
  if fe then Control.Monad.liftM getSpecNames (readFile fp) else return []


-- use this history file
historyFilePath :: IO FilePath
historyFilePath = do
  tmp <- getTemporaryDirectory
  return $ joinPath [tmp, "AnEvenHistory.txt"]

{- ----------------------------------------------------------------------
Shell abstraction
---------------------------------------------------------------------- -}

type BackendState = ShellacState
-- type BackendState = ()

defaultBackend :: ShBE.ShellBackend BackendState
defaultBackend = haskelineBackend
-- defaultBackend = readlineBackend


{- ----------------------------------------------------------------------
Pretty Printing for AnEvenState fields
---------------------------------------------------------------------- -}

class PrettyOutput a b where
    showPretty :: a -> b -> Doc

data POdefault = POdefault

instance PrettyOutput POdefault (SigSens a b) where
    showPretty _ = pretty . sigsensLibname

instance PrettyOutput POdefault [Named CMD] where
    showPretty _ = pretty

instance PrettyOutput POdefault [(String, Guarded EPRange)] where
    showPretty _ = pretty

instance PrettyOutput POdefault (GuardedMap EPRange) where
    showPretty _ = pretty


{- TODO: implement it for the other types...
    , stDS :: Maybe (GuardedMap EPRange) -- the current dependency store
                                         -- (derived from spec)

    -- the ordered version of the current dependency store
    , stODS :: Maybe [(String, Guarded EPRange)]

    -- the guarded version of the current dependency store
    , stGDS :: Maybe [(String, Guarded EPRange)]
    -- the flattened version of the guarded dependency store
    , stFDS :: Maybe [(ConstantName, AssDefinition)]
    -- the elim constant to eprange mapping
    , stECRgMap :: Maybe (Map.Map ConstantName EPRange)

    -- the environment for the range-comparer facility
    , stCmpEnv :: Maybe CMP.VarEnv
-}

visualize :: PrettyOutput POdefault a => a -> Sh AnEvenState ()
visualize x = shellPutStrLn $ show $ showPretty POdefault x

{- ----------------------------------------------------------------------
Basic Datatypes
---------------------------------------------------------------------- -}

data AnEvenConfig = AnEvenConfig

defaultConfig :: AnEvenConfig
defaultConfig = AnEvenConfig

{- AnEventState

-}

data AnEvenState =
    AnEvenState
    { stSpec :: Maybe (SigSens Sign CMD) -- current hets environment
    , stProg :: Maybe [Named CMD] -- the current program (derived from spec)
    , stDS :: Maybe (GuardedMap EPRange) {- the current dependency store
                                         (derived from spec) -}

    -- the ordered version of the current dependency store
    , stODS :: Maybe [(String, Guarded EPRange)]

    -- the guarded version of the current dependency store
    , stGDS :: Maybe [(String, Guarded EPRange)]
    -- the flattened version of the guarded dependency store
    , stFDS :: Maybe [(ConstantName, AssDefinition)]
    -- the elim constant to eprange mapping
    , stECRgMap :: Maybe (Map.Map ConstantName EPRange)

    -- the environment for the range-comparer facility
    , stCmpEnv :: Maybe CMP.VarEnv


    , stConfig :: AnEvenConfig -- the global settings
    , stCompletionState :: IORef (Maybe FilePath) -- see completion-logic
    }


initialState :: IO AnEvenState
initialState = do
  csinit <- newIORef Nothing
  return AnEvenState
    { stSpec = Nothing
    , stProg = Nothing
    , stDS = Nothing
    , stODS = Nothing
    , stGDS = Nothing
    , stFDS = Nothing
    , stECRgMap = Nothing
    , stCmpEnv = Nothing

    , stConfig = defaultConfig
    , stCompletionState = csinit
    }


-- accessor functions
getStGeneric :: (AnEvenState -> Maybe a) -- the accessor function
             -> String -- the error message
             -> Sh AnEvenState a

getStGeneric f msg = do
  st <- getShellSt
  case f st of
    Just a -> return a
    Nothing -> error msg

getStSpec :: Sh AnEvenState (SigSens Sign CMD)
getStSpec = getStGeneric stSpec "Any specification loaded."

getStProg :: Sh AnEvenState [Named CMD]
getStProg = getStGeneric stProg "Program not initialized."

getStDepStore :: Sh AnEvenState (GuardedMap EPRange)
getStDepStore = getStGeneric stDS "Dependency Store not initialized."

getStODS :: Sh AnEvenState [(String, Guarded EPRange)]
getStODS = getStGeneric stODS "Ordered Dependency Store not initialized."

getStGDS :: Sh AnEvenState [(String, Guarded EPRange)]
getStGDS = getStGeneric stGDS "Guarded Dependency Store not initialized."

getStFDS :: Sh AnEvenState [(ConstantName, AssDefinition)]
getStFDS = getStGeneric stFDS "Flattened Dependency Store not initialized."

getStECRgMap :: Sh AnEvenState (Map.Map ConstantName EPRange)
getStECRgMap = getStGeneric stECRgMap
                "Elim constant to eprange mapping not initialized."

getStCmpEnv :: Sh AnEvenState CMP.VarEnv
getStCmpEnv = getStGeneric stCmpEnv "Comparer environment not initialized."


-- update functions
updStAS :: GuardedMap EPRange -> [Named CMD] -> Sh AnEvenState ()
updStAS gm l =
    let f st = st { stProg = Just l, stDS = Just gm } in modifyShellSt f

updStSpec :: SigSens Sign CMD -> Sh AnEvenState ()
updStSpec sp = let f st = st { stSpec = Just sp } in modifyShellSt f

updStODS :: [(String, Guarded EPRange)] -> Sh AnEvenState ()
updStODS ods = let f st = st { stODS = Just ods } in modifyShellSt f

updStGDS :: [(String, Guarded EPRange)] -> Sh AnEvenState ()
updStGDS gds = let f st = st { stGDS = Just gds } in modifyShellSt f

updStFDS :: [(ConstantName, AssDefinition)] -> Sh AnEvenState ()
updStFDS fds = let f st = st { stFDS = Just fds } in modifyShellSt f

updStECRgMap :: Map.Map ConstantName EPRange -> Sh AnEvenState ()
updStECRgMap m = let f st = st { stECRgMap = Just m } in modifyShellSt f

updStCmpEnv :: CMP.VarEnv -> Sh AnEvenState ()
updStCmpEnv ve = let f st = st { stCmpEnv = Just ve } in modifyShellSt f


{- completion-logic:

  due to shortcomings of the Shellac interface concerning completion
  (no context-sensitive completion possible!), we implement the following
  completion logic using the AnEvenState:

  * When a filename argument is completed we remember the completion in the
    state-field stCompletionState.

  * When a command using filename arguments is executed we clear the
    stCompletionState field

  * In the specname completion function we use the stCompletionState field to
    read eventually the specfile and extract the possible specnames

-}

-- see completion-logic
setComplFilepath :: AnEvenState -> Maybe FilePath -> IO ()
setComplFilepath st mFp =
    atomicModifyIORef (stCompletionState st) $ const (mFp, ())

getComplFilepath :: AnEvenState -> IO (Maybe FilePath)
getComplFilepath st = readIORef $ stCompletionState st

writeComplState :: Maybe FilePath -> Sh AnEvenState ()
writeComplState mFp = do
  nst <- getShellSt
  liftIO $ setComplFilepath nst mFp

readComplState :: Sh AnEvenState (Maybe FilePath)
readComplState = do
  nst <- getShellSt
  liftIO $ getComplFilepath nst


-- Completable dummytypes and completion instances

-- File completable

data SpecFile = SpecFile
data SpecName = SpecName

instance Completion SpecFile AnEvenState where

{- REMARK (on a Shellac issue):
  There is no way to get the backend state from the backend other than the init
  function, but when we call initBackend explicitly we get segfaults (later in
  the program, not directly...).
  For our purposes it is sufficient to use a dummy backend state because in the
  completeFilename function this value is not touched.
-}
  complete _ st str = do
      -- the backend state is not touched only passed...
      opts <- ShBE.completeFilename defaultBackend (error "117: no bst") str
      unless (null opts) -- see completion-logic
                 $ setComplFilepath st $ Just $ head opts
      return opts

  completableLabel _ = "<fname>"

instance Completion SpecName AnEvenState where
  complete _ st str = do
      mFp <- getComplFilepath st
      l <- getSpecNamesFromFile mFp
      return $ matchCands l str
  completableLabel _ = "<specname>"


{- ----------------------------------------------------------------------
Basic Interface Functions
---------------------------------------------------------------------- -}

{-

1. loads the spec and translates it to signature and sentences
sigsensGen :: String -> String -> IO (SigSens Sign CMD)

2. sentences are split into guarded dependency store and program
splitAS :: [Named CMD] -> (GuardedMap [EXTPARAM], [Named CMD])

3. guarded dependency is analyzed and made disjoint,
 to apply it to a dependency store use 'fmap'
analyzeGuarded :: Guarded [EXTPARAM] -> Guarded EPRange

4. the dependency store is sorted by the dependency relation
dependencySortAS :: GuardedMap EPRange -> [(String, Guarded EPRange)]

5. we apply extended parameter elimination to the dependency store
epElimination :: CompareIO m => [(String, Guarded EPRange)] ->
                 m [(String, Guarded EPRange)]

6. the guarded dependency store is flattened to an ordinary one
getElimAS :: [(String, Guarded EPRange)] -> [(ConstantName, AssDefinition)]

6'. as 6, but this one returns in addition a mapping of elim-constants to ranges
getElimASWithMap :: [(String, Guarded EPRange)] ->
       ([(ConstantName, AssDefinition)], Map.Map ConstantName EPRange)

-}


-- 1.
cmdLoadSpecEnv :: Completable SpecFile -> Completable SpecName ->
                  Sh AnEvenState ()
cmdLoadSpecEnv (Completable lfn) (Completable spn) = do
  sigs <- liftIO $ sigsensGen lfn spn
  updStSpec sigs
  let (gm, prg) = splitAS $ sigsensNamedSentences sigs
  updStAS (fmap analyzeGuarded gm) prg
  writeComplState Nothing -- see completion-logic


-- 4. viz
cmdShowDS :: Sh AnEvenState ()
cmdShowDS = do
  ds <- getStDepStore
  visualize ds

cmdShowProg :: Sh AnEvenState ()
cmdShowProg = do
  p <- getStProg
  visualize p

cmdShowODS :: Sh AnEvenState ()
cmdShowODS = do
  ods <- getStODS
  visualize ods


-- ??.
stateInfo :: Sh AnEvenState ()
stateInfo = do
  st <- getShellSt
  case stSpec st of
    Just (SigSens { sigsensLibname = ln, sigsensNode = nd }) ->
        shellPutInfoLn $ show $ text "Library" <+> pretty ln <>
        text ":" <> pretty nd <+> text "loaded."
    _ -> shellPutInfoLn "System not initialized."
  when (isJust $ stProg st) $ shellPutInfoLn "Program loaded."
  when (isJust $ stDS st) $ shellPutInfoLn "Dependency Store loaded."
  when (isJust $ stODS st) $ shellPutInfoLn "Ordered Dependency Store loaded."
  when (isJust $ stGDS st) $ shellPutInfoLn "Guarded Dependency Store loaded."
  when (isJust $ stFDS st) $ shellPutInfoLn "Flattened Dependency Store loaded."
  when (isJust $ stECRgMap st) $ shellPutInfoLn "Elim-constant Map loaded."
  when (isJust $ stCmpEnv st) $ shellPutInfoLn "Comparer Environment loaded."


debugInfo :: Sh AnEvenState ()
debugInfo = do
  mFp <- readComplState
  case mFp of
    Just fp ->
        do
          shellPutInfoLn $ "Debug: " ++ fp
          fe <- liftIO $ doesFileExist fp
          when fe $
               do
                 cont <- liftIO $ readFile fp
                 shellPutInfoLn ("=========================== CONTENT " ++
                                 "===========================")
                 shellPutInfoLn cont
                 shellPutInfoLn ("====================================" ++
                                 "===========================")
                 shellPutInfoLn $ unlines $ getSpecNames cont
    _ -> shellPutInfoLn "Debug: <EMPTY>"


-- 4.
alSortDS :: Sh AnEvenState ()
alSortDS = do
  ds <- getStDepStore
  updStODS $ dependencySortAS ds

-- 5.
alEPElim :: Sh AnEvenState ()
alEPElim = do
  ods <- getStODS
  gds <- epElimination ods
  updStGDS gds

-- 6.
alElimAS :: Sh AnEvenState ()
alElimAS = do
  gds <- getStGDS
  updStFDS $ getElimAS gds

-- 6'.
alElimASWithMap :: Sh AnEvenState ()
alElimASWithMap = do
  gds <- getStGDS
  let (fds, m) = getElimASWithMap gds
  updStFDS fds
  updStECRgMap m


-- A REPL based on Shellac

runToolREPL :: AnEvenState -> IO AnEvenState
runToolREPL st = do
    hfp <- historyFilePath
    let desc =
            (mkShellDescription cmds evalFun)
            { greetingText = Just (versionInfo ++ shellMessage)
            , commandStyle = OnlyCommands
            , historyFile = Just hfp
            }

    -- execute the shell
    runShell desc defaultBackend st

runTool :: IO AnEvenState
runTool = initialState >>= runToolREPL

evalFun :: String -> Sh AnEvenState ()
evalFun [] = return ()
evalFun s = do
  shellPutInfoLn $ concat ["Unknown command: ", s, "\n\nAvailable commands:\n"]
  shellSpecial $ ShellHelp Nothing

cmds :: [ShellCommand AnEvenState]
cmds =
  [ exitCommand "q"
  , helpCommand "h"

  , cmd "load" cmdLoadSpecEnv ("Loads an EnCL spec from the given file-" ++
                               " and specname")
  , cmd "ods" cmdShowODS "Shows the ordered dependency store"
  , cmd "ds" cmdShowDS "Shows the dependency store"
  , cmd "prog" cmdShowProg "Shows the program"

  , cmd "info" stateInfo "Show information on the current state"
  , cmd "debug" debugInfo "Show debug information"
  ]


-- ------ a Readline REPL
rEPL :: IO ()
rEPL = do
   maybeLine <- readline "% "
   case maybeLine of
    Nothing -> return () -- EOF / control-d
    Just "exit" -> return ()
    Just line -> do
                    addHistory line
                    putStrLn $ "The user input: " ++ show line
                    rEPL

{- ----------------------------------------------------------------------
CompareIO related stuff
---------------------------------------------------------------------- -}

instance CompareIO (Sh AnEvenState) where
    logMessage s = do
      ve <- getStCmpEnv
      case CMP.loghandle ve of
        Just hdl -> liftIO $ hPutStrLn hdl s
        _ -> return ()

    rangeFullCmp r1 r2 = do
            ve <- getStCmpEnv
            let vm = CMP.varmap ve
            liftIO $ CMP.smtCompare ve (boolRange vm r1) $ boolRange vm r2

{- ----------------------------------------------------------------------
The functionality for the EvalSpec-Tool
---------------------------------------------------------------------- -}

-- TODO: replace it with the AnEven functionality when finished.

-- ------------------------- Shortcuts --------------------------

initFlags :: (StepDebugger m, SymbolicEvaluator m) => Bool -> Bool -> m ()
initFlags sm dm = do
  setSymbolicMode sm
  setDebugMode dm

evalWithVerification :: Bool -- ^ auto-close connection
                     -> CAS -> Maybe FilePath -> Maybe String -> Bool -> Bool
                     -> PC.DTime -> Int -> String -> String -> IO CASState
evalWithVerification cl c mFp mN smode dmode to v lb sp =
  let {- exitWhen s = null s || s == "q" ||
         take 4 s == "quit" || take 4 s == "exit"
      program for initialization -}

      p prog = do
         prettyInfo $ text ""
         prettyInfo $ text ("****************** Assignment " ++
                            "store loaded ******************")
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
              (mst, _) <- testWithMathematicaGen v mFp mN
                           (initFlags smode dmode) p lb sp
              when cl $ mathematicaExit mst
              return $ MathematicaState mst


-- | Returns sorted assignment store and program without EP elimination
assStoreAndProgSimple :: [Named CMD] -> IO ([(ConstantName, AssDefinition)],
                         [Named CMD])
assStoreAndProgSimple ncl = do
  let (asss, prog) = splitAS ncl
      gm = fmap analyzeGuarded asss
      sgl = dependencySortAS gm
  return (getSimpleAS sgl, prog)


verifyProg :: (MessagePrinter m, StepDebugger m, VCGenerator m,
               MonadIO m, MonadError ASError m) =>
              [Named CMD] -> m (Maybe ASError)
verifyProg ncl = stepwiseSafe verifyingStepper $ Sequence $ map sentence ncl

testWithMapleGen :: Int -> PC.DTime -> MapleIO b -> ([Named CMD] -> MapleIO a)
                     -> String -> String -> IO (MITrans, a)
testWithMapleGen v to = testWithCASGen rf where
    rf adg =
        runWithMaple adg v to
           [ "EnCLFunctions"
           {- , "intpakX" -- Problems with the min,max functions,
                             they are remapped by this package! -}
           ]


testWithMathematicaGen :: Int -> Maybe FilePath -> Maybe String
                       -> MathematicaIO b -> ([Named CMD] -> MathematicaIO a)
                       -> String -> String -> IO (MathState, a)
testWithMathematicaGen v mFp mN = testWithCASGen rf where
    rf adg =
        runWithMathematica adg v mFp mN
           [ "/home/ewaryst/Hets/CSL/CAS/Mathematica.m" ]


testWithCASGen :: (AssignmentStore as, MonadState (ASState st) as, MonadIO as)
                  => (AssignmentDepGraph () -> as a -> IO (ASState st, a))
                     -> as b -> ([Named CMD] -> as a)
                     -> String -> String -> IO (ASState st, a)
testWithCASGen rf ip f lb sp = do
  ncl <- fmap sigsensNamedSentences $ sigsensGen lb sp
  -- get ordered assignment store and program
  (as, prog) <- assStoreAndProgSimple ncl
  vchdl <- openFile "/tmp/vc.out" WriteMode
  -- build the dependency graph
  let gr = assDepGraphFromDescList (const $ const ()) as
      {- make sure that the assignment store is loaded into maple before
      the execution of f -}
      g x = ip >> loadAS as >> modify (\ mit -> mit {vericondOut = Just vchdl})
       >> f x

  -- start maple and run g
  res <- rf gr $ (withLogFile "/tmp/evalWV.txt" . g) prog
  hClose vchdl
  return res

{- ----------------------------------------------------------------------
Temp tools
---------------------------------------------------------------------- -}

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
