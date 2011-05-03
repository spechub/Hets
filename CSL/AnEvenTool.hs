{-# LANGUAGE TypeSynonymInstances, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
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


{- TODO:

 * implement the output of the elim-const to eprange mapping
 * implement the cmpenv creation
   - get the corresponding data from the signature
   - implement the global settings for logfiles etc...
 * complete the pretty printing stuff
   - add visualization functions and bind them to commands
 * check the autoload/reset facility

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
-- ** Utils
-- ----------------------------------------------------------------------


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
          let l' = filter (flip Set.notMember cache) l
              cache' = foldr Set.insert cache l'
              (cache'', iss) = mapAccumL (terminalSegEx rel) cache' l'
          in (cache'', Set.unions iss)

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
  if fe then readFile fp >>= return . getSpecNames else return []


-- use this history file
historyFilePath :: IO FilePath
historyFilePath = do
  tmp <- getTemporaryDirectory
  return $ joinPath [tmp, "AnEvenHistory.txt"]

-- ----------------------------------------------------------------------
-- ** Shell abstraction
-- ----------------------------------------------------------------------

type BackendState = ShellacState
-- type BackendState = ()

defaultBackend :: ShBE.ShellBackend BackendState
defaultBackend = haskelineBackend
-- defaultBackend = readlineBackend


-- ----------------------------------------------------------------------
-- ** Pretty Printing for AnEvenState fields
-- ----------------------------------------------------------------------

class PrettyOutput a b where
    showPretty :: a -> b -> Doc

data POdefault = POdefault

instance PrettyOutput POdefault (SigSens a b) where
    showPretty _ sigs = pretty $ sigsensLibname sigs

instance PrettyOutput POdefault [Named CMD] where
    showPretty _ prog = pretty prog

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

-- ----------------------------------------------------------------------
-- ** Basic Datatypes
-- ----------------------------------------------------------------------

data AnEvenConfig = AnEvenConfig

defaultConfig :: AnEvenConfig
defaultConfig = AnEvenConfig

{- AnEventState

   We use this state as a cache/store for data which depends of other data.
   In order to clear dependent entries when we update a given value we
   use *update trigger*, which are executed recursively.

-}

{- autoload-logic:

  Each trigger symbol has
   * a corresponding field in the state (see resetSt/checkSt),
   and
   * a function which sets the field value (see triggerFunc)

  If a function depends on some state fields we provide an autoload
  facility which tries to fill unset fields recursively.
  This is only possible if the corresponding function does not take arguments.
  In the latter case we break the autoload process with an error message.
-}

data TriggerSymbol = TrgSpec | TrgProg | TrgDS | TrgODS | TrgFDS | TrgGDS
                   | TrgECRgMap | TrgCmpEnv deriving (Eq, Ord, Show)

triggers :: Map.Map TriggerSymbol [TriggerSymbol]
triggers = Map.fromList
           [ (TrgSpec,  [TrgProg, TrgDS, TrgCmpEnv])
           , (TrgDS,    [TrgODS])
           , (TrgODS,    [TrgGDS])
           , (TrgGDS,    [TrgFDS, TrgECRgMap])
           ]



data AnEvenState = 
    AnEvenState
    { stSpec :: Maybe (SigSens Sign CMD) -- current hets environment
    , stProg :: Maybe [Named CMD] -- the current program (derived from spec)
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


    , stConfig :: AnEvenConfig -- the global settings
    , stCompletionState :: IORef (Maybe FilePath) -- see completion-logic
    }



initialState :: IO AnEvenState
initialState = do
  csinit <- newIORef Nothing
  return $
    AnEvenState
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
getStECRgMap = getStGeneric stECRgMap "Elim constant to eprange mapping not initialized."

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


-- reset functions, when partially applied to a TriggerSymbol can be passed to
-- modifyShellSt
resetSt :: TriggerSymbol -> AnEvenState -> AnEvenState
resetSt trg st =
    case trg of
      TrgSpec     -> st { stSpec = Nothing }
      TrgProg     -> st { stProg = Nothing }
      TrgDS       -> st { stDS   = Nothing }
      TrgODS      -> st { stODS  = Nothing }
      TrgGDS      -> st { stGDS  = Nothing }
      TrgFDS      -> st { stFDS  = Nothing }
      TrgECRgMap  -> st { stECRgMap  = Nothing }
      TrgCmpEnv   -> st { stCmpEnv  = Nothing }


-- triggers recursively all resets for the given symbol
runResetTrigger :: [TriggerSymbol] -> Sh AnEvenState ()
runResetTrigger trgs =
    let trgSet = Set.unions $ map (terminalSeg triggers) trgs
        f st = Set.fold resetSt st trgSet
    in modifyShellSt f

-- checks whether the corresponding field is set (Just-val) or unset (Nothing)
checkSt :: TriggerSymbol -> AnEvenState -> Bool
checkSt trg st =
    case trg of
      TrgSpec    -> isJust $ stSpec st
      TrgProg    -> isJust $ stProg st
      TrgDS      -> isJust $ stDS st
      TrgODS     -> isJust $ stODS st
      TrgGDS     -> isJust $ stGDS st
      TrgFDS     -> isJust $ stFDS st
      TrgECRgMap -> isJust $ stECRgMap st
      TrgCmpEnv  -> isJust $ stCmpEnv st


triggerFunc :: TriggerSymbol -> Sh AnEvenState ()
triggerFunc trg =
    case trg of
      TrgSpec     -> noTriggerFunc trg "load"
      TrgProg     -> alExtractFromSpec
      TrgDS       -> alExtractFromSpec
      TrgCmpEnv   -> alExtractFromSpec
      TrgODS      -> alSortDS
      TrgGDS      -> alEPElim
      TrgFDS      -> alElimAS
      TrgECRgMap  -> alElimASWithMap


noTriggerFunc :: TriggerSymbol -> String -> a
noTriggerFunc trg s =
    error $ concat [ "Cannot autoload for trigger ", show trg
                   , "\nPlease use the ", s, "-command for this purpose" ]

autoloads :: [TriggerSymbol] -> Sh AnEvenState ()
autoloads trgs = mapM_ autoload trgs

autoload :: TriggerSymbol -> Sh AnEvenState ()
autoload trg = do
  let isFieldSet = fmap (checkSt trg) getShellSt
  b <- isFieldSet
  unless b $ do
    mapM_ autoload $ predecessorsOf triggers trg
    b' <- isFieldSet
    unless b' $ triggerFunc trg
    

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
    atomicModifyIORef (stCompletionState st) $ \ _ -> (mFp, ())

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


-- ----------------------------------------------------------------------
-- ** Basic Interface Functions
-- ----------------------------------------------------------------------

{- Most of this functions are autoload functions required for some visualization output

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
getElimASWithMap :: [(String, Guarded EPRange)] -> ([(ConstantName, AssDefinition)], Map.Map ConstantName EPRange)

-}



-- 1. 
cmdLoadSpecEnv :: Completable SpecFile -> Completable SpecName -> Sh AnEvenState ()
cmdLoadSpecEnv (Completable lfn) (Completable spn) = do
  sigs <- liftIO $ sigsensGen lfn spn
  updStSpec sigs
  runResetTrigger [TrgSpec]
  writeComplState Nothing -- see completion-logic






-- ??. 
stateInfo :: Sh AnEvenState ()
stateInfo = do
  st <- getShellSt
  case stSpec st of
    Just (SigSens { sigsensLibname = ln, sigsensNode = nd }) ->
        shellPutInfoLn $ show $ text "Library" <+> pretty ln <> text ":" <> pretty nd  <+> text "loaded."
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
                 shellPutInfoLn "=========================== CONTENT ==========================="
                 shellPutInfoLn cont
                 shellPutInfoLn "==============================================================="
                 shellPutInfoLn $ unlines $ getSpecNames cont
    _ -> shellPutInfoLn "Debug: <EMPTY>"




-- ** Autoloadable functions
-- 2., 3.
alExtractFromSpec :: Sh AnEvenState ()
alExtractFromSpec = do
  autoload TrgSpec
  sigs <- getStSpec
  let (gm, prg) = splitAS $ sigsensNamedSentences sigs
  updStAS (fmap analyzeGuarded gm) prg
  runResetTrigger [TrgDS, TrgProg]

-- 4.
alSortDS :: Sh AnEvenState ()
alSortDS = do
  autoload TrgDS
  ds <- getStDepStore
  updStODS $ dependencySortAS ds
  runResetTrigger [TrgODS]

-- 5.
alEPElim :: Sh AnEvenState ()
alEPElim = do
  autoloads [TrgODS, TrgCmpEnv]
  ods <- getStODS
  gds <- epElimination ods
  updStGDS gds
  runResetTrigger [TrgGDS]
  
-- 6.
alElimAS :: Sh AnEvenState ()
alElimAS = do
  autoload TrgGDS
  gds <- getStGDS
  updStFDS $ getElimAS gds
  runResetTrigger [TrgFDS]

-- 6'.
alElimASWithMap :: Sh AnEvenState ()
alElimASWithMap = do
  autoload TrgGDS
  gds <- getStGDS
  let (fds, m) = getElimASWithMap gds
  updStFDS fds
  updStECRgMap m
  runResetTrigger [TrgFDS, TrgECRgMap]



-- A REPL based on Shellac

runToolREPL :: AnEvenState -> IO AnEvenState
runToolREPL st = do
    hfp <- historyFilePath
    let desc =
            (mkShellDescription cmds evalFun)
            { greetingText       = Just (versionInfo ++ shellMessage)
            , commandStyle       = OnlyCommands
            , historyFile        = Just hfp
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

  , cmd "load"       cmdLoadSpecEnv    "Loads an EnCL spec from the given file- and specname"

  , cmd "info"       stateInfo      "Show information on the current state"
  , cmd "debug"      debugInfo      "Show debug information"
  ]



-------- a Readline REPL 
rEPL :: IO ()
rEPL = do
   maybeLine <- readline "% "
   case maybeLine of 
    Nothing     -> return () -- EOF / control-d
    Just "exit" -> return ()
    Just line -> do addHistory line
                    putStrLn $ "The user input: " ++ (show line)
                    rEPL

-- ----------------------------------------------------------------------
-- ** CompareIO related stuff
-- ----------------------------------------------------------------------

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
