{- |
Module      :  $Header$
Description :  Datatypes and functions for options that hets understands.
Copyright   :  (c) Martin Kuehl, Christian Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Datatypes for options that hets understands.
   Useful functions to parse and check user-provided values.
-}

module Driver.Options
  ( HetcatsOpts (..)
  , AnaType (..)
  , GuiType (..)
  , InType (..)
  , OutType (..)
  , PrettyType (..)
  , GraphType (..)
  , SPFType (..)
  , ATType
  , Delta
  , hetcatsOpts
  , guess
  , rmSuffix
  , envSuffix
  , prfSuffix
  , removePrfOut
  , hasEnvOut
  , hasPrfOut
  , existsAnSource
  , checkRecentEnv
  , downloadExtensions
  , pathAndBase
  , defaultHetcatsOpts
  , hetsVersion
  , showDiags
  , showDiags1
  , putIfVerbose
  , doDump
  , checkUri
  ) where

import Driver.Version
import Common.Utils
import Common.Id
import Common.Result
import Common.ResultT
import Common.Amalgamate

import System.Directory
import System.Console.GetOpt
import System.IO.Error
import System.Exit

import Control.Monad.Trans
import Data.List

-- | short version without date for ATC files
hetsVersion :: String
hetsVersion = takeWhile (/= ',') hetcats_version

bracket :: String -> String
bracket s = "[" ++ s ++ "]"

-- use the same strings for parsing and printing!
verboseS, intypeS, outtypesS, skipS, structS, transS,
     guiS, libdirS, outdirS, amalgS, specS, recursiveS,
     interactiveS, modelSparQS, connectS, xmlS, listenS, normalFormS :: String

modelSparQS = "modelSparQ"
verboseS = "verbose"
intypeS = "input-type"
outtypesS = "output-types"
skipS = "just-parse"
structS = "just-structured"
guiS = "gui"
libdirS = "hets-libdir"
outdirS = "output-dir"
amalgS = "casl-amalg"
specS = "named-specs"
transS = "translation"
recursiveS = "recursive"
interactiveS = "interactive"
connectS = "connect"
xmlS = "xml"
listenS = "listen"
normalFormS = "normal-form"

genTermS, treeS, bafS :: String
genTermS = "gen_trm"
treeS = "tree."
bafS = ".baf"

graphS, ppS, envS, deltaS, prfS, owlS, omdocS, hsS, experimentalS :: String
graphS = "graph."
ppS = "pp."
envS = "env"
deltaS = ".delta"
prfS = "prf"
owlS = "owl"
omdocS = "omdoc"
hsS = "hs"
experimentalS = "exp"

tptpS, dfgS, cS :: String
tptpS = "tptp"
dfgS = "dfg"
cS = ".c"

showOpt :: String -> String
showOpt s = if null s then "" else " --" ++ s

showEqOpt :: String -> String -> String
showEqOpt k s = if null s then "" else showOpt k ++ "=" ++ s

-- main Datatypes --

-- | 'HetcatsOpts' is a record of all options received from the command line
data HetcatsOpts = HcOpt     -- for comments see usage info
  { analysis :: AnaType
  , guiType :: GuiType
  , infiles :: [FilePath] -- ^ files to be read
  , specNames :: [SIMPLE_ID] -- ^ specs to be processed
  , transNames :: [SIMPLE_ID] -- ^ comorphism to be processed
  , intype :: InType
  , libdir :: FilePath
  , modelSparQ :: FilePath
  , outdir :: FilePath
  , outtypes :: [OutType]
  , recurse :: Bool
  , verbose :: Int
  , defLogic :: String
  , outputToStdout :: Bool    -- ^ send messages to stdout?
  , caslAmalg :: [CASLAmalgOpt]
  , interactive :: Bool
  , connectP :: Int
  , connectH :: String
  , uncolored :: Bool
  , xmlFlag :: Bool
  , computeNormalForm :: Bool
  , dumpOpts :: [String]
  , listen :: Int }

-- | 'defaultHetcatsOpts' defines the default HetcatsOpts, which are used as
-- basic values when the user specifies nothing else
defaultHetcatsOpts :: HetcatsOpts
defaultHetcatsOpts = HcOpt
  { analysis = Basic
  , guiType = NoGui
  , infiles  = []
  , specNames = []
  , transNames = []
  , intype   = GuessIn
  , libdir   = ""
  , modelSparQ = ""
  , outdir   = ""
  , outtypes = [] -- no default
  , recurse  = False
  , defLogic = "CASL"
  , verbose  = 1
  , outputToStdout = True
  , caslAmalg = [Cell]
  , interactive = False
  , connectP = -1
  , connectH = ""
  , uncolored = False
  , xmlFlag = False
  , computeNormalForm = False
  , dumpOpts = []
  , listen   = -1 }

instance Show HetcatsOpts where
  show opts = showEqOpt verboseS (show $ verbose opts)
    ++ show (guiType opts)
    ++ (if interactive opts then showOpt interactiveS else "")
    ++ show (analysis opts)
    ++ showEqOpt libdirS (libdir opts)
    ++ (if modelSparQ opts /= "" then showEqOpt modelSparQS (modelSparQ opts)
        else "")
    ++ (if xmlFlag opts then showOpt xmlS else "")
    ++ (if connectP opts /= -1 then showOpt connectS else "")
    ++ (if listen opts /= -1 then showOpt listenS else "")
    ++ showEqOpt intypeS (show $ intype opts)
    ++ showEqOpt outdirS (outdir opts)
    ++ showEqOpt outtypesS (intercalate "," $ map show $ outtypes opts)
    ++ (if recurse opts then showOpt recursiveS else "")
    ++ (if computeNormalForm opts then showOpt normalFormS else "")
    ++ showEqOpt specS (intercalate "," $ map show $ specNames opts)
    ++ showEqOpt transS (intercalate ":" $ map show $ transNames opts)
    ++ showEqOpt amalgS (tail $ init $ show $
                                      case caslAmalg opts of
                                      [] -> [NoAnalysis]
                                      l -> l)
    ++ " " ++ intercalate " " (infiles opts)

-- | every 'Flag' describes an option (see usage info)
data Flag =
    Verbose Int
  | Quiet
  | Uncolored
  | Version
  | Recurse
  | NormalForm
  | Help
  | Gui GuiType
  | Analysis AnaType
  | DefaultLogic String
  | InType InType
  | LibDir FilePath
  | OutDir FilePath
  | ModelSparQ FilePath
  | OutTypes [OutType]
  | Specs [SIMPLE_ID]
  | Trans [SIMPLE_ID]
  | CASLAmalg [CASLAmalgOpt]
  | Interactive
  | Connect Int String
  | XML
  | Dump String
  | Listen Int

-- | 'makeOpts' includes a parsed Flag in a set of HetcatsOpts
makeOpts :: HetcatsOpts -> Flag -> HetcatsOpts
makeOpts opts flg = case flg of
    Interactive -> opts { interactive = True }
    XML         -> opts { xmlFlag = True }
    Listen x    -> opts { listen = x }
    Connect x y -> opts { connectP = x, connectH = y }
    Analysis x -> opts { analysis = x }
    Gui x      -> opts { guiType = x }
    InType x   -> opts { intype = x }
    LibDir x   -> opts { libdir = x }
    ModelSparQ x -> opts { modelSparQ = x }
    OutDir x   -> opts { outdir = x }
    OutTypes x -> opts { outtypes = x }
    Recurse    -> opts { recurse = True }
    NormalForm -> opts { computeNormalForm = True }
    Specs x    -> opts { specNames = x }
    Trans x    -> opts { transNames = x }
    Verbose x  -> opts { verbose = x }
    DefaultLogic x -> opts { defLogic = x }
    CASLAmalg x   -> opts { caslAmalg = x }
    Quiet         -> opts { verbose = 0 }
    Uncolored     -> opts { uncolored = True }
    Dump s        -> opts { dumpOpts = s : dumpOpts opts }
    Help          -> opts -- skipped
    Version       -> opts -- skipped

-- | 'AnaType' describes the type of analysis to be performed
data AnaType = Basic | Structured | Skip

instance Show AnaType where
  show a = case a of
    Basic -> ""
    Structured -> showOpt structS
    Skip -> showOpt skipS

-- | 'GuiType' determines if we want the GUI shown
data GuiType = UseGui | NoGui

instance Show GuiType where
  show g = case g of
    UseGui -> showOpt guiS
    NoGui  -> ""

-- | 'InType' describes the type of input the infile contains
data InType =
    ATermIn ATType
  | CASLIn
  | HetCASLIn
  | OWLIn
  | HaskellIn
  | PrfIn
  | OmdocIn
  | ProofCommand
  | GuessIn

instance Show InType where
  show i = case i of
    ATermIn at -> genTermS ++ show at
    CASLIn -> "casl"
    HetCASLIn -> "het"
    OWLIn -> owlS
    HaskellIn -> hsS
    PrfIn -> prfS
    OmdocIn -> omdocS
    ProofCommand -> "hpf"
    GuessIn -> ""

-- maybe this optional tree prefix can be omitted
instance Read InType where
    readsPrec _ = readShowAux $ map ( \ i -> (show i, i))
                  (plainInTypes ++ aInTypes)
                  ++ [(treeS ++ genTermS ++ show at, ATermIn at)
                           | at <- [BAF, NonBAF]]

-- | 'ATType' describes distinct types of ATerms
data ATType = BAF | NonBAF

instance Show ATType where
  show a = case a of
    BAF -> bafS
    NonBAF -> ""

plainInTypes :: [InType]
plainInTypes =
    [CASLIn, HetCASLIn, OWLIn, HaskellIn, PrfIn, OmdocIn, ProofCommand]

aInTypes :: [InType]
aInTypes = [ ATermIn x | x <- [BAF, NonBAF] ]

data SPFType = ConsistencyCheck | ProveTheory

instance Show SPFType where
  show x = case x of
    ConsistencyCheck -> cS
    ProveTheory  -> ""

spfTypes :: [SPFType]
spfTypes = [ConsistencyCheck, ProveTheory]

-- | 'OutType' describes the type of outputs that we want to generate
data OutType =
    PrettyOut PrettyType
  | GraphOut GraphType
  | Prf
  | EnvOut
  | OWLOut
  | OmdocOut
  | ExperimentalOut -- ^ for testing new functionality
  | HaskellOut
  | ThyFile -- ^ isabelle theory file
  | DfgFile SPFType -- ^ SPASS input file
  | TPTPFile SPFType
  | ComptableXml
  | SigFile Delta -- ^ signature as text
  | TheoryFile Delta -- ^ signature with sentences as text

instance Show OutType where
  show o = case o of
    PrettyOut p -> ppS ++ show p
    GraphOut f -> graphS ++ show f
    Prf -> prfS
    EnvOut -> envS
    OWLOut -> owlS
    OmdocOut -> omdocS
    ExperimentalOut -> experimentalS
    HaskellOut -> hsS
    ThyFile -> "thy"
    DfgFile t -> dfgS ++ show t
    TPTPFile t -> tptpS ++ show t
    ComptableXml -> "comptable.xml"
    SigFile d -> "sig" ++ show d
    TheoryFile d -> "th" ++ show d

plainOutTypeList :: [OutType]
plainOutTypeList =
  [Prf, EnvOut, OWLOut, OmdocOut, ExperimentalOut,
      HaskellOut, ThyFile, ComptableXml]

outTypeList :: [OutType]
outTypeList = let dl = [Delta, Fully] in
    plainOutTypeList
    ++ [ PrettyOut p | p <- prettyList ]
    ++ [ SigFile d | d <- dl ]
    ++ [ TheoryFile d | d <- dl ]
    ++ [ DfgFile x | x <- spfTypes]
    ++ [ TPTPFile x | x <- spfTypes]
    ++ [ GraphOut f | f <- graphList ]

instance Read OutType where
    readsPrec  _ = readShowAux $ map ( \ o -> (show o, o)) outTypeList

data Delta = Delta | Fully

instance Show Delta where
  show d = case d of
    Delta -> deltaS
    Fully -> ""

-- | 'PrettyType' describes the type of output we want the pretty-printer
-- to generate
data PrettyType = PrettyAscii | PrettyLatex | PrettyXml

instance Show PrettyType where
  show p = case p of
    PrettyAscii -> "het"
    PrettyLatex -> "tex"
    PrettyXml -> "xml"

prettyList :: [PrettyType]
prettyList = [PrettyAscii, PrettyLatex, PrettyXml]

-- | 'GraphType' describes the type of Graph that we want generated
data GraphType =
    Dot Bool -- ^ True means show internal node labels

instance Show GraphType where
  show g = case g of
    Dot si -> (if si then "exp." else "") ++ "dot"

graphList :: [GraphType]
graphList = [Dot True, Dot False]

-- | 'options' describes all available options and is used to generate usage
-- information
options :: [OptDescr Flag]
options = let
    listS = "is a comma-separated list without blanks"
       ++ crS ++ "of one or more from:"
    crS = "\n  "
    bS = "| "
    joinBar l = "(" ++ intercalate "|" l ++ ")" in
    [ Option ['v'] [verboseS] (OptArg parseVerbosity "0-5")
      "verbosity, default is -v1"
    , Option ['q'] ["quiet"] (NoArg Quiet)
      "same as -v0, no output to stdout"
    , Option ['V'] ["version"] (NoArg Version)
      "print version number and exit"
    , Option ['h'] ["help", "usage"] (NoArg Help)
      "print usage information and exit"
    , Option ['g'] [guiS] (NoArg (Gui UseGui))
      "show graphs in windows"
    , Option ['u'] ["uncolored"] (NoArg Uncolored)
      "no colors in shown graphs"
    , Option ['I'] [interactiveS] (NoArg Interactive)
      "run in interactive mode"
    , Option ['p'] [skipS] (NoArg $ Analysis Skip)
      "skip static analysis, only parse"
    , Option ['s'] [structS] (NoArg $ Analysis Structured)
      "skip basic, just do structured analysis"
    , Option ['l'] ["logic"] (ReqArg DefaultLogic "LOGIC")
      "choose logic, default is CASL"
    , Option ['L'] [libdirS] (ReqArg LibDir "DIR")
      "source directory of libraries"
    , Option ['m'] [modelSparQS] (ReqArg ModelSparQ "FILE")
      "lisp file for SparQ definitions"
    , Option ['x'] [xmlS] (NoArg XML)
       "use xml packets to communicate"
    , Option ['c'] [connectS] (ReqArg parseConnect "HOSTNAME:PORT")
      "run interface comunicating via connecting to the port"
    , Option ['S'] [listenS] (ReqArg parseListen "PORT")
      "run interface by listening to the port"
    , Option ['i'] [intypeS] (ReqArg parseInType "ITYPE")
      ("input file type can be one of:" ++ crS ++ joinBar
       (map show plainInTypes ++
        map (++ bracket bafS) [bracket treeS ++ genTermS]))
    , Option ['d'] ["dump"] (ReqArg Dump "STRING")
      "dump various strings"
    , Option ['O'] [outdirS] (ReqArg OutDir "DIR")
      "destination directory for output files"
    , Option ['o'] [outtypesS] (ReqArg parseOutTypes "OTYPES")
      ("output file types, default nothing," ++ crS ++
       listS ++ crS ++ concatMap ( \ t -> bS ++ show t ++ crS)
             plainOutTypeList
       ++ bS ++ joinBar (map show [SigFile Fully,
                                   TheoryFile Fully])
              ++ bracket deltaS ++ crS
       ++ bS ++ ppS ++ joinBar (map show prettyList) ++ crS
       ++ bS ++ graphS ++ joinBar (map show graphList) ++ crS
       ++ bS ++ dfgS ++ bracket cS ++ crS
       ++ bS ++ tptpS ++ bracket cS)
    , Option ['R'] [recursiveS] (NoArg Recurse)
      "output also imported libraries"
    , Option ['N'] [normalFormS] (NoArg NormalForm)
      "compute normal forms (takes long)"
    , Option ['n'] [specS] (ReqArg parseSpecOpts "NSPECS")
      ("process specs option " ++ crS ++ listS ++ " SIMPLE-ID")
    , Option ['t'] [transS] (ReqArg parseTransOpt "TRANS")
      ("translation option " ++ crS ++
          "is a colon-separated list without blank" ++
          crS ++ "of one or more from: SIMPLE-ID")
    , Option ['a'] [amalgS] (ReqArg parseCASLAmalg "ANALYSIS")
      ("CASL amalgamability analysis options" ++ crS ++ listS ++
       crS ++ joinBar (map show caslAmalgOpts)) ]

-- parser functions returning Flags --

-- | 'parseVerbosity' parses a 'Verbose' Flag from user input
parseVerbosity :: (Maybe String) -> Flag
parseVerbosity ms = case ms of
    Nothing -> Verbose 2
    Just s -> case reads s of
      [(i, "")] -> Verbose i
      _  -> hetsError (s ++ " is not a valid INT")

divideIntoPortHost :: String -> Bool -> (String, String) -> (String, String)
divideIntoPortHost s sw (accP,accH)
 = case s of
    ':':ll -> divideIntoPortHost ll True (accP,accH)
    c:ll -> case sw of
             False -> divideIntoPortHost ll False (c:accP,accH)
             True -> divideIntoPortHost ll True (accP,c:accH)
    [] -> (accP,accH)

-- | 'parseConnect' parses a port Flag from user input
parseConnect :: String -> Flag
parseConnect s
 = let (sP,sH) = divideIntoPortHost s False ([],[])
   in case reads sP of
                [(i,"")] -> Connect i sH
                _        -> Connect (-1) sH

parseListen :: String -> Flag
parseListen s
 = case reads s of
                [(i,"")] -> Listen i
                _        -> Listen (-1)

-- | intypes useable for downloads
downloadExtensions :: [String]
downloadExtensions = map ('.' :) $
    map show plainInTypes
    ++ map ((treeS ++) . show) [ATermIn BAF, ATermIn NonBAF]
    ++ map show aInTypes

-- | remove the extension from a file
rmSuffix :: FilePath -> FilePath
rmSuffix = fst . stripSuffix (envSuffix : downloadExtensions)

-- | the suffix of env files
envSuffix :: String
envSuffix = '.' : envS

-- | the suffix of env files
prfSuffix :: String
prfSuffix = '.' : prfS

-- |
-- checks if a source file for the given file name exists
existsAnSource :: HetcatsOpts -> FilePath -> IO (Maybe FilePath)
existsAnSource opts file = do
       let base = rmSuffix file
           exts = case intype opts of
                  GuessIn -> downloadExtensions
                  e@(ATermIn _) -> ['.' : show e, '.' : treeS ++ show e]
                  e -> ['.' : show e]
           names = file : map (base ++) (exts ++ [envSuffix])
       -- look for the first existing file
       validFlags <- mapM doesFileExist names
       return (find fst (zip validFlags names) >>= (return . snd))

-- | should env be written
hasEnvOut :: HetcatsOpts -> Bool
hasEnvOut = any ( \ o -> case o of
                           EnvOut -> True
                           _ -> False) . outtypes

-- | should prf be written
isPrfOut :: OutType -> Bool
isPrfOut o = case o of
    Prf -> True
    _ -> False

-- | should prf be written
hasPrfOut :: HetcatsOpts -> Bool
hasPrfOut = any isPrfOut . outtypes

-- | remove prf writing
removePrfOut :: HetcatsOpts -> HetcatsOpts
removePrfOut opts =
     opts { outtypes = filter (not . isPrfOut) $ outtypes opts }

-- |
-- gets two Paths and checks if the first file is not older than the
-- second one and should return True for two identical files
checkRecentEnv :: HetcatsOpts -> FilePath -> FilePath -> IO Bool
checkRecentEnv opts fp1 base2 = catch (do
    fp1_time <- getModificationTime fp1
    maybe_source_file <- existsAnSource opts {intype = GuessIn} base2
    maybe (return False) ( \ fp2 -> do
       fp2_time <- getModificationTime fp2
       return (fp1_time >= fp2_time)) maybe_source_file
    ) (const $ return False)

-- | 'parseInType' parses an 'InType' Flag from user input
parseInType :: String -> Flag
parseInType = InType . parseInType1

-- | 'parseInType1' parses an 'InType' Flag from a String
parseInType1 :: String -> InType
parseInType1 str =
  case reads str of
    [(t, "")] -> t
    _ -> hetsError (str ++ " is not a valid ITYPE")
      {- the mere typo read instead of reads caused the runtime error:
         Fail: Prelude.read: no parse -}

-- 'parseOutTypes' parses an 'OutTypes' Flag from user input
parseOutTypes :: String -> Flag
parseOutTypes str = case reads $ bracket str of
    [(l, "")] -> OutTypes l
    _ -> hetsError (str ++ " is not a valid OTYPES")

-- | 'parseSpecOpts' parses a 'Specs' Flag from user input
parseSpecOpts :: String -> Flag
parseSpecOpts s = Specs $ map mkSimpleId $ splitOn ',' s

-- | 'parseTransOpt' parses a 'Trans' Flag from user input
parseTransOpt :: String -> Flag
parseTransOpt s = Trans $ map mkSimpleId $ splitOn ':' s

-- | guesses the InType
guess :: String -> InType -> InType
guess file itype = case itype of
    GuessIn -> guessInType file
    _ -> itype

-- | 'guessInType' parses an 'InType' from the FilePath
guessInType :: FilePath -> InType
guessInType file =
    case fileparse downloadExtensions file of
      (_,_,Just ('.' : suf)) -> parseInType1 suf
      (_,_,_)  -> GuessIn

-- | 'parseCASLAmalg' parses CASL amalgamability options
parseCASLAmalg :: String -> Flag
parseCASLAmalg str =
    case reads $ bracket str of
    [(l, "")] -> CASLAmalg $ filter ( \ o -> case o of
                                      NoAnalysis -> False
                                      _ -> True ) l
    _ -> hetsError $ str ++
                    " is not a valid CASL amalgamability analysis option list"

-- main functions --

-- | 'hetcatsOpts' parses sensible HetcatsOpts from ARGV
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
  let argv' = filter (not . isUni) argv
      isUni s = take 5 s == "--uni"
   in case (getOpt Permute options argv') of
        (opts, non_opts, []) ->
            do flags <- checkFlags opts
               infs <- checkInFiles non_opts
               let hcOpts = (foldr (flip makeOpts) defaultHetcatsOpts flags)
                            { infiles = infs }
               if null infs && not (interactive hcOpts)&&(connectP hcOpts <0)&&
                  (listen hcOpts <0) then
                   hetsError "missing input files"
                   else return hcOpts
        (_, _, errs) -> hetsError (concat errs)

-- | 'checkFlags' checks all parsed Flags for sanity
checkFlags :: [Flag] -> IO [Flag]
checkFlags fs =
    let collectFlags = (collectDirs
                        . collectOutTypes
                        . collectVerbosity
                        . collectSpecOpts
                        -- collect some more here?
                   )
    in do if not $ null [ () | Help <- fs]
             then do putStrLn hetsUsage
                     exitWith ExitSuccess
             else return [] -- fall through
          if not $ null [ () | Version <- fs]
             then do putStrLn ("version of hets: " ++ hetcats_version)
                     exitWith ExitSuccess
             else return [] -- fall through
          fs' <- collectFlags fs
          return fs'

-- | 'checkInFiles' checks all given input files for sanity
checkInFiles :: [String] -> IO [FilePath]
checkInFiles fs = do
    let ifs = filter (not . checkUri) fs
        efs = filter hasExtension ifs
        hasExtension f = any ( \ e -> isSuffixOf e f)
                                        downloadExtensions
    bs <- mapM doesFileExist efs
    if and bs
      then return fs
      else hetsError $ "invalid input files: " ++
             (unwords $ map snd $ filter (not . fst) $ zip bs efs)

-- auxiliary functions: FileSystem interaction --

-- | check if infile is uri
checkUri :: FilePath -> Bool
checkUri file = let (_, t) = span (/= ':') file in
                   if length t < 4 then False
                      else let (_ : c2 : c3 : _) = t in
                              if c2 == '/' && c3 == '/' then True
                              -- (http://, https://, ftp://, file://, etc.)
                                 else False

-- | 'checkOutDirs' checks a list of OutDir for sanity
checkOutDirs :: [Flag] -> IO [Flag]
checkOutDirs fs = do
    case fs of
        [] -> return ()
        [f] -> checkOutDir f
        _ -> hetsError
            "Only one output directory may be specified on the command line"
    return fs

-- | 'checkLibDirs' checks a list of LibDir for sanity
checkLibDirs :: [Flag] -> IO [Flag]
checkLibDirs fs = do
    case fs of
        [] -> do
            s <- getEnvDef "HETS_LIB" ""
            if null s then return [] else do
                let d = LibDir s
                checkLibDir d
                return [d]
        [f] -> checkLibDir f >> return fs
        _ -> hetsError
            "Only one library directory may be specified on the command line"

-- | 'checkLibDir' checks a single LibDir for sanity
checkLibDir :: Flag -> IO ()
checkLibDir (LibDir file) =
    do exists <- doesDirectoryExist file
       if exists then return ()
          else hetsError $ "Not a valid library directory: " ++ file
checkLibDir _ = return ()

-- | 'checkOutDir' checks a single OutDir for sanity
checkOutDir :: Flag -> IO ()
checkOutDir (OutDir file) =
    do exists <- doesDirectoryExist file
       if exists then return ()
          else hetsError $ "Not a valid output directory: " ++ file
checkOutDir _ = return ()

-- auxiliary functions: collect flags --

collectDirs :: [Flag] -> IO [Flag]
collectDirs fs =
    let (ods,fs') = partition isOutDir fs
        (lds,fs'') = partition isLibDir fs'
        isOutDir (OutDir _) = True
        isOutDir _          = False
        isLibDir (LibDir _) = True
        isLibDir _          = False
    in do ods' <- checkOutDirs ods
          lds' <- checkLibDirs lds
          return $ ods' ++ lds' ++ fs''

collectVerbosity :: [Flag] -> [Flag]
collectVerbosity fs =
    let (vs,fs') = partition isVerb fs
        verbosity = (sum . map (\(Verbose x) -> x)) vs
        isVerb (Verbose _) = True
        isVerb _           = False
        vfs = Verbose verbosity : fs'
    in if not $ null [() | Quiet <- fs'] then Verbose 0 : fs' else
       if null vs then Verbose 1 : fs' else vfs

collectOutTypes :: [Flag] -> [Flag]
collectOutTypes fs =
    let (ots,fs') = partition isOType fs
        isOType (OutTypes _) = True
        isOType _            = False
        otypes = foldl concatOTypes [] ots
        concatOTypes = (\ os (OutTypes ot) -> os ++ ot)
    in if null otypes then fs' else OutTypes otypes : fs'

collectSpecOpts :: [Flag] -> [Flag]
collectSpecOpts fs =
    let (rfs,fs') = partition isSpecOpt fs
        isSpecOpt (Specs _) = True
        isSpecOpt _ = False
        specs = foldl concatSpecOpts [] rfs
        concatSpecOpts = (\ os (Specs ot) -> os ++ ot)
    in if null specs then fs' else Specs specs : fs'

-- auxiliary functions: error messages --

-- | 'hetsError' is a generic Error messaging function that prints the Error
-- and usage information, if the user caused the Error
hetsError :: String -> a
hetsError errorString = error (errorString ++ "\n" ++ hetsUsage)

-- | 'hetsUsage' generates usage information for the commandline
hetsUsage :: String
hetsUsage = let header = "Usage: hets [OPTION...] file ... file [+RTS -?]"
  in usageInfo header options

-- | 'putIfVerbose' prints a given String to StdOut when the given HetcatsOpts'
-- Verbosity exceeds the given level
putIfVerbose :: HetcatsOpts -> Int -> String -> IO ()
putIfVerbose opts level str =
    if outputToStdout opts then
        if verbose opts >= level then putStrLn str else return ()
    else return ()

doDump :: HetcatsOpts -> String -> IO () -> IO ()
doDump opts str act = if elem str $ dumpOpts opts then act else return ()

-- | add base file name (second argument) to path
pathAndBase :: FilePath -> FilePath -> FilePath
pathAndBase path base =
    if null path then base
       else if last path == '/' then path ++ base
            else path ++ "/" ++ base

-- | show diagnostic messages (see Result.hs), according to verbosity level
showDiags :: HetcatsOpts -> [Diagnosis] -> IO()
showDiags opts ds =
    runResultT (showDiags1 opts $ liftR $ Result ds Nothing) >> return ()

-- | show diagnostic messages (see Result.hs), according to verbosity level
showDiags1 :: HetcatsOpts -> ResultT IO a -> ResultT IO a
showDiags1 opts res =
  if outputToStdout opts then do
    Result ds res' <- lift $ runResultT res
    lift $ printDiags (verbose opts) ds
    case res' of
      Just res'' -> return res''
      Nothing -> liftR $ Result [] Nothing
  else res
