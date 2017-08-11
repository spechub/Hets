{-# LANGUAGE CPP #-}
{- |
Module      :  ./Driver/Options.hs
Description :  Datatypes and functions for options that hets understands.
Copyright   :  (c) Martin Kuehl, Christian Maeder, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Datatypes for options that hets understands.
   Useful functions to parse and check user-provided values.
-}

module Driver.Options
  ( HetcatsOpts (..)
  , Flag
  , optionArgs
  , optionFlags
  , accessTokenS
  , makeOpts
  , AnaType (..)
  , GuiType (..)
  , InType (..)
  , plainInTypes
  , OWLFormat (..)
  , plainOwlFormats
  , OutType (..)
  , PrettyType (..)
  , prettyList
  , GraphType (..)
  , SPFType (..)
  , ATType
  , Delta
  , hetcatsOpts
  , printOptionsWarnings
  , isStructured
  , guess
  , rmSuffix
  , envSuffix
  , prfSuffix
  , removePrfOut
  , hasEnvOut
  , hasPrfOut
  , getFileNames
  , existsAnSource
  , getExtensions
  , checkRecentEnv
  , downloadExtensions
  , defaultHetcatsOpts
  , showDiags
  , showDiags1
  , putIfVerbose
  , doDump
  , checkUri
  , defLogicIsDMU
  , useCatalogURL
  , hetsIOError
  ) where

import Driver.Version

import Common.Utils
import Common.IO
import Common.Id
import Common.Result
import Common.ResultT
import Common.Amalgamate
import Common.Keywords

import System.Directory
import System.Console.GetOpt
import System.Exit
import System.IO

import Control.Monad
import Control.Monad.Trans
import Data.Char
import Data.List
import Data.Maybe

-- | translate a given http reference using the URL catalog
useCatalogURL :: HetcatsOpts -> FilePath -> FilePath
useCatalogURL opts fname = case mapMaybe
    (\ (a, b) -> fmap (b ++) $ stripPrefix a fname)
    $ urlCatalog opts of
  m : _ -> m
  _ -> fname

bracket :: String -> String
bracket s = "[" ++ s ++ "]"

-- use the same strings for parsing and printing!
verboseS, intypeS, outtypesS, skipS, justStructuredS, transS,
     guiS, libdirsS, outdirS, amalgS, recursiveS, namedSpecsS,
     interactiveS, modelSparQS, counterSparQS, connectS, xmlS, dbS, listenS,
     applyAutomaticRuleS, normalFormS, unlitS, pidFileS :: String

modelSparQS = "modelSparQ"
counterSparQS = "counterSparQ"
verboseS = "verbose"
intypeS = "input-type"
outtypesS = "output-types"
skipS = "just-parse"
justStructuredS = "just-structured"
guiS = "gui"
libdirsS = "hets-libdirs"
outdirS = "output-dir"
amalgS = "casl-amalg"
namedSpecsS = "named-specs"
transS = "translation"
recursiveS = "recursive"
interactiveS = "interactive"
connectS = "connect"
xmlS = "xml"
dbS = "db"
listenS = "listen"
pidFileS = "pidfile"
applyAutomaticRuleS = "apply-automatic-rule"
normalFormS = "normal-form"
unlitS = "unlit"

urlCatalogS :: String
urlCatalogS = "url-catalog"

relposS :: String
relposS = "relative-positions"

fullSignS :: String
fullSignS = "full-signatures"

printASTS :: String
printASTS = "print-AST"

fullTheoriesS :: String
fullTheoriesS = "full-theories"

logicGraphS :: String
logicGraphS = "logic-graph"

logicListS :: String
logicListS = "logic-list"

fileTypeS :: String
fileTypeS = "file-type"

blacklistS :: String
blacklistS = "blacklist"

whitelistS :: String
whitelistS = "whitelist"

accessTokenS :: String
accessTokenS = "access-token"

httpRequestHeaderS :: String
httpRequestHeaderS = "http-request-header"

genTermS, treeS, bafS :: String
genTermS = "gen_trm"
treeS = "tree."
bafS = ".baf"

graphE, ppS, envS, deltaS, prfS, omdocS, hsS, experimentalS :: String
graphE = "graph."
ppS = "pp."
envS = "env"
deltaS = ".delta"
prfS = "prf"
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
  , urlCatalog :: [(String, String)]
  , infiles :: [FilePath] -- ^ files to be read
  , specNames :: [SIMPLE_ID] -- ^ specs to be processed
  , transNames :: [SIMPLE_ID] -- ^ comorphism to be processed
  , viewNames :: [SIMPLE_ID] -- ^ views to be processed
  , intype :: InType
  , libdirs :: [FilePath]
  , modelSparQ :: FilePath
  , counterSparQ :: Int
  , outdir :: FilePath
  , outtypes :: [OutType]
  , databaseConfigFile :: FilePath
  , databaseSubConfig :: String
  , xupdate :: FilePath
  , recurse :: Bool
  , verbose :: Int
  , defLogic :: String
  , defSyntax :: String
  , outputToStdout :: Bool    -- ^ send messages to stdout?
  , caslAmalg :: [CASLAmalgOpt]
  , interactive :: Bool
  , connectP :: Int
  , connectH :: String
  , uncolored :: Bool
  , xmlFlag :: Bool
  , applyAutomatic :: Bool
  , computeNormalForm :: Bool
  , dumpOpts :: [String]
  , disableCertificateVerification :: Bool
  , ioEncoding :: Enc
    -- | use the library name in positions to avoid differences after uploads
  , useLibPos :: Bool
  , unlit :: Bool
  , serve :: Bool
  , listen :: Int
  , pidFile :: FilePath
  , whitelist :: [[String]]
  , blacklist :: [[String]]
  , runMMT :: Bool
  , fullTheories :: Bool
  , outputLogicList :: Bool
  , outputLogicGraph :: Bool
  , fileType :: Bool
  , accessToken :: String
  , httpRequestHeaders :: [String]
  , fullSign :: Bool
  , printAST :: Bool }

{- | 'defaultHetcatsOpts' defines the default HetcatsOpts, which are used as
basic values when the user specifies nothing else -}
defaultHetcatsOpts :: HetcatsOpts
defaultHetcatsOpts = HcOpt
  { analysis = Basic
  , guiType = NoGui
  , urlCatalog = []
  , infiles = []
  , specNames = []
  , transNames = []
  , viewNames = []
  , intype = GuessIn
  , libdirs = []
  , modelSparQ = ""
  , counterSparQ = 3
  , outdir = ""
  , outtypes = [] -- no default
  , databaseConfigFile = ""
  , databaseSubConfig = ""
  , xupdate = ""
  , recurse = False
  , defLogic = "CASL"
  , defSyntax = ""
  , verbose = 1
  , outputToStdout = True
  , caslAmalg = [Cell]
  , interactive = False
  , connectP = -1
  , connectH = ""
  , uncolored = False
  , xmlFlag = False
  , applyAutomatic = False
  , computeNormalForm = False
  , dumpOpts = []
  , disableCertificateVerification = False
  , ioEncoding = Utf8
  , useLibPos = False
  , unlit = False
  , serve = False
  , listen = -1
  , pidFile = ""
  , whitelist = []
  , blacklist = []
  , runMMT = False
  , fullTheories = False
  , outputLogicList = False
  , outputLogicGraph = False
  , fileType = False
  , accessToken = ""
  , httpRequestHeaders = []
  , fullSign = False
  , printAST = False }

instance Show HetcatsOpts where
  show opts =
    let showFlag p o = if p opts then showOpt o else ""
        showIPLists p s = let ll = p opts in if null ll then "" else
          showEqOpt s . intercalate "," $ map (intercalate ".") ll
    in
    showEqOpt verboseS (show $ verbose opts)
    ++ show (guiType opts)
    ++ showFlag outputLogicList logicListS
    ++ showFlag outputLogicGraph logicGraphS
    ++ showFlag fileType fileTypeS
    ++ showFlag interactive interactiveS
    ++ show (analysis opts)
    ++ case defLogic opts of
          s | s /= defLogic defaultHetcatsOpts -> showEqOpt logicS s
          _ -> ""
    ++ case defSyntax opts of
          s | s /= defSyntax defaultHetcatsOpts -> showEqOpt serializationS s
          _ -> ""
    ++ case httpRequestHeaders opts of
          [] -> ""
          headers -> concatMap (showEqOpt httpRequestHeaderS . show) headers
    ++ case accessToken opts of
          "" -> ""
          t -> showEqOpt accessTokenS t
    ++ showEqOpt libdirsS (intercalate ":" $ libdirs opts)
    ++ case modelSparQ opts of
          "" -> ""
          f -> showEqOpt modelSparQS f
    ++ case counterSparQ opts of
          n | n /= counterSparQ defaultHetcatsOpts
              -> showEqOpt counterSparQS $ show n
          _ -> ""
    ++ showFlag xmlFlag xmlS
    ++ showFlag ((/= -1) . connectP) connectS
    ++ showFlag ((/= -1) . listen) listenS
    ++ showEqOpt pidFileS (pidFile opts)
    ++ showIPLists whitelist whitelistS
    ++ showIPLists blacklist blacklistS
    ++ concatMap (showEqOpt "dump") (dumpOpts opts)
    ++ showEqOpt "encoding" (map toLower $ show $ ioEncoding opts)
    ++ showFlag unlit unlitS
    ++ showFlag useLibPos relposS
    ++ showFlag fullSign fullSignS
    ++ showFlag printAST printASTS
    ++ showFlag fullTheories fullTheoriesS
    ++ case urlCatalog opts of
         [] -> ""
         cs -> showEqOpt urlCatalogS $ intercalate ","
           $ map (\ (a, b) -> a ++ '=' : b) cs
    ++ showEqOpt intypeS (show $ intype opts)
    ++ showEqOpt outdirS (outdir opts)
    ++ showEqOpt outtypesS (intercalate "," $ map show $ outtypes opts)
    ++ showFlag recurse recursiveS
    ++ showFlag applyAutomatic applyAutomaticRuleS
    ++ showFlag computeNormalForm normalFormS
    ++ showEqOpt namedSpecsS (intercalate "," $ map show $ specNames opts)
    ++ showEqOpt transS (intercalate ":" $ map show $ transNames opts)
    ++ showEqOpt viewS (intercalate "," $ map show $ viewNames opts)
    ++ showEqOpt amalgS (tail $ init $ show $
                                      case caslAmalg opts of
                                      [] -> [NoAnalysis]
                                      l -> l)
    ++ " " ++ unwords (infiles opts)

-- | every 'Flag' describes an option (see usage info)
data Flag =
    Verbose Int
  | Quiet
  | Uncolored
  | Version
  | VersionNumeric
  | Recurse
  | ApplyAutomatic
  | NormalForm
  | Help
  | Gui GuiType
  | Analysis AnaType
  | DefaultLogic String
  | DefaultSyntax String
  | InType InType
  | LibDirs String
  | OutDir FilePath
  | XUpdate FilePath
  | ModelSparQ FilePath
  | CounterSparQ Int
  | OutTypes [OutType]
  | DatabaseConfigFile FilePath
  | DatabaseSubConfig String
  | Specs [SIMPLE_ID]
  | Trans [SIMPLE_ID]
  | Views [SIMPLE_ID]
  | CASLAmalg [CASLAmalgOpt]
  | Interactive
  | Connect Int String
  | XML
  | Dump String
  | DisableCertificateVerification
  | IOEncoding Enc
  | Unlit
  | RelPos
  | Serve
  | Listen Int
  | PidFile FilePath
  | Whitelist String
  | Blacklist String
  | UseMMT
  | FullTheories
  | FullSign
  | PrintAST
  | OutputLogicList
  | OutputLogicGraph
  | FileType
  | AccessToken String
  | HttpRequestHeader String
  | UrlCatalog [(String, String)] deriving Show

-- | 'makeOpts' includes a parsed Flag in a set of HetcatsOpts
makeOpts :: HetcatsOpts -> Flag -> HetcatsOpts
makeOpts opts flg =
  let splitIPs = map (splitBy '.') . splitOn ','
  in case flg of
    Interactive -> opts { interactive = True }
    XML -> opts { xmlFlag = True }
    Listen x -> opts { listen = x }
    PidFile x -> opts { pidFile = x }
    Blacklist x -> opts { blacklist = splitIPs x }
    Whitelist x -> opts { whitelist = splitIPs x }
    Connect x y -> opts { connectP = x, connectH = y }
    Analysis x -> opts { analysis = x }
    Gui x -> opts { guiType = x }
    InType x -> opts { intype = x }
    LibDirs x -> opts { libdirs = joinHttpLibPath $ splitPaths x }
    ModelSparQ x -> opts { modelSparQ = x }
    CounterSparQ x -> opts { counterSparQ = x }
    OutDir x -> opts { outdir = x }
    OutTypes x -> opts { outtypes = x }
    DatabaseConfigFile x -> opts { databaseConfigFile = x }
    DatabaseSubConfig x -> opts { databaseSubConfig = x }
    XUpdate x -> opts { xupdate = x }
    Recurse -> opts { recurse = True }
    ApplyAutomatic -> opts { applyAutomatic = True }
    NormalForm -> opts { computeNormalForm = True }
    Specs x -> opts { specNames = x }
    Trans x -> opts { transNames = x }
    Views x -> opts { viewNames = x }
    Verbose x -> opts { verbose = x }
    DefaultLogic x -> opts { defLogic = x }
    DefaultSyntax x -> opts { defSyntax = x }
    CASLAmalg x -> opts { caslAmalg = x }
    Quiet -> opts { verbose = 0 }
    Uncolored -> opts { uncolored = True }
    Dump s -> opts { dumpOpts = s : dumpOpts opts }
    DisableCertificateVerification ->
      opts { disableCertificateVerification = True }
    IOEncoding e -> opts { ioEncoding = e }
    Serve -> opts { serve = True }
    Unlit -> opts { unlit = True }
    RelPos -> opts { useLibPos = True }
    UseMMT -> opts { runMMT = True }
    FullTheories -> opts { fullTheories = True }
    OutputLogicList -> opts { outputLogicList = True }
    OutputLogicGraph -> opts { outputLogicGraph = True }
    FileType -> opts { fileType = True }
    FullSign -> opts { fullSign = True }
    PrintAST -> opts { printAST = True }
    UrlCatalog m -> opts { urlCatalog = m ++ urlCatalog opts }
    AccessToken s -> opts { accessToken = s }
    HttpRequestHeader header -> opts { httpRequestHeaders = header : httpRequestHeaders opts }
    Help -> opts -- skipped
    Version -> opts -- skipped
    VersionNumeric -> opts -- skipped

-- | 'AnaType' describes the type of analysis to be performed
data AnaType = Basic | Structured | Skip

instance Show AnaType where
  show a = case a of
    Basic -> ""
    Structured -> showOpt justStructuredS
    Skip -> showOpt skipS

-- | check if structured analysis should be performed
isStructured :: HetcatsOpts -> Bool
isStructured a = case analysis a of
    Structured -> True
    _ -> False

-- | 'GuiType' determines if we want the GUI shown
data GuiType = UseGui | NoGui
  deriving Eq

instance Show GuiType where
  show g = case g of
    UseGui -> showOpt guiS
    NoGui -> ""

-- | 'InType' describes the type of input the infile contains
data InType =
    ATermIn ATType
  | CASLIn
  | HetCASLIn
  | DOLIn
  | OWLIn OWLFormat
  | HaskellIn
  | MaudeIn
  | TwelfIn
  | HolLightIn
  | IsaIn
  | ThyIn
  | PrfIn
  | OmdocIn
  | ExperimentalIn -- ^ for testing new functionality
  | ProofCommand
  | GuessIn
  | RDFIn
  | FreeCADIn
  | CommonLogicIn Bool  -- ^ "clf" or "clif" ('True' is long version)
  | DgXml
  | Xmi
  | Qvt
  | TPTPIn
  | HtmlIn -- just to complain
  deriving Eq

instance Show InType where
  show i = case i of
    ATermIn at -> genTermS ++ show at
    CASLIn -> "casl"
    HetCASLIn -> "het"
    DOLIn -> "dol"
    OWLIn oty -> show oty
    HaskellIn -> hsS
    ExperimentalIn -> "exp"
    MaudeIn -> "maude"
    TwelfIn -> "elf"
    HolLightIn -> "hol"
    IsaIn -> "isa"
    ThyIn -> "thy"
    TPTPIn -> "tptp"
    PrfIn -> prfS
    OmdocIn -> omdocS
    ProofCommand -> "hpf"
    GuessIn -> ""
    RDFIn -> "rdf"
    FreeCADIn -> "fcstd"
    CommonLogicIn isLong -> if isLong then "clif" else "clf"
    DgXml -> xmlS
    Xmi -> "xmi"
    Qvt -> "qvt"
    HtmlIn -> "html"

-- maybe this optional tree prefix can be omitted
instance Read InType where
    readsPrec _ = readShowAux $ concatMap showAll (plainInTypes ++ aInTypes)
      where showAll i@(ATermIn _) = [(show i, i), (treeS ++ show i, i)]
            showAll i = [(show i, i)]

-- | 'ATType' describes distinct types of ATerms
data ATType = BAF | NonBAF deriving Eq

instance Show ATType where
  show a = case a of
    BAF -> bafS
    NonBAF -> ""

-- RDFIn is on purpose not listed; must be added manually if neccessary
plainInTypes :: [InType]
plainInTypes =
  [ CASLIn, HetCASLIn, DOLIn ]
  ++ map OWLIn plainOwlFormats ++
  [ HaskellIn, ExperimentalIn
  , MaudeIn, TwelfIn
  , HolLightIn, IsaIn, ThyIn, PrfIn, OmdocIn, ProofCommand
  , CommonLogicIn False, CommonLogicIn True
  , DgXml, FreeCADIn, Xmi, Qvt, TPTPIn ]

aInTypes :: [InType]
aInTypes = [ ATermIn x | x <- [BAF, NonBAF] ]

-- | 'OWLFormat' lists possibilities for OWL syntax (in + out)
data OWLFormat =
    Manchester
  | OwlXml
  | RdfXml
  | OBO
  | Turtle
  deriving Eq

plainOwlFormats :: [OWLFormat]
plainOwlFormats = [ Manchester, OwlXml, RdfXml, OBO, Turtle ]

instance Show OWLFormat where
  show ty = case ty of
    Manchester -> "omn"
    OwlXml -> "owl"
    -- "owl.xml" ?? might occur but conflicts with dgxml
    RdfXml -> "rdf"
    OBO -> "obo"
    Turtle -> "ttl"

data SPFType = ConsistencyCheck | ProveTheory deriving Eq

instance Show SPFType where
  show x = case x of
    ConsistencyCheck -> cS
    ProveTheory -> ""

spfTypes :: [SPFType]
spfTypes = [ConsistencyCheck, ProveTheory]

-- | 'OutType' describes the type of outputs that we want to generate
data OutType =
    PrettyOut PrettyType
  | GraphOut GraphType
  | Prf
  | EnvOut
  | OWLOut OWLFormat
  | CLIFOut
  | KIFOut
  | OmdocOut
  | XmlOut -- ^ development graph xml output
  | DbOut -- ^ development graph database output
  | JsonOut -- ^ development graph json output
  | ExperimentalOut -- ^ for testing new functionality
  | HaskellOut
  | FreeCADOut
  | ThyFile -- ^ isabelle theory file
  | DfgFile SPFType -- ^ SPASS input file
  | TPTPFile
  | ComptableXml
  | MedusaJson
  | RDFOut
  | SigFile Delta -- ^ signature as text
  | TheoryFile Delta -- ^ signature with sentences as text
  | SymXml
  | SymsXml
  deriving Eq

instance Show OutType where
  show o = case o of
    PrettyOut p -> ppS ++ show p
    GraphOut f -> graphE ++ show f
    Prf -> prfS
    EnvOut -> envS
    OWLOut oty -> show oty
    CLIFOut -> "clif"
    KIFOut -> "kif"
    OmdocOut -> omdocS
    XmlOut -> xmlS
    DbOut -> dbS
    JsonOut -> "json"
    ExperimentalOut -> experimentalS
    HaskellOut -> hsS
    FreeCADOut -> "fcxml"
    ThyFile -> "thy"
    DfgFile t -> dfgS ++ show t
    TPTPFile -> tptpS
    ComptableXml -> "comptable.xml"
    MedusaJson -> "medusa.json"
    RDFOut -> "nt"
    SigFile d -> "sig" ++ show d
    TheoryFile d -> "th" ++ show d
    SymXml -> "sym.xml"
    SymsXml -> "syms.xml"

plainOutTypeList :: [OutType]
plainOutTypeList =
  [ Prf, EnvOut ] ++ map OWLOut plainOwlFormats ++
  [ RDFOut, CLIFOut, KIFOut, OmdocOut, XmlOut, JsonOut, DbOut, ExperimentalOut
  , HaskellOut, ThyFile, ComptableXml, MedusaJson, FreeCADOut, SymXml, SymsXml
  , TPTPFile]

outTypeList :: [OutType]
outTypeList = let dl = [Delta, Fully] in
    plainOutTypeList
    ++ [ PrettyOut p | p <- prettyList ++ prettyList2]
    ++ [ SigFile d | d <- dl ]
    ++ [ TheoryFile d | d <- dl ]
    ++ [ DfgFile x | x <- spfTypes]
    ++ [ GraphOut f | f <- graphList ]

instance Read OutType where
    readsPrec _ = readShow outTypeList

data Delta = Delta | Fully deriving Eq

instance Show Delta where
  show d = case d of
    Delta -> deltaS
    Fully -> ""

{- | 'PrettyType' describes the type of output we want the pretty-printer
to generate -}
data PrettyType = PrettyAscii Bool | PrettyLatex Bool | PrettyXml | PrettyHtml
  deriving Eq

instance Show PrettyType where
  show p = case p of
    PrettyAscii b -> (if b then "stripped." else "") ++ "het"
    PrettyLatex b -> (if b then "labelled." else "") ++ "tex"
    PrettyXml -> xmlS
    PrettyHtml -> "html"

prettyList :: [PrettyType]
prettyList = [PrettyAscii False, PrettyLatex False, PrettyXml, PrettyHtml]

prettyList2 :: [PrettyType]
prettyList2 = [PrettyAscii True, PrettyLatex True]

-- | 'GraphType' describes the type of Graph that we want generated
data GraphType =
    Dot Bool -- ^ True means show internal node labels
  deriving Eq

instance Show GraphType where
  show g = case g of
    Dot si -> (if si then "exp." else "") ++ "dot"

graphList :: [GraphType]
graphList = [Dot True, Dot False]

{- | 'options' describes all available options and is used to generate usage
information -}
options :: [OptDescr Flag]
options = let
    cslst = "is a comma-separated list"
       ++ crS ++ "of one or more from:"
    crS = "\n  "
    bS = "| "
    joinBar l = "(" ++ intercalate "|" l ++ ")" in
    [ Option "v" [verboseS] (OptArg parseVerbosity "0-5")
      "verbosity, default is -v1"
    , Option "q" ["quiet"] (NoArg Quiet)
      "same as -v0, no output to stdout"
    , Option "V" ["version"] (NoArg Version)
      "print version information and exit"
    , Option "" ["numeric-version"] (NoArg VersionNumeric)
      "print version number and exit"
    , Option "h" ["help", "usage"] (NoArg Help)
      "print usage information and exit"
#ifdef UNI_PACKAGE
    , Option "g" [guiS] (NoArg (Gui UseGui))
      "show graphs in windows"
    , Option "u" ["uncolored"] (NoArg Uncolored)
      "no colors in shown graphs"
#endif
    , Option "x" [xmlS] (NoArg XML)
       "use xml packets to communicate"
#ifdef SERVER
    , Option "P" [pidFileS] (ReqArg PidFile "FILEPATH")
       "path to put the PID file of the hets server (omit if no pidfile is desired)"
    , Option "X" ["server"] (NoArg Serve)
       "start hets as web-server"
#endif
    , Option "z" [logicListS] (NoArg OutputLogicList)
      "output logic list as plain text"
    , Option "G" [logicGraphS] (NoArg OutputLogicGraph)
      "output logic graph (as xml) or as graph (-g)"
    , Option "I" [interactiveS] (NoArg Interactive)
      "run in interactive (console) mode"
    , Option "F" [fileTypeS] (NoArg FileType)
      "only display file type"
    , Option "p" [skipS] (NoArg $ Analysis Skip)
      "skip static analysis, only parse"
    , Option "s" [justStructuredS] (NoArg $ Analysis Structured)
      "skip basic, just do structured analysis"
    , Option "l" [logicS] (ReqArg DefaultLogic "LOGIC")
      "choose logic, default is CASL"
    , Option "y" [serializationS] (ReqArg DefaultSyntax "SER")
      "choose different logic syntax"
    , Option "L" [libdirsS] (ReqArg LibDirs "DIR")
      ("colon-separated list of directories"
       ++ crS ++ "containing DOL libraries."
       ++ crS ++ "If an http[s] URL is specified here, it is treated as the last libdir because colons can occur in such URLs")
    , Option "m" [modelSparQS] (ReqArg ModelSparQ "FILE")
      "lisp file for SparQ definitions"
    , Option "" [counterSparQS] (ReqArg parseCounter "0-99")
      "maximal number of counter examples"
    , Option "c" [connectS] (ReqArg parseConnect "HOST:PORT")
      ("run (console) interface via connection"
       ++ crS ++ "to given host and port")
    , Option "S" [listenS] (ReqArg parseListen "PORT")
      "run interface/server by listening to the port"
    , Option "" [whitelistS] (ReqArg Whitelist "IP4s")
      $ "comma-separated list of IP4 addresses"
      ++ crS ++ "(missing numbers at dots are wildcards)"
    , Option "" [blacklistS] (ReqArg Blacklist "IP4s")
      $ "comma-separated list of IP4 addresses"
      ++ crS ++ "(example: 77.75.77.)"
    , Option "C" [urlCatalogS] (ReqArg parseCatalog "URLS")
      "comma-separated list of URL pairs: srcURL=tarURL"
    , Option "i" [intypeS] (ReqArg parseInType "ITYPE")
      ("input file type can be one of:" ++
       concatMap (\ t -> crS ++ bS ++ t)
       (map show plainInTypes ++
        map (++ bracket bafS) [bracket treeS ++ genTermS]))
    , Option "d" ["dump"] (ReqArg Dump "STRING")
      "dump various strings"
    , Option "" ["disable-certificate-verification"]
      (NoArg DisableCertificateVerification)
      "Disable TLS certificate verification"
    , Option "e" ["encoding"] (ReqArg parseEncoding "ENCODING")
      "latin1 or utf8 (default) encoding"
    , Option "" [unlitS] (NoArg Unlit) "unlit input source"
    , Option "" [relposS] (NoArg RelPos) "use relative file positions"
    , Option "" [fullSignS] (NoArg FullSign) "xml output full signatures"
    , Option "" [printASTS] (NoArg PrintAST) ("print AST in xml/json output")
    , Option "" [fullTheoriesS] (NoArg FullTheories) "xml output full theories"
    , Option "" [accessTokenS] (ReqArg AccessToken "TOKEN")
      "add access token to URLs (for ontohub)"
    , Option "H" [httpRequestHeaderS] (ReqArg HttpRequestHeader "HTTP_HEADER")
      ("additional headers to use for HTTP requests"
      ++ crS ++ "this option can be used multiple times")
    , Option "O" [outdirS] (ReqArg OutDir "DIR")
      "destination directory for output files"
    , Option "o" [outtypesS] (ReqArg parseOutTypes "OTYPES")
      ("output file types, default nothing," ++ crS ++
       cslst ++ crS ++ concatMap ( \ t -> bS ++ show t ++ crS)
             plainOutTypeList
       ++ bS ++ joinBar (map show [SigFile Fully,
                                   TheoryFile Fully])
              ++ bracket deltaS ++ crS
       ++ bS ++ ppS ++ joinBar (map show prettyList) ++ crS
       ++ bS ++ ppS ++ joinBar (map show prettyList2) ++ crS
       ++ bS ++ graphE ++ joinBar (map show graphList) ++ crS
       ++ bS ++ dfgS ++ bracket cS ++ crS
       ++ bS ++ tptpS ++ bracket cS)
    , Option "" ["database-config"] (ReqArg DatabaseConfigFile "FILEPATH")
       ("path to the database configuration (yaml) file - "
       ++ "if none is given despite database output, "
       ++ "an sqlite database is created in the output directory")
    , Option "" ["database-subconfig"] (ReqArg DatabaseSubConfig "KEY")
       ("subconfig of the database-config - "
       ++ "one of: production, development, test")
    , Option "U" ["xupdate"] (ReqArg XUpdate "FILE")
      "apply additional xupdates from file"
    , Option "R" [recursiveS] (NoArg Recurse)
      "output also imported libraries"
    , Option "A" [applyAutomaticRuleS] (NoArg ApplyAutomatic)
      "apply automatic dev-graph strategy"
    , Option "N" [normalFormS] (NoArg NormalForm)
      "compute normal forms (takes long)"
    , Option "n" [namedSpecsS] (ReqArg (Specs . parseSIdOpts) "NSPECS")
      ("process specs option " ++ crS ++ cslst ++ " SIMPLE-ID")
    , Option "w" [viewS] (ReqArg (Views . parseSIdOpts) "NVIEWS")
      ("process views option " ++ crS ++ cslst ++ " SIMPLE-ID")
    , Option "t" [transS] (ReqArg parseTransOpt "TRANS")
      ("translation option " ++ crS ++
          "is a colon-separated list" ++
          crS ++ "of one or more from: SIMPLE-ID")
    , Option "a" [amalgS] (ReqArg parseCASLAmalg "ANALYSIS")
      ("CASL amalgamability analysis options" ++ crS ++ cslst ++
       crS ++ joinBar (map show caslAmalgOpts)),
      Option "M" ["MMT"] (NoArg UseMMT)
      "use MMT" ]

-- | options that require arguments for the wep-api excluding \"translation\"
optionArgs :: [(String, String -> Flag)]
optionArgs = foldr (\ o l -> case o of
  Option _ (s : _) (ReqArg f _) _ | s /= transS -> (s, f) : l
  _ -> l) [] options

-- | command line switches for the wep-api excluding non-dev-graph related ones
optionFlags :: [(String, Flag)]
optionFlags = dropWhile ((/= justStructuredS). fst) $ foldr (\ o l -> case o of
  Option _ (s : _) (NoArg f) _ -> (s, f) : l
  _ -> l) [] options

-- parser functions returning Flags --

-- | 'parseVerbosity' parses a 'Verbose' Flag from user input
parseVerbosity :: Maybe String -> Flag
parseVerbosity ms = case ms of
    Nothing -> Verbose 2
    Just s -> Verbose $ parseInt s

parseInt :: String -> Int
parseInt s = fromMaybe (hetsError $ s ++ " is not a valid INT") $ readMaybe s

parseCounter :: String -> Flag
parseCounter = CounterSparQ . parseInt

divideIntoPortHost :: String -> Bool -> (String, String) -> (String, String)
divideIntoPortHost s sw (accP, accH) = case s of
    ':' : ll -> divideIntoPortHost ll True (accP, accH)
    c : ll -> if sw then divideIntoPortHost ll True (accP, c : accH)
              else divideIntoPortHost ll False (c : accP, accH)
    [] -> (accP, accH)

-- | 'parseConnect' parses a port Flag from user input
parseConnect :: String -> Flag
parseConnect s
 = let (sP, sH) = divideIntoPortHost s False ([], [])
   in case reads sP of
                [(i, "")] -> Connect i sH
                _ -> Connect (-1) sH

parseListen :: String -> Flag
parseListen s
 = case reads s of
                [(i, "")] -> Listen i
                _ -> Listen (-1)

parseEncoding :: String -> Flag
parseEncoding s = case map toLower $ trim s of
  "latin1" -> IOEncoding Latin1
  "utf8" -> IOEncoding Utf8
  r -> hetsError (r ++ " is not a valid encoding")

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

isDefLogic :: String -> HetcatsOpts -> Bool
isDefLogic s = (s ==) . defLogic

defLogicIsDMU :: HetcatsOpts -> Bool
defLogicIsDMU = isDefLogic "DMU"

getExtensions :: HetcatsOpts -> [String]
getExtensions opts = case intype opts of
        GuessIn
          | defLogicIsDMU opts -> [".xml"]
          | isDefLogic "Framework" opts
            -> [".elf", ".thy", ".maude", ".het"]
        GuessIn -> downloadExtensions
        e@(ATermIn _) -> ['.' : show e, '.' : treeS ++ show e]
        e -> ['.' : show e]
  ++ [envSuffix]

getFileNames :: [String] -> FilePath -> [FilePath]
getFileNames exts file =
  file : map (rmSuffix file ++) exts

-- | checks if a source file for the given file name exists
existsAnSource :: HetcatsOpts -> FilePath -> IO (Maybe FilePath)
existsAnSource opts file = do
  let names = getFileNames (getExtensions opts) file
  -- look for the first existing file
  validFlags <- mapM doesFileExist names
  return . fmap snd . find fst $ zip validFlags names

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

{- |
gets two Paths and checks if the first file is not older than the
second one and should return True for two identical files -}
checkRecentEnv :: HetcatsOpts -> FilePath -> FilePath -> IO Bool
checkRecentEnv opts fp1 base2 = catchIOException False $ do
    fp1_time <- getModificationTime fp1
    maybe_source_file <- existsAnSource opts {intype = GuessIn} base2
    maybe (return False) ( \ fp2 -> do
       fp2_time <- getModificationTime fp2
       return (fp1_time >= fp2_time)) maybe_source_file

parseCatalog :: String -> Flag
parseCatalog str = UrlCatalog $ map ((\ l -> case l of
  [a, b] -> (a, b)
  _ -> hetsError (str ++ " is not a valid URL catalog"))
  . splitOn '=') $ splitOn ',' str

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

-- | parses a comma separated list from user input
parseSIdOpts :: String -> [SIMPLE_ID]
parseSIdOpts = map mkSimpleId . splitOn ','

-- | 'parseTransOpt' parses a 'Trans' Flag from user input
parseTransOpt :: String -> Flag
parseTransOpt = Trans . map mkSimpleId . splitPaths

-- | guesses the InType
guess :: String -> InType -> InType
guess file itype = case itype of
    GuessIn -> guessInType file
    _ -> itype

-- | 'guessInType' parses an 'InType' from the FilePath
guessInType :: FilePath -> InType
guessInType file = case fileparse downloadExtensions file of
      (_, _, Just ('.' : suf)) -> parseInType1 suf
      (_, _, _) -> GuessIn

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
      isUni = isPrefixOf "--uni"
   in case getOpt Permute options argv' of
        (opts, nonOpts, []) ->
            do flags <- checkFlags opts
               return (foldr (flip makeOpts) defaultHetcatsOpts flags)
                            { infiles = nonOpts }
        (_, _, errs) -> hetsIOError (concat errs)

printOptionsWarnings :: HetcatsOpts -> IO ()
printOptionsWarnings opts =
  let v = verbose opts in
  unless (null (pidFile opts) || serve opts)
    (verbMsgIOLn v 1 "option -P has no effect because it is used without -X")

-- | 'checkFlags' checks all parsed Flags for sanity
checkFlags :: [Flag] -> IO [Flag]
checkFlags fs = do
    let collectFlags = collectDirs
                        . collectOutTypes
                        . collectVerbosity
                        . collectSpecOpts
                        -- collect some more here?
        h = null [ () | Help <- fs]
        v = null [ () | Version <- fs]
        vn = null [ () | VersionNumeric <- fs]
    unless h $ putStr hetsUsage
    unless v $ putStrLn hetsVersion
    unless vn $ putStrLn hetsVersionNumeric
    unless (h && v && vn) exitSuccess
    collectFlags fs

-- auxiliary functions: FileSystem interaction --

-- | check if infile is uri
checkUri :: FilePath -> Bool
checkUri file = "://" `isPrefixOf` dropWhile isAlpha file
   -- (http://, https://, ftp://, file://, etc.)

-- | 'checkOutDirs' checks a list of OutDir for sanity
checkOutDirs :: [Flag] -> IO [Flag]
checkOutDirs fs = do
    case fs of
        [] -> return ()
        [f] -> checkOutDir f
        _ -> hetsIOError
            "Only one output directory may be specified on the command line"
    return fs

-- | 'checkLibDirs' checks a list of LibDir for sanity
checkLibDirs :: [Flag] -> IO [Flag]
checkLibDirs fs =
    case fs of
        [] -> do
            s <- getEnvDef "HETS_LIB" ""
            if null s then return [] else do
                let d = LibDirs s
                checkLibDirs [d]
                return [d]
        [LibDirs f] -> mapM_ checkLibDir (joinHttpLibPath $ splitPaths f)
          >> return fs
        _ -> hetsIOError
            "Only one library path may be specified on the command line"

joinHttpLibPath :: [String] -> [String]
joinHttpLibPath l = case l of
  p : f : r | p  == "file" && take 2 f == "//" ->
    (p ++ ':' : f) : joinHttpLibPath r
  p : f : _ | elem p ["http", "https"] && take 2 f == "//" ->
    [intercalate ":" l]
  f : r -> f : joinHttpLibPath r
  [] -> []

-- | 'checkLibDir' checks a single LibDir for sanity
checkLibDir :: FilePath -> IO ()
checkLibDir file = do
    exists <- if checkUri file then return True else doesDirectoryExist file
    unless exists . hetsIOError $ "Not a valid library directory: " ++ file

-- | 'checkOutDir' checks a single OutDir for sanity
checkOutDir :: Flag -> IO ()
checkOutDir (OutDir file) = do
    exists <- doesDirectoryExist file
    unless exists . hetsIOError $ "Not a valid output directory: " ++ file
checkOutDir _ = return ()

-- auxiliary functions: collect flags --

collectDirs :: [Flag] -> IO [Flag]
collectDirs fs = do
    let (ods, fs1) = partition isOutDir fs
        (lds, fs2) = partition isLibDir fs1
        isOutDir (OutDir _) = True
        isOutDir _ = False
        isLibDir (LibDirs _) = True
        isLibDir _ = False
    ods' <- checkOutDirs ods
    lds' <- checkLibDirs lds
    return $ ods' ++ lds' ++ fs2

collectVerbosity :: [Flag] -> [Flag]
collectVerbosity fs =
    let (v, fs') = foldr (\ f (n, rs) -> case f of
           Verbose x -> (if n < 0 then x else n + x, rs)
           _ -> (n, f : rs)) (-1, []) fs
    in if v < 0 || not (null [() | Quiet <- fs']) then fs' else Verbose v : fs'

collectOutTypes :: [Flag] -> [Flag]
collectOutTypes fs =
    let (ots, fs') = foldr (\ f (os, rs) -> case f of
           OutTypes ot -> (ot ++ os, rs)
           _ -> (os, f : rs)) ([], []) fs
    in if null ots then fs' else OutTypes ots : fs'

collectSpecOpts :: [Flag] -> [Flag]
collectSpecOpts fs =
    let (specs, fs') = foldr (\ f (os, rs) -> case f of
           Specs ot -> (ot ++ os, rs)
           _ -> (os, f : rs)) ([], []) fs
    in if null specs then fs' else Specs specs : fs'

-- auxiliary functions: error messages --

-- | only print the error (and no usage info)
hetsError :: String -> a
hetsError = error . ("command line usage error (see 'hets -h')\n" ++)

-- | print error and usage and exit with code 2
hetsIOError :: String -> IO a
hetsIOError s = do
  unless (null s) $ hPutStrLn stderr s
  putStr "for Hets usage, use: hets -h\n"
  exitWith $ ExitFailure 2

-- | 'hetsUsage' generates usage information for the commandline
hetsUsage :: String
hetsUsage = let header = "Usage: hets [OPTION ...] [FILE ...] [+RTS -?]"
  in usageInfo header options

{- | 'putIfVerbose' prints a given String to StdOut when the given HetcatsOpts'
Verbosity exceeds the given level -}
putIfVerbose :: HetcatsOpts -> Int -> String -> IO ()
putIfVerbose opts level =
    when (outputToStdout opts) . when (verbose opts >= level) . putStrLn

doDump :: HetcatsOpts -> String -> IO () -> IO ()
doDump opts str = when (elem str $ dumpOpts opts)

-- | show diagnostic messages (see Result.hs), according to verbosity level
showDiags :: HetcatsOpts -> [Diagnosis] -> IO ()
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
