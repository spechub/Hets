{-| 
   
Module      :  $Header$
Copyright   :  (c) Martin Kühl, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

   Datatypes for options, a list of options hets understands.
   Useful functions to parse and check the user-provided functions
   and for filling in default values.

   A record datatype for fast and easy access and modification
   extension of the options. 

-}

{- TODO:
    -- Check for -G Option -- if given, set OutTypes to [] and Ana to Basic
    just Maybe: 
    -- implement Read instance for some (all?) Types of Flags
    -- parse the input type via 'instance Read InType'?
    -- there's got to be a better way to realize parseOutType...
    -- an Error should be raised when more than one OutDir were specified,
       or when the OutDir wasn't approved sane
-}

{- Optionen:

Usage: hets [OPTION...] file ... file
  -v[Int]   --verbose[=Int]       chatty output to stderr
  -q        --quiet               no output to stderr
  -V        --version             print version number and exit
  -g        --gui                 use graphical user interface
  -G        --only-gui            use graphical user interface ONLY!
  -h        --help, --usage       print usage information and exit
  -i ITYPE  --input-type=ITYPE    ITYPE of input file: 
            (tree.)?gen_trm(.baf)? | het(casl)? | casl | ast(.baf)?
  -p        --just-parse          skip analysis - just parse
  -s        --just-structure      skip basic analysis - just do structured
            analysis
  -O DIR    --output-dir=DIR      destination directory for output files
  -o OTYPES --output-types=OTYPES OTYPES of output files, a comma seperated
            list of OTYPE
            OTYPE is (pp.(het|tex|html))
            |(ast|[fh]?dg(.nax)?).(het|trm|taf|html|xml)
            |(graph.(dot|ps|davinci))
	    |env
            (default: dg.taf)
?  -l id     --output-logic=id     select output logic and optional logic coding
                mit Parsec (Token.simpleId) parsen
  -L DIR    --hets-libdir=DIR     CASL library directory
  -r RAW    --raw=RAW             raw options passed to the pretty-printer
            RAW is (ascii|text|(la)?tex)=STRING where STRING is passed to the
            appropiate pretty-printer
            --casl-amalg=ANALYSIS  CASL amalgamability analysis options
            ANALYSIS is a comma-separated list of zero or more options from: 
	    (sharing,cell,colimit-thinness)

-}

module Options where

import Version
import Common.Utils
import Common.Result

import System.Directory
import System.Exit

import Data.List
import Control.Monad (filterM)

import System.Console.GetOpt

-- main Datatypes --

-- | 'HetcatsOpts' is a record set of all options received from the command line
data HetcatsOpts = 
    HcOpt { analysis :: AnaType    -- Skip | Structured | Basic
          , gui      :: GuiType    -- True when Output is shown in a GUI
          , infiles  :: [FilePath] -- files to be read
          , intype   :: InType     -- type of the file to be read
          , libdir   :: FilePath   -- CASL library directory
          , outdir   :: FilePath   -- output directory
          , outtypes :: [OutType]  -- list of output types to be generated
          , rawopts  :: [RawOpt]   -- raw options for the pretty printer
          , verbose  :: Int        -- greater than null to turn verbosity on
	  , defLogic :: String     -- initial logic 
	  , web      :: WebType    -- Web Interface
          , outputToStdout :: Bool    -- flag: output diagnostic messages?
	  , caslAmalg :: [CASLAmalgOpt] -- CASL amalgamability analysis options
          }
    deriving (Eq)

instance Show HetcatsOpts where
    show opts =    " --verbose="      ++ show (verbose opts)
                ++ showGui (gui opts)
                ++ showAnalysis (analysis opts)
                ++ " --logic="  ++ defLogic opts
                ++ " --input-type="   ++ show (intype opts)
                ++ " --output-types=" ++ showOutTypes (outtypes opts)
                ++ " " ++ showRaw (rawopts opts)
                ++ " --hets-libdir="  ++ (libdir opts)
                ++ " --output-dir="   ++ (outdir opts)
                ++ " " ++ showInFiles (infiles opts)
        where
        showAnalysis x = case x of  Skip -> " --just-parse"
                                    Structured -> " --just-structured"
                                    Basic -> ""
        showGui x = case x of Only -> " -- only-gui"
                              Also -> " --gui"
                              Not  -> ""
        showInFiles  = joinWith ' '
        showOutTypes = joinWith ',' . map show
        showRaw = joinWith ' ' . map showRaw'
        showRaw' (RawAscii s) = "--raw=ascii=" ++ s
        showRaw' (RawLatex s) = "--raw=latex=" ++ s

-- | 'makeOpts' includes a parsed Flag in a set of HetcatsOpts
makeOpts :: HetcatsOpts -> Flag -> HetcatsOpts
makeOpts opts (Analysis x) = opts { analysis = x }
makeOpts opts (Gui x)      = opts { gui = x }
makeOpts opts (InType x)   = opts { intype = x }
makeOpts opts (LibDir x)   = opts { libdir = x }
makeOpts opts (OutDir x)   = opts { outdir = x }
makeOpts opts (OutTypes x) = opts { outtypes = x }
makeOpts opts (Raw x)      = opts { rawopts = x }
makeOpts opts (Web x)      = opts { web = x }
makeOpts opts (Verbose x)  = opts { verbose = x }
makeOpts opts (DefaultLogic x) = opts { defLogic = x }
makeOpts opts (CASLAmalg x) = opts { caslAmalg = x }
makeOpts opts _    = opts -- skipped

-- | 'defaultHetcatsOpts' defines the default HetcatsOpts, which are used as
-- basic values when the user specifies nothing else
defaultHetcatsOpts :: HetcatsOpts
defaultHetcatsOpts = 
    HcOpt { analysis = Basic
          , gui      = Not
	  , web      = No
          , infiles  = []
          , intype   = GuessIn
          , libdir   = ""
          , outdir   = ""
          , outtypes = [HetCASLOut OutASTree OutAscii]
          -- better default options, but not implemented yet:
          --, outtypes = [HetCASLOut OutASTree OutXml]
          , rawopts  = []
	  , defLogic = "CASL"
          , verbose  = 1
          , outputToStdout = True
	  , caslAmalg = [Cell]
          }

-- | every 'Flag' describes a raw option
data Flag = Analysis AnaType     -- to analyse or not to analyse
          | Gui      GuiType     -- show Output in GUI
          | Help                 -- print usage message
          | InType   InType      -- type of input file
          | LibDir   FilePath    -- CASL library directory
          | OutDir   FilePath    -- destination directory for output files
          | OutTypes [OutType]   -- types of output to generate
          | Quiet                -- Ssht! Be silent!
          | Raw      [RawOpt]    -- raw options passed on to the pretty-printer
          | Verbose  Int         -- how verbose shall we be?
          | Version              -- print version number
	  | Web      WebType     -- show output in web
	  | DefaultLogic String  -- default logic to start with
	  | CASLAmalg [CASLAmalgOpt] -- CASL amalgamability analysis options
            deriving (Show,Eq)

-- | 'AnaType' describes the type of analysis we want performed
data AnaType = Basic | Structured | Skip
               deriving (Show, Eq)

-- | 'GuiType' determines if we want the GUI shown
data GuiType = Only | Also | Not
               deriving (Show, Eq)

-- | 'InType' describes the type of input the infile contains
data InType = ATermIn ATType | ASTreeIn ATType | CASLIn | WebIn | HetCASLIn | HaskellIn | GuessIn
              deriving (Show, Eq)

-- | 'ATType' describes distinct types of ATerms
data ATType = BAF | NonBAF
              deriving (Show, Eq)

-- | 'OutType' describes the type of Output that we want generated
data OutType = PrettyOut PrettyType 
             | HetCASLOut HetOutType HetOutFormat
             | GraphOut GraphType
	     | EnvOut
               deriving (Show, Eq)

-- | 'PrettyType' describes the type of Output we want the Pretty-Printer 
-- to generate
data PrettyType = PrettyAscii | PrettyLatex | PrettyHtml
                  deriving (Show, Eq)

-- | 'HetOutType' describes the type of Output we want Hets to create
data HetOutType = OutASTree | OutDGraph Flattening Bool
                  deriving (Show, Eq)

-- | 'Flattening' describes how flat the Earth really is (TODO: add comment)
data Flattening = Flattened | HidingOutside | Full
                  deriving (Show, Eq)

-- | 'HetOutFormat' describes the format of Output that HetCASL shall create
data HetOutFormat = OutAscii | OutTerm | OutTaf | OutHtml | OutXml
                    deriving (Show, Eq)

-- | 'GraphType' describes the type of Graph that we want generated
data GraphType = Dot | PostScript | Davinci
                 deriving (Show, Eq)

-- | 'WebType'
data WebType = Yes | No
	       deriving (Show, Eq)

-- | 'RawOpt' describes the options we want to be passed to the Pretty-Printer
data RawOpt = RawAscii String | RawLatex String
              deriving (Show, Eq)

-- | 'CASLAmalgOpt' describes the options for CASL amalgamability analysis algorithms
data CASLAmalgOpt = Sharing         -- ^ perform the sharing checks
		  | ColimitThinness -- ^ perform colimit thinness check (implies Sharing)
		  | Cell            -- ^ perform cell condition check (implies Sharing)
		  | NoAnalysis      -- ^ dummy option to indicate empty option string
		    deriving (Show, Eq)

-- | 'ErrorSource' describes possible sources of errors: 
-- user input or internal errors
data ErrorSource = User | Intern
                   deriving (Show, Eq)

-- | 'options' describes all available options and is used to generate usage 
-- information
options :: [OptDescr Flag]
options =
    [ Option ['v'] ["verbose"] (OptArg parseVerbosity "Int")
      "chatty output to stderr"
    , Option ['l'] ["logic"] (ReqArg DefaultLogic "LOGIC")
      "choose initial logic, the default is CASL"
    , Option ['q'] ["quiet"] (NoArg Quiet)
      "no output at all to stderr. overrides --verbose!"
    , Option ['g'] ["gui"] (NoArg (Gui Also))
      "show graphical output in a GUI window"
    , Option ['w'] ["web"] (NoArg (Web Yes))
      "show Web Interface"
    , Option ['G'] ["only-gui"] (NoArg $ Gui Only)
      "show graphical output in a GUI window - don't write Output to file"
    , Option ['V'] ["version"] (NoArg Version)
      "print version number and exit"
    , Option ['h'] ["help", "usage"] (NoArg Help)
      "print usage information and exit"
    , Option ['i'] ["input-type"]  (ReqArg parseInType "ITYPE")
      "ITYPE of input file: \n\t(tree.)?gen_trm(.baf)? | het(casl)? | casl | ast(.baf)?"
    , Option ['O'] ["output-dir"]  (ReqArg OutDir "DIR")
      "destination directory for output files"
    , Option ['o'] ["output-types"] (ReqArg parseOutTypes "OTYPES")
      "OTYPES of output files, a comma seperated list of OTYPE\n\tOTYPE is (pp.(het|tex|html))\n\t\t|(ast|[fh]?dg(.nax)?).(het|trm|taf|html|xml)\n\t\t|(graph.(dot|ps|davinci))\n\t\t|env\n\t\t(default: dg.taf)"
    , Option ['p'] ["just-parse"]  (NoArg $ Analysis Skip)
      "skip static analysis - just parse"
    , Option ['s'] ["just-structured"]  (NoArg $ Analysis Structured)
      "skip basic analysis - just do structured analysis"
    , Option ['L'] ["hets-libdir"]  (ReqArg LibDir "DIR")
      "CASL library directory"
    , Option ['r'] ["raw"] (ReqArg parseRawOpts "RAW")
      "raw options passed to the pretty-printer \n\tRAW is (ascii|text|(la)?tex)=STRING where STRING is passed to the appropiate pretty-printer"
    , Option [] ["casl-amalg"] (ReqArg parseCASLAmalg "ANALYSIS")
      "CASL amalgamability analysis options \n\tANALYSIS is a comma-separated list of zero or more options from: (sharing,cell,colimit-thinness)"
    ]
-- TODO: order in some useful way...


-- parser functions returning Flags --

-- | 'parseVerbosity' parses a 'Verbose' Flag from user input
parseVerbosity :: (Maybe String) -> Flag
parseVerbosity Nothing = Verbose 2
parseVerbosity (Just s)
    = case reads s of
                   [(i,"")] -> Verbose i
                   _        -> hetsError User (s ++ " is not a valid INT")

-- | possible input types. Boolean flag is true if intype is useable for downloads.
inTypes :: [(String,(InType,Bool))]
inTypes = [("casl",(CASLIn,True)),
           ("het",(HetCASLIn,True)),
           ("hs",(HaskellIn,True)),
	   ("web",(WebIn,True)),
           ("gen_trm",(ATermIn NonBAF,False)),
           ("tree.gen_trm",(ATermIn NonBAF,False)),
           ("gen_trm.baf",(ATermIn BAF,False)),
           ("tree.gen_trm.baf",(ATermIn BAF,False)),
           ("ast",(ASTreeIn NonBAF,False)),
           ("ast.baf",(ASTreeIn BAF,False))]

-- | possible CASL amalgamability options
caslAmalgOpts :: [(String, CASLAmalgOpt)]
caslAmalgOpts = [("sharing", Sharing),
		 ("colimit-thinness", ColimitThinness),
		 ("cell", Cell),
		 ("", NoAnalysis)]


-- | 
downloadExtensions :: [String]
downloadExtensions = map fst $ filter (\(_,(_,b)) -> b) inTypes

-- |
-- checks if a source file for the given base  exists
existsAnSource :: FilePath -> IO (Maybe FilePath)
existsAnSource base2 = 
       do
       let names = map (base2++) ("":(map ("."++) downloadExtensions))
       -- look for the first existing file
       existFlags <- sequence (map doesFileExist names)
       return (find fst (zip existFlags names) >>= (return . snd))

-- | 
-- gets two Paths and checks if the first file is more recent than the
-- second one
checkRecentEnv :: FilePath -> FilePath -> IO Bool
checkRecentEnv fp1 base2 = 
   do fp1_exists <- doesFileExist fp1
      if not fp1_exists then return False 
       else do
      maybe_source_file <- existsAnSource base2
      maybe (return False) 
	     (\ fp2 ->     do fp1_time <- getModificationTime fp1
	                      fp2_time <- getModificationTime fp2
		              return (fp1_time > fp2_time))
	     maybe_source_file


-- | 'parseInType' parses an 'InType' Flag from user input
parseInType :: String -> Flag
parseInType = InType . parseInType1


-- | 'parseInType1' parses an 'InType' Flag from a String
parseInType1 :: String -> InType
parseInType1 str = 
  case lookup str inTypes of
    Just (int,_) -> int
    Nothing -> hetsError User (str ++ " is not a valid ITYPE")

-- 'parseOutTypes' parses an 'OutTypes' Flag from user input
parseOutTypes :: String -> Flag
parseOutTypes str
    | ',' `elem` str = OutTypes $ 
                       (map eitherOType . map parseOutType . splitOn ',') str
    | otherwise = OutTypes [eitherOType (parseOutType str)]
    where
    eitherOType = either error' id
    error' s = hetsError User (s ++ " is not a valid OTYPE")

-- 'parseOutType' parses an 'OutType' from a String
parseOutType :: String -> Either String OutType
parseOutType s
    | "pp."    `isPrefixOf` s =
        parseOutType' (parsePrettyType $ drop 3 s) PrettyOut
    | "graph." `isPrefixOf` s =
        parseOutType' (parseGraphType $ drop 6 s) GraphOut
    | "ast."   `isPrefixOf` s =
        parseOutType' (parseOutFormat $ drop 4 s) (HetCASLOut OutASTree)
    | "fdg.nax."   `isPrefixOf` s =
        parseOutType' (parseOutFormat $ drop 8 s) 
                      (HetCASLOut $ OutDGraph Flattened True)
    | "fdg."   `isPrefixOf` s =
        parseOutType' (parseOutFormat $ drop 4 s)
                      (HetCASLOut $ OutDGraph Flattened False)
    | "hdg.nax."   `isPrefixOf` s =
        parseOutType' (parseOutFormat $ drop 8 s) 
                      (HetCASLOut $ OutDGraph HidingOutside True)
    | "hdg."   `isPrefixOf` s =
        parseOutType' (parseOutFormat $ drop 4 s)
                      (HetCASLOut $ OutDGraph HidingOutside False)
    | "dg.nax."    `isPrefixOf` s =
        parseOutType' (parseOutFormat $ drop 7 s)
                      (HetCASLOut $ OutDGraph Full True)
    | "dg."    `isPrefixOf` s =
        parseOutType' (parseOutFormat $ drop 3 s)
                      (HetCASLOut $ OutDGraph Full False)
    | s == "env" = Right EnvOut
    | otherwise               = Left s
    where
    parsePrettyType "het"  = Just PrettyAscii
    parsePrettyType "tex"  = Just PrettyLatex
    parsePrettyType "html" = Just PrettyHtml
    parsePrettyType _      = Nothing
    parseGraphType "dot"     = Just Dot
    parseGraphType "ps"      = Just PostScript
    parseGraphType "davinci" = Just Davinci
    parseGraphType _         = Nothing
    parseOutFormat "het"  = Just OutAscii
    parseOutFormat "taf"  = Just OutTaf
    parseOutFormat "trm"  = Just OutTerm
    parseOutFormat "html" = Just OutHtml
    parseOutFormat "xml"  = Just OutXml
    parseOutFormat _      = Nothing
    parseOutType' getter typ =
        case getter of
                    (Just t) -> Right (typ t)
                    Nothing  -> Left  s

-- | 'parseRawOpts' parses a 'Raw' Flag from user input
parseRawOpts :: String -> Flag
parseRawOpts s =
    let (prefix, string) = break (== '=') s
        parsePrefix "ascii" = RawAscii
        parsePrefix "text"  = RawAscii
        parsePrefix "latex" = RawLatex
        parsePrefix "tex"   = RawLatex
        parsePrefix _       = error'
        error' = hetsError User (s ++ " ia not a valid RAW String")
    in Raw [(parsePrefix prefix) (drop 1 string)]


-- | guesses the InType
guess :: String -> InType -> InType
guess file GuessIn = guessInType file
guess _file itype  = itype

-- | 'guessInType' parses an 'InType' from the FilePath to our 'InFile'
guessInType :: FilePath -> InType
guessInType file = 
    case fileparse (map fst inTypes)
         file of
      (_,_,Just suf) -> parseInType1 suf
      (_,_,Nothing)  -> hetsError User $
                        "InType of " ++ file ++ " unclear, please specify"


-- | 'parseCASLAmalg' parses CASL amalgamability options
parseCASLAmalg :: String -> Flag
parseCASLAmalg str = 
    let tokenize s = 
	    let mcp = findIndex (== ',') s
	    in case mcp of
			Nothing -> [s]
			Just pos -> let (w, (_ : s')) = splitAt pos s
				    in w : (tokenize s')
	recognize tok = case lookup tok caslAmalgOpts of
						      Nothing -> hetsError User (tok ++ " is not a valid CASL amalgamability analysis option")
						      Just opt -> opt
    in CASLAmalg (filter (/= NoAnalysis) (map recognize (tokenize str)))


-- main functions --

-- | 'hetcatsOpts' parses sensible HetcatsOpts from ARGV
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
  let argv' = filter (not . isUni) argv
      isUni ('-':'-':'u':'n':'i':_) = True
      isUni _ = False
   in case (getOpt Permute options argv') of
        (opts,non_opts,[]) ->
            do flags <- checkFlags opts
               infs  <- checkInFiles non_opts
               hcOpts <- return $ 
                         foldr (flip makeOpts) defaultHetcatsOpts flags
	       let hcOpts' = hcOpts { infiles = infs }
               seq (length $ show hcOpts') $ return $ hcOpts' 
        (_,_,errs) -> hetsError User (concat errs)

-- | 'checkFlags' checks all parsed Flags for sanity
checkFlags :: [Flag] -> IO [Flag]
checkFlags fs =
    let collectFlags = (collectOutDirs
                        . collectOutTypes
                        . collectVerbosity
                        . collectRawOpts
                        -- collect some more here?
                   )
    in do if (Help `elem` fs)
             then do putStrLn hetsUsage
                     exitWith ExitSuccess
             else return [] -- fall through
          if (Version `elem` fs)
             then do putStrLn ("version of hets: " ++ hetcats_version)
                     exitWith ExitSuccess
             else return [] -- fall through
          fs' <- collectFlags fs
          return fs'

-- | 'checkInFiles' checks all given InFiles for sanity
checkInFiles :: [String] -> IO [FilePath]
checkInFiles fs = 
    do ifs <- filterM checkInFile fs
       case ifs of
                []  -> return (hetsError User "No valid input file specified")
                xs  -> return xs


-- auxiliary functions: FileSystem interaction --

-- | 'checkInFile' checks a single InFile for sanity
checkInFile :: FilePath -> IO Bool
checkInFile file =
    do exists <- doesFileExist file
       perms  <- catch (getPermissions file) (\_ -> return noPerms)
       return (exists && (readable perms))

-- | 'checkOutDirs' checks a list of OutDir for sanity
checkOutDirs :: [Flag] -> IO [Flag]
checkOutDirs fs = 
    do ods <- ((filterM checkOutDir) 
               . (map (\(OutDir x) -> x))) fs
       if null ods
          then return []
          else return $ [OutDir $ head ods]

-- | 'checkOutDir' checks a single OutDir for sanity
checkOutDir :: String -> IO Bool
checkOutDir file = 
    do exists <- doesDirectoryExist file
       perms  <- catch (getPermissions file) (\_ -> return noPerms)
       return (exists && (writable perms))

-- Nil Permissions. Returned, if an Error occurred in FS-Interaction
noPerms :: Permissions
noPerms = Permissions { readable = False
                      , writable = False
                      , executable = False
                      , searchable = False
                      }

-- auxiliary functions: collect flags -- 

collectOutDirs :: [Flag] -> IO [Flag]
collectOutDirs fs =
    let (ods,fs') = partition isOutDir fs
        isOutDir (OutDir _) = True
        isOutDir _          = False
    in do ods' <- checkOutDirs ods
          return $ ods' ++ fs'

collectVerbosity :: [Flag] -> [Flag]
collectVerbosity fs =
    let (vs,fs') = partition isVerb fs
        verbosity = (sum . map (\(Verbose x) -> x)) vs
        isVerb (Verbose _) = True
        isVerb _           = False
        vfs = Verbose verbosity : fs'
    in if (Quiet `elem` fs') then Verbose 0 : fs' else
       if null vs then Verbose 1 : fs' else vfs

collectOutTypes :: [Flag] -> [Flag]
collectOutTypes fs =
    let (ots,fs') = partition isOType fs
        isOType (OutTypes _) = True
        isOType _            = False
        otypes = foldl concatOTypes [] ots
        concatOTypes = (\os (OutTypes ot) -> os ++ ot)
    in if ((null otypes) || ((Gui Only) `elem` fs'))
        then fs'
        else ((OutTypes otypes):fs')

collectRawOpts :: [Flag] -> [Flag]
collectRawOpts fs =
    let (rfs,fs') = partition isRawOpt fs
        isRawOpt (Raw _) = True
        isRawOpt _       = False
        raws = foldl concatRawOpts [] rfs
        concatRawOpts = (\os (Raw ot) -> os ++ ot)
    in if (null raws) then fs' else ((Raw raws):fs')


-- auxiliary functions: error messages --

-- | 'hetsError' is a generic Error messaging function that prints the Error
-- and usage information, if the user caused the Error
hetsError :: forall a. ErrorSource -> String -> a
hetsError User   errorString = error (errorString ++ "\n" ++ hetsUsage)
hetsError Intern errorString = error ("Internal Error: " ++ errorString)

-- | 'hetsUsage' generates usage information for the commandline
hetsUsage :: String
hetsUsage = usageInfo header options
    where header = "Usage: hets [OPTION...] file"

-- | 'putIfVerbose' prints a given String to StdOut when the given HetcatsOpts' 
-- Verbosity exceeds the given level
putIfVerbose :: HetcatsOpts -> Int -> String -> IO ()
putIfVerbose opts level str = 
    if outputToStdout opts
       then doIfVerbose opts level (putStrLn str)
    else return()

-- | 'doIfVerbose' executes a given function when the given HetcatsOpts' 
-- Verbosity exceeds the given level
doIfVerbose :: HetcatsOpts -> Int -> (IO ()) -> IO ()
doIfVerbose opts level func =
    if (verbose opts) >= level then func
        else return ()

-- | show diagnostic messages (see Result.hs), according to verbosity level
showDiags :: HetcatsOpts -> [Diagnosis] -> IO()
showDiags opts ds = do
    ioresToIO $ showDiags1 opts $ resToIORes $ Result ds Nothing
    return ()

-- | show diagnostic messages (see Result.hs), according to verbosity level
showDiags1 :: HetcatsOpts -> IOResult a -> IOResult a
showDiags1 opts res = do
  if outputToStdout opts
     then do Result ds res' <- ioToIORes $ ioresToIO res 
             ioToIORes $ sequence $ map (putStrLn . show) -- take maxdiags
                       $ filter (relevantDiagKind . diagKind) ds
             case res' of
               Just res'' -> return res''
               Nothing    -> resToIORes $ Result [] Nothing
     else res
  where relevantDiagKind FatalError = True
        relevantDiagKind Error = True
        relevantDiagKind Warning = (verbose opts) >= 2
        relevantDiagKind Hint = (verbose opts) >= 4
        relevantDiagKind Debug  = (verbose opts) >= 5
        relevantDiagKind MessageW = False


