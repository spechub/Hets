
{- 
| 
 > HetCATS/hetcats/Options.hs
 > $Id$
 > Author: Martin Kühl
 > Year:   2002

   Datatypes for options, a list of options hetcats understands.
   Useful functions to parse and check the user-provided functions
   and for filling in default values.

   A record datatype for fast and easy access and modification
   extension of the options. 

-}

{- TODO:
   -- parse the input type via 'instance Read InType'?
   -- there's got to be a better way to realize parseOutType
   -- an Error should be raised when more than one OutDir were specified,
      or when the OutDir wasn't approved sane
   -- implement Read instance for some (all?) Types of Flags
-}

{- Optionen:

Usage: hetcats [OPTION...] file ... file
  -v[Int]   --verbose[=Int]       chatty output on stderr
  -V        --version             print version number and exit
  -h        --help, --usage       print usage information and exit
  -i ITYPE  --input-type=ITYPE    ITYPE of input file: 
            (tree.)?gen_trm(.baf)? | het(casl)? | casl | ast(.baf)?
  -p        --just-parse          skip analysis - just parse
  -O DIR    --output-dir=DIR      destination directory for output files
  -o OTYPES --output-types=OTYPES OTYPES of output files, a comma seperated list of OTYPE
            OTYPE is (pp.(het|tex|html))
            |(ast|[fh]?dg(.nax)?).(het|trm|taf|html|xml)
            |(graph.(dot|ps|davinci))
            (default: dg.taf)
?  -l id     --output-logic=id     select output logic and optional logic coding
                mit Parsec (Token.simpleId) parsen
  -L DIR    --casl-libdir=DIR     CASL library directory
  -r RAW    --raw=RAW             raw options passed to the pretty-printer
            RAW is (ascii|text|(la)?tex)=STRING where STRING is passed to the appropiate pretty-printer

  -s        --just-structure      skip basic analysis - just do structured analysis
  -g        --gui                 use graphical user interface
-}

module Options where

import Version
import Common.Utils

import System.Directory
import System.Exit

import Data.List
import Control.Monad (filterM)

import System.Console.GetOpt


-- main Datatypes --

{- | 'HetcatsOpts' describes the interpreted options -}
data HetcatsOpts = 
    HcOpt { verbose  :: Int        -- greater than null to turn verbosity on
          , analysis :: Bool       -- False if analysis should be skipped
          , intype   :: InType     -- type of the file to be read
          , outtypes :: [OutType]  -- list of output types to be generated
          , rawopts  :: [RawOpt]   -- raw options for the pretty printer
          , libdir   :: FilePath   -- CASL library directory
          , outdir   :: FilePath   -- output directory
          , infiles  :: [FilePath] -- files to be read
          }
    deriving (Eq)

instance Show HetcatsOpts where
    show opts =    " --verbose="      ++ show (verbose opts)
                ++ showAnalysis (analysis opts)
                ++ " --input-type="   ++ show (intype opts)
                ++ " --output-types=" ++ showOutTypes (outtypes opts)
                ++ " " ++ showRaw (rawopts opts)
                ++ " --casl-libdir="  ++ (libdir opts)
                ++ " --output-dir="   ++ (outdir opts)
                ++ " " ++ showInFiles (infiles opts)
        where
        showAnalysis x = if x then " --just-parse" else ""
        showInFiles  = joinWith ' '
        showOutTypes = joinWith ',' . map show
        showRaw = joinWith ' ' . map showRaw'
        showRaw' (RawAscii s) = "--raw=ascii=" ++ s
        showRaw' (RawLatex s) = "--raw=latex=" ++ s

{- | incorporates a Flag into a setof HetcatsOpts -}
makeOpts :: HetcatsOpts -> Flag -> HetcatsOpts
makeOpts opts (Version)    = opts -- skipped
makeOpts opts (Help)       = opts -- skipped
makeOpts opts (Verbose x)  = opts { verbose = x }
makeOpts opts (InType x)   = opts { intype = x }
makeOpts opts (OutTypes x) = opts { outtypes = x }
makeOpts opts (OutDir x)   = opts { outdir = x }
makeOpts opts (Analysis x) = opts { analysis = x }
makeOpts opts (LibDir x)   = opts { libdir = x }
makeOpts opts (Raw x)      = opts { rawopts = x }
makeOpts _     x           = hetsError Intern ("unrecognized Flag: " ++ (show x))

{- | the default HetcatsOpts, used when nothing else is specified -}
defaultHetcatsOpts :: HetcatsOpts
defaultHetcatsOpts = 
    HcOpt { verbose  = 1
          , analysis = True
          , intype   = GuessIn
          , outtypes = [HetCASLOut OutASTree OutAscii]
            {- better default options, but 
            the underlying functions are not yet implemented:
          , outtypes = [HetCASLOut OutASTree OutXml]
            -}
          , rawopts  = []
          , libdir   = ""
          , outdir   = ""
          , infiles  = []
          }

{- | 'Flag' describes the raw options -}
data Flag = Verbose  Int         -- how verbose shall we be?
          | Version              -- print version number
          | Help                 -- print usage message
          | Analysis Bool        -- to analyse or not to analyse
          | InType   InType      -- type of input file
          | OutTypes [OutType]   -- types of output to generate
          | Raw      [RawOpt]    -- raw options passed on to the pretty-printer
          | LibDir   FilePath    -- CASL library directory
          | OutDir   FilePath    -- destination directory for output files
            deriving (Show,Eq)

data InType = ATermIn ATType | ASTreeIn ATType | CASLIn | HetCASLIn | GuessIn
              deriving (Show, Eq)

data ATType = BAF | NonBAF
              deriving (Show, Eq)

data OutType = PrettyOut PrettyType 
             | HetCASLOut HetOutType HetOutFormat
             | GraphOut GraphType
               deriving (Show, Eq)

data PrettyType = PrettyAscii | PrettyLatex | PrettyHtml
                  deriving (Show, Eq)

data HetOutType = OutASTree | OutDGraph Flattening Bool
                  deriving (Show, Eq)

data Flattening = Flattened | HidingOutside | Full
                  deriving (Show, Eq)

data HetOutFormat = OutAscii | OutTerm | OutTaf | OutHtml | OutXml
                    deriving (Show, Eq)

data GraphType = Dot | PostScript | Davinci
                 deriving (Show, Eq)

data RawOpt = RawAscii String | RawLatex String
              deriving (Show, Eq)

-- posible sources of errors: user input or internal errors
data ErrorSource = User | Intern
                   deriving (Show, Eq)

{- | 'options' describes all available options and generates usage information
-}
options :: [OptDescr Flag]
options =
    [ Option ['v'] ["verbose"] (OptArg parseVerbosity "Int")
      "chatty output on stderr"
    , Option ['V'] ["version"] (NoArg Version)
      "print version number and exit"
    , Option ['h'] ["help", "usage"] (NoArg Help)
      "print usage information and exit"
    , Option ['i'] ["input-type"]  (ReqArg parseInType "ITYPE")
      "ITYPE of input file: \n\t(tree.)?gen_trm(.baf)? | het(casl)? | casl | ast(.baf)?"
    , Option ['O'] ["output-dir"]  (ReqArg (\x -> OutDir x) "DIR")
      "destination directory for output files"
    , Option ['o'] ["output-types"] (ReqArg parseOutTypes "OTYPES")
      "OTYPES of output files, a comma seperated list of OTYPE\n\tOTYPE is (pp.(het|tex|html))\n\t\t|(ast|[fh]?dg(.nax)?).(het|trm|taf|html|xml)\n\t\t|(graph.(dot|ps|davinci))\n\t\t(default: dg.taf)"
    , Option ['p'] ["just-parse"]  (NoArg (Analysis False))
      "skip static analysis - just parse"
    , Option ['L'] ["casl-libdir"]  (ReqArg (\x -> LibDir x) "DIR")
      "CASL library directory"
    , Option ['r'] ["raw"] (ReqArg parseRawOpts "RAW")
      "raw options passed to the pretty-printer \n\tRAW is (ascii|text|(la)?tex)=STRING where STRING is passed to the appropiate pretty-printer"
    ]


-- parser functions returning Flags --

-- parse the level of verbosity
parseVerbosity :: (Maybe String) -> Flag
parseVerbosity Nothing = Verbose 1
parseVerbosity (Just s)
    = case reads s of
                   [(i,"")] -> Verbose i
                   _        -> hetsError User (s ++ " is not a valid INT")

-- parse the input type 
parseInType :: String -> Flag
parseInType = InType . parseInType1

parseInType1 :: String -> InType
parseInType1 "casl"             = CASLIn
parseInType1 "hetcasl"          = HetCASLIn
parseInType1 "het"              = HetCASLIn
parseInType1 "gen_trm"          = ATermIn NonBAF
parseInType1 "tree.gen_trm"     = ATermIn NonBAF
parseInType1 "gen_trm.baf"      = ATermIn BAF
parseInType1 "tree.gen_trm.baf" = ATermIn BAF
parseInType1 "ast"              = ASTreeIn NonBAF
parseInType1 "ast.baf"          = ASTreeIn BAF
parseInType1 str                = hetsError User
                                   (str ++ " is not a valid ITYPE")

-- parse the output types 
parseOutTypes :: String -> Flag
parseOutTypes str
    | ',' `elem` str = OutTypes $ 
                       (map maybeOType . map parseOutType . splitOn ',') str
    | otherwise = case (parseOutType str) of
                                          (Just ts) -> OutTypes [ts]
                                          Nothing   -> error' str
    where
    maybeOType = maybe (error' str) id
    error' s = hetsError User (s ++ " is not a valid OTYPE")

-- parse a single output type from a string
parseOutType :: String -> Maybe OutType
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
    | otherwise               = Nothing
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
                    (Just t) -> Just (typ t)
                    Nothing  -> Nothing

-- parse raw options
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

guessInType :: FilePath -> InType
guessInType file = 
    case fileparse ["casl","hetcasl","het","gen_trm","tree.gen_trm",
                    "gen_trm.baf","tree.gen_trm.baf","ast","ast.baf"]
         file of
      (_,_,Just suf) -> parseInType1 suf
      (_,_,Nothing)  -> hetsError User $
                        "InType of " ++ file ++ " unclear, please specify"

-- main functions --

-- main function, parses ARGV to our desired HetcatsOpts
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
    case (getOpt Permute options argv) of
        (opts,non_opts,[]) ->
            do flags <- checkFlags opts
               infs  <- checkInFiles non_opts
               hcOpts <- return $ 
                         foldr (flip makeOpts) defaultHetcatsOpts flags
               return $ hcOpts { infiles = infs }
        (_,_,errs) -> hetsError User (concat errs)

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

checkInFiles :: [String] -> IO [FilePath]
checkInFiles fs = 
    do ifs <- filterM checkInFile fs
       case ifs of
                []  -> return (hetsError User "No valid input file specified")
                xs  -> return xs


-- auxiliary functions: FileSystem interaction --

-- sanity check for a single input file
checkInFile :: FilePath -> IO Bool
checkInFile file =
    do exists <- doesFileExist file
       perms  <- catch (getPermissions file) (\_ -> return noPerms)
       return (exists && (readable perms))

-- sanity check for all output directories
checkOutDirs :: [Flag] -> IO [Flag]
checkOutDirs fs = 
    do ods <- ((filterM checkOutDir) 
               . (map (\(OutDir x) -> x))) fs
       if null ods
          then return []
          else return $ [OutDir $ head ods]

-- Sanity Check For A Single Output Directory
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
    in (Verbose verbosity):fs'

collectOutTypes :: [Flag] -> [Flag]
collectOutTypes fs =
    let (ots,fs') = partition isOType fs
        isOType (OutTypes _) = True
        isOType _            = False
        otypes = foldl concatOTypes [] ots
        concatOTypes = (\os (OutTypes ot) -> os ++ ot)
    in if (null otypes) then fs' else ((OutTypes otypes):fs')

collectRawOpts :: [Flag] -> [Flag]
collectRawOpts fs =
    let (rfs,fs') = partition isRawOpt fs
        isRawOpt (Raw _) = True
        isRawOpt _       = False
        raws = foldl concatRawOpts [] rfs
        concatRawOpts = (\os (Raw ot) -> os ++ ot)
    in if (null raws) then fs' else ((Raw raws):fs')


-- auxiliary functions: error messages --

-- generic error message function for internal or user errors
-- user errors also print our usage information, 
-- as presumably something went wrong while parsing the input flags
hetsError :: forall a. ErrorSource -> String -> a
hetsError User   errorString = error (errorString ++ "\n" ++ hetsUsage)
hetsError Intern errorString = error ("Internal Error: " ++ errorString)

-- generates usage information for the commandline
hetsUsage :: String
hetsUsage = usageInfo header options
    where header = "Usage: hetcats [OPTION...] file"

-- prints a string on a certain minimum verbosity level
putIfVerbose :: HetcatsOpts -> Int -> String -> IO ()
putIfVerbose opts level str =
    if (verbose opts >= level) then putStrLn str
        else return ()

-- execs a function on a certain minimum verbosity level
doIfVerbose :: HetcatsOpts -> Int -> (IO ()) -> IO ()
doIfVerbose opts level func =
    if (verbose opts) >= level then func
        else return ()

