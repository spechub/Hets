
{-| 
   
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
     - Flag und HetCATSOpts Datentyp anpassen
     - options Liste erweitern 
     - mehrere infiles zulassen
-}

{- Optionen:

Usage: hetcats [OPTION...] file ... file
  -v[Int]   --verbose[=Int]       chatty output on stderr
  -V        --version             show version number
  -h        --help                show usage information
  -i ITYPE  --input-type=ITYPE    ITYPE of input file: casl|het|tree.gen_trm
  -p        --just-parse          just parse -- skip analysis
  -O DIR    --output-dir=DIR      output DIR
  -o OTYPES --output-types=OTYPES select OTYPES of output files
  -l id     --output-logic=id     select output logic and optional logic coding
  -L DIR    --casl-libdir=DIR     CASL library directory
  -r STRING --raw=STRING          raw options for the pretty-printer
  -w        --width tex=10cm het=75 
 -- or something else for width/papersize etc?

OTYPES is a comma separated list of OTYPE
OTYPE is (pp.(het|tex|html))
         |(ast|[fh]?dg(.nax)?).(het|trm|taf|html|xml)
         |(graph.(dot|ps|davinci))
         (default: dg.taf)
-}

module Options where

import Version
import Common.Utils

import System.Directory
import System.Exit

-- import Data.Char (isSpace)
import Data.List

import Control.Monad (filterM)

import System.Console.GetOpt


-- main Datatypes --

{- | 'HetcatsOpts' describes the interpreted options -}
-- TODO: pretty-printer Options
data HetcatsOpts = 
    HcOpt { verbose  :: Int       -- greater than null to turn verbosity on
	  , intype   :: InType    -- type of the file to be read
	  , infile   :: FilePath  -- file to be read
	  , outdir   :: FilePath  -- output directory
	  , outtypes :: [OutType] -- list of output types to be generated
	  , analysis :: Bool      -- False if analysis should be skipped
	  , libdir   :: FilePath  -- CASL library directory
	  , rawoptions :: [RawOpt] -- raw options for the pretty printer
	  }
    deriving (Eq)

instance Show HetcatsOpts where
    show opts =    " --verbose="      ++ show (verbose opts)
		++ " --input-type="   ++ showInType
		++ " --output-types=" ++ showOutType
		++ " --output-dir="   ++ (outdir opts)
		++ showAnalysis
		++ " --casl-libdir="  ++ (libdir opts)
		++ showRaw (rawoptions opts)
		++ " " ++ showInFiles
	where
	showInType = show (intype opts)
	showOutType = joinWith ',' $ map show (outtypes opts)
	showAnalysis
	    | analysis opts = ""
	    | otherwise     = " --just-parse"
	showInFiles  = infile opts
	showRaw = joinWith ' ' . (map showRaw')
	showRaw' (RawAscii s) = " --raw=ascii=" ++ s
	showRaw' (RawLatex s) = " --raw=latex=" ++ s
-- these might be used when multiple infiles are implemented
--	showInType = joinWith ' ' (map show (intype opts))
--	showInFiles  = joinWith ' ' (infile opts)


{- | the default HetcatsOpts, used when nothing else is specified -}
defaultHetcatsOpts :: HetcatsOpts
defaultHetcatsOpts = 
    HcOpt { verbose = 0
	  , infile = ""
	  , intype   = Guess -- ATerm NonBAF
	  , outdir = ""
	  , outtypes = [HetCASLOut OutASTree Ascii]
            {- better default options, but 
	    the underlying functions are not yet implemented:
	  , intype   = HetCASLIn
	  , outtypes = [Global_Env [XML]]
	    -}
	  , analysis = True
	  , libdir  = ""
	  , rawoptions = []
	  }

{- | 'Flag' describes the raw options -}
data Flag = Verbose  Int         -- how verbose shall we be?
	  | Version              -- print version number
	  | Help                 -- print usage message
	  | InType   InType      -- type of input file
	  | OutDir   FilePath    -- destination directory for output files
	  | OutTypes [OutType]   -- types of output to generate
	  | Analysis Bool        -- to analyse or not to analyse
	  | LibDir   FilePath    -- CASL library directory
	  | Raw      [RawOpt]    -- raw options passed on to the pretty-printer
	    deriving (Show,Eq)

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
    , Option ['i'] ["input-type"]  (ReqArg parseInputType "ITYPE")
      "ITYPE of input file: \n\t(tree.)?gen_trm(.baf)? | het(casl)? | casl | ast(.baf)?"
    , Option ['O'] ["output-dir"]  (ReqArg parseOutputDir "DIR")
      "destination directory for output files"
    , Option ['o'] ["output-types"] (ReqArg parseOutputTypes "OTYPES")
      "OTYPES of output files, a comma seperated list of OTYPE\n\tOTYPE is (pp.(het|tex|html))\n\t\t|(ast|[fh]?dg(.nax)?).(het|trm|taf|html|xml)\n\t\t|(graph.(dot|ps|davinci))\n\t\t(default: dg.taf)"
    , Option ['p'] ["just-parse"]  (NoArg (Analysis False))
      "skip static analysis - just parse"
    , Option ['L'] ["casl-libdir"]  (ReqArg parseLibDir "DIR")
      "CASL library directory"
    , Option ['r'] ["raw"] (ReqArg parseRawOpts "RAW")
      "raw options passed to the pretty-printer \n\tRAW is (ascii|text|(la)?tex)=STRING where STRING is passed to the appropiate pretty-printer"
    ]


-- auxiliary Datatypes --

-- posible sources of errors: user input or internal errors
data ErrorSource = User | Intern
		   deriving (Show, Eq)

-- valid types of input
data InType = ATerm ATType | ASTree ATType | CASLIn | HetCASLIn | Guess
	      deriving (Show, Eq)
-- ATerm was: SML_Gen_ATerm

-- valid types of ATerms: baf or non-baf ATerms
data ATType = BAF | NonBAF
	      deriving (Show, Eq)

-- valid types of output: pretty, hetcasl or graph
data OutType = PrettyPrint PrettyType 
	     | HetCASLOut HetOutType HetOutFormat
	     | Graph GraphType
	       deriving (Show, Eq)

-- valid types of pretty-print
data PrettyType = PrettyAscii | PrettyLatex | PrettyHtml
		  deriving (Show, Eq)

-- valid types of hetcasl output
data HetOutType = OutASTree | OutDGraph Flattening Bool
		  deriving (Show, Eq)

-- valid types of DGraph types: flat, hiding or full
data Flattening = Flattened | HidingOutside | Full
		  deriving (Show, Eq)

-- valid formats of hetcasl output: ascii, term, taf, html or xml
data HetOutFormat = Ascii | Term | Taf | Html | Xml
		    deriving (Show, Eq)

-- valid types of graphs
data GraphType = Dot | PostScript | Davinci
		 deriving (Show, Eq)

-- valid types of Raw Options
data RawOpt = RawAscii String | RawLatex String
	      deriving (Show, Eq)


-- parser functions returning Flags --

-- parse the level of verbosity
parseVerbosity :: (Maybe String) -> Flag
parseVerbosity Nothing = Verbose 1
parseVerbosity (Just s)
    = case reads s of
		   [(i,"")] -> Verbose i
		   _        -> hetsError User (s ++ " is not a valid INT")

-- parse the input type 
-- TODO: maybe this can be implemented via 'instance Read InType'?
parseInputType :: String -> Flag
parseInputType "casl"             = InType CASLIn
parseInputType "hetcasl"          = InType HetCASLIn
parseInputType "het"              = InType HetCASLIn
parseInputType "gen_trm"          = InType (ATerm NonBAF)
parseInputType "tree.gen_trm"     = InType (ATerm NonBAF)
parseInputType "gen_trm.baf"      = InType (ATerm BAF)
parseInputType "tree.gen_trm.baf" = InType (ATerm BAF)
parseInputType "ast"              = InType (ASTree NonBAF)
parseInputType "ast.baf"          = InType (ASTree BAF)
parseInputType str                = error' str
    where
    error' s = hetsError User (s ++ " is not a valid ITYPE")

-- parse the output types 
parseOutputTypes :: String -> Flag
parseOutputTypes str
    | ',' `elem` str = OutTypes $ 
		       (map maybeOType . map parseOutType . splitOn ',') str
    | otherwise = case (parseOutType str) of
					  (Just ts) -> OutTypes [ts]
					  Nothing   -> error' str
    where
    maybeOType (Just t) = t
    maybeOType Nothing  = error' str
    error' s = hetsError User (s ++ " is not a valid OTYPE")

-- parse a single output type from a string
parseOutType :: String -> Maybe OutType
parseOutType s
    | "pp."    `isPrefixOf` s =
	parseOutType' (getPrettyType $ drop 3 s) PrettyPrint
    | "graph." `isPrefixOf` s =
	parseOutType' (getGraphType $ drop 6 s) Graph
    | "ast."   `isPrefixOf` s =
	parseOutType' (getOutFormat $ drop 4 s) (HetCASLOut OutASTree)
    | "fdg.nax."   `isPrefixOf` s =
	parseOutType' (getOutFormat $ drop 8 s) 
		      (HetCASLOut $ OutDGraph Flattened True)
    | "fdg."   `isPrefixOf` s =
	parseOutType' (getOutFormat $ drop 4 s)
		      (HetCASLOut $ OutDGraph Flattened False)
    | "hdg.nax."   `isPrefixOf` s =
	parseOutType' (getOutFormat $ drop 8 s) 
		      (HetCASLOut $ OutDGraph HidingOutside True)
    | "hdg."   `isPrefixOf` s =
	parseOutType' (getOutFormat $ drop 4 s)
		      (HetCASLOut $ OutDGraph HidingOutside False)
    | "dg.nax."    `isPrefixOf` s =
	parseOutType' (getOutFormat $ drop 7 s)
		      (HetCASLOut $ OutDGraph Full True)
    | "dg."    `isPrefixOf` s =
	parseOutType' (getOutFormat $ drop 3 s)
		      (HetCASLOut $ OutDGraph Full False)
    | otherwise               = Nothing
    where
    getPrettyType "het"  = Just PrettyAscii
    getPrettyType "tex"  = Just PrettyLatex
    getPrettyType "html" = Just PrettyHtml
    getPrettyType _      = Nothing
    getGraphType "dot"     = Just Dot
    getGraphType "ps"      = Just PostScript
    getGraphType "davinci" = Just Davinci
    getGraphType _         = Nothing
    getOutFormat "het"  = Just Ascii
    getOutFormat "taf"  = Just Taf
    getOutFormat "trm"  = Just Term
    getOutFormat "html" = Just Html
    getOutFormat "xml"  = Just Xml
    getOutFormat _      = Nothing
    parseOutType' getter typ =
	case getter of
		    (Just t) -> Just (typ t)
		    Nothing  -> Nothing

-- parse raw options
parseRawOpts :: String -> Flag
parseRawOpts s 
    | "ascii=" `isPrefixOf` s = Raw $ [RawAscii (drop 6 s)]
    | "text="  `isPrefixOf` s = Raw $ [RawAscii (drop 5 s)]
    | "latex=" `isPrefixOf` s = Raw $ [RawLatex (drop 6 s)]
    | "tex="   `isPrefixOf` s = Raw $ [RawLatex (drop 4 s)]
    | otherwise = error'
    where
    error' = hetsError User "RAW is (ascii|text|(la)?tex)=STRING"

-- parse the output directory 
parseOutputDir :: String -> Flag
parseOutputDir s = OutDir s

-- parse casl library directory
parseLibDir :: String -> Flag
parseLibDir s = LibDir s


-- main functions --

-- main function, parses ARGV to our desired HetcatsOpts
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
    case (getOpt Permute options argv) of
        (opts,non_opts,[]) ->
	    do useOpts  <- formOpts opts
	       ourOpts  <- return (useOpts defaultHetcatsOpts)
	       ourIns   <- formInFiles non_opts
	       optsWithIns <- return $
			      map (makeOpts ourOpts) ourIns
	       guessedOpts <- return $
			      map (guessIT . guessOD) optsWithIns
	       return (head guessedOpts)
        (_,_,errs) -> fail (concat errs ++ hetsUsage)

formOpts :: [Flag] -> IO (HetcatsOpts -> HetcatsOpts)
formOpts fs = do if (hasHelp fs)
		    then do putStrLn hetsUsage
			    exitWith ExitSuccess
		    else return () -- fall through
		 if (hasVersion fs)
		    then do putStrLn ("version of hets: " 
				      ++ hetcats_version)
			    exitWith ExitSuccess
		    else return () -- fall through
		 fs' <- (collectOutDirs
			 . collectOutTypes
			 . collectVerbosity
			 . collectRawOpts
			 -- collect some more here
			) fs
		 return $ extractOpts fs'
    where
    hasVersion xs = Version `elem` xs
    hasHelp xs = Help `elem` xs

extractOpts :: [Flag] -> HetcatsOpts -> HetcatsOpts
extractOpts ((Version):xs)    opts = extractOpts xs opts
extractOpts ((Help):xs)       opts = extractOpts xs opts
extractOpts ((Verbose x):xs)  opts = extractOpts xs opts { verbose = x }
extractOpts ((InType x):xs)   opts = extractOpts xs opts { intype = x }
extractOpts ((OutDir x):xs)   opts = extractOpts xs opts { outdir = x }
extractOpts ((OutTypes x):xs) opts = extractOpts xs opts { outtypes = x }
extractOpts ((Analysis x):xs) opts = extractOpts xs opts { analysis = x }
extractOpts ((LibDir x):xs)   opts = extractOpts xs opts { libdir = x }
extractOpts ((Raw x):xs)      opts = extractOpts xs opts { rawoptions = x }
extractOpts [] opts = opts
extractOpts _ _ = hetsError Intern "Unknown Error in extractOpts"

formInFiles :: [String] -> IO [FilePath]
formInFiles fs = do ifs <- checkInFiles fs
		    case ifs of
			     []  -> return (hetsError User 
					    "No valid input file specified")
			     xs  -> return xs

guessIT :: HetcatsOpts -> HetcatsOpts
guessIT opts 
    | (intype opts) == Guess = opts { intype = guessInType (infile opts) }
    | otherwise              = opts

guessOD :: HetcatsOpts -> HetcatsOpts
guessOD opts 
    | null (outdir opts) = opts { outdir = dirname (infile opts) }
    | otherwise          = opts


-- auxiliary functions: FileSystem interaction --

-- sanity check for all input files
checkInFiles :: [FilePath] -> IO [FilePath]
checkInFiles = filterM checkInFile

-- sanity check for a single input file
checkInFile :: FilePath -> IO Bool
checkInFile file = do exists <- doesFileExist file
		      perms  <- catch (getPermissions file)
				(\_ -> return noPerms)
		      if (exists && (readable perms))
			 then return True
			 else return False

-- sanity check for all output directories
checkOutDirs :: [Flag] -> IO [Flag]
checkOutDirs fs = 
    do ods <- ((filterM checkOutDir) . (map unOutDir)) fs
       if null ods
	  then return []
	  else return $ [OutDir $ head ods]
    where
    unOutDir (OutDir x) = x
    unOutDir _          = hetsError Intern "Unknown error in checkOutDirs"

-- sanity check for a single output directory
checkOutDir :: String -> IO Bool
checkOutDir file = do exists <- doesDirectoryExist file
		      perms  <- catch (getPermissions file)
				(\_ -> return noPerms)
		      if (exists && (writable perms))
			 then return True
			 else return False

noPerms :: Permissions
noPerms = Permissions { readable = False
		      , writable = False
		      , executable = False
		      , searchable = False
		      }


-- auxiliary functions: collect flags -- 

collectVerbosity :: [Flag] -> [Flag]
collectVerbosity fs =
    let (vs,fs') = partition isVerb fs
	verbosity = sum $ map extractVerbosity vs
    in (Verbose verbosity):fs'
    where
    isVerb (Verbose _) = True
    isVerb _           = False
    extractVerbosity (Verbose x) = x
    extractVerbosity _ = hetsError Intern "Unknown Error in collectVerbosity"

collectOutTypes :: [Flag] -> [Flag]
collectOutTypes fs =
    let (ots,fs') = partition isOType fs
	otypes = foldl concatOTypes [] ots
	otypes' = if (null otypes) then [] else [(OutTypes otypes)]
    in otypes' ++ fs'
    where
    isOType (OutTypes _) = True
    isOType _            = False
    concatOTypes os (OutTypes ot) = os ++ ot
    concatOTypes _ _ = hetsError Intern "Unknown Error in collectOutTypes"

-- TODO: if there were OutDirs specified, and none of them are sane,
-- we should warn the user instead of sticking to our defaults!
collectOutDirs :: [Flag] -> IO [Flag]
collectOutDirs fs =
    do let (ods,fs') = partition isOutDir fs
       ods' <- checkOutDirs ods
       return $ ods' ++ fs'
    where
    isOutDir (OutDir _) = True
    isOutDir _          = False

collectRawOpts :: [Flag] -> [Flag]
collectRawOpts fs =
    let (rfs,fs') = partition isRawOpt fs
	raws = foldl concatRawOpts [] rfs
	raws' = if (null raws) then [] else [(Raw raws)]
    in raws' ++ fs'
    where
    isRawOpt (Raw _) = True
    isRawOpt _       = False
    concatRawOpts os (Raw ot) = os ++ ot
    concatRawOpts _ _ = hetsError Intern "Unknown Error in collectRawOpts"

makeOpts :: HetcatsOpts -> FilePath -> HetcatsOpts
makeOpts opts file = opts { infile = file }

guessInType :: FilePath -> InType
guessInType _ = ATerm NonBAF


-- auxiliary functions: error messages --

-- generic error message function for internal or user errors
-- user errors also print our usage information, 
-- as presumably something went wrong while parsing the input flags
hetsError :: forall a. ErrorSource -> String -> a
hetsError User errorString = error (errorString ++ "\n" ++ hetsUsage)
hetsError Intern errorString = error ("Internal Error: " ++ errorString)

-- generates usage information for the commandline
hetsUsage :: String
hetsUsage = usageInfo header options
    where header = "Usage: hetcats [OPTION...] file"

-- prints a list of all recognized options passed to the command line
-- non really an error Message, but anyway...
printOpts :: HetcatsOpts -> IO ()
printOpts opts = 
    let optString = "Options: " ++ (show opts)
    in putStrLn optString
