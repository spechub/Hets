
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
     - Posix Spezifikation zu command line interfaces \/
     - Dokumentation zu System.Console.GetOpt vom ghc \/
     - Flag und HetCATSOpts Datentyp anpassen \/
     - options Liste erweitern 
     - parse funktionen schreiben \/
     - form_opt_rec anpassen 
     - perm_infile und check_in_file implemetieren \/
-}

{- Optionen:

Usage: hetcats [OPTION...] file ... file
  -v[Int]  --verbose[=Int]      chatty output on stderr
  -V       --version            show version number
  -h       --help               show usage information
  -i ITYPE  --input-type=ITYPE  ITYPE of input file: casl|het|tree.gen_trm
  -p       --just-parse         just parse -- skip analysis
  -O DIR   --output-dir=DIR     output DIR
  -o OTYPES  --output-types=OTYPES  select OTYPES of output files
  -l id    --output-logic=id    select output logic and optional logic coding
  -L DIR   --casl-libdir=DIR    CASL library directory
  -w --width tex=10cm het=75

OTYPES is a comma separated list of OTYPE
OTYPE is (pp.(het|tex|html))|(ast|[fh]?dg(.nax)?).(het|trm|taf|html|xml)|
         (graph.(dot|ps|davinci))
         (default: dg.taf)
-}

module Options where

import Version
import Common.Utils

import System.Directory
import System.Exit

-- import Data.Char (isSpace) -- unused...
import Data.List

import Control.Monad (filterM)

import System.Console.GetOpt


-- main Datatypes --

{- | 'HetcatsOpts' describes the interpreted options -}
-- TODO: pretty-printer Options
data HetcatsOpts = 
    HcOpt { verbose  :: Int       -- greater than null to turn verbosity on
	  , infile   :: FilePath  -- file to be read
	  , intype   :: InType    -- type of the file to be read
	  , outdir   :: FilePath  -- output directory
	  , outtypes :: [OutType] -- list of output types to be generated
	  , analysis :: Bool      -- False if analysis should be skipped
	  , libdir   :: FilePath  -- CASL library directory
	  , rawoptions :: [Flag]
	  } deriving (Show,Eq)

{- | the default HetcatsOpts, used when nothing else is specified -}
defaultHetcatsOpts :: HetcatsOpts
defaultHetcatsOpts = 
    HcOpt { verbose = 0
	  , infile = ""
	  , intype   = ATerm NonBAF
	  , outdir = "."
	    -- ...or like cats: same as that of the input file
	    -- might be done with an extra constructor
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
--	  | Analysis [AnaFlag]   -- might as well be a Bool...
	  | Pretty   [String]    -- options passed to the pretty-printer
	  | LibDir   FilePath    -- CASL library directory
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
    , Option ['i'] ["input-type"]  (ReqArg parseInputType "TYPE")
      "TYPE of input file: tree.gen_trm(_baf)? | het(casl)? | casl"
    , Option ['O'] ["output-dir"]  (ReqArg parseOutputDir "DIR")
      "destination directory for output files"
    , Option ['o'] ["output-types"] (ReqArg parseOutputTypes "TYPE")
      "TYPE of output files: hetcasl-latex | hetcasl-ascii | global-env"
    , Option ['p'] ["just-parse"]  (NoArg (Analysis False))
      "skip static analysis - just parse"
    , Option ['L'] ["casl-libdir"]  (ReqArg parseLibDir "DIR")
      "CASL library directory"
    ]


-- auxiliary Datatypes --

-- posible sources of errors: user input or internal errors
data ErrorSource = User | Intern
		   deriving (Show, Eq)

-- valid types of input
data InType = ATerm ATType | ASTree ATType | CASLIn | HetCASLIn
	      deriving (Show, Eq)
-- was: SML_Gen_ATerm

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


-- parser functions returning Flags --

-- parse the level of verbosity
parseVerbosity :: (Maybe String) -> Flag
parseVerbosity Nothing = Verbose 1
parseVerbosity (Just s)
    = case reads s of
		   [(i,"")] -> Verbose i
		   _        -> error'
    where
    error' = hetsError User (s ++ " is not a valid INT")

-- parse the input type 
-- TODO: this one is _ugly_ ...
-- ... but this seems to be the easiest way
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
		       (map maybeOType . map parseOType . splitOn ',') str
    | otherwise = case (parseOType str) of
					(Just ts) -> OutTypes [ts]
					Nothing   -> error' str
    where
    error' s = hetsError User (s ++ " is not a valid OTYPE")
    maybeOType (Just t) = t
    maybeOType Nothing  = error' str

-- parse a single output type from a string
parseOType :: String -> Maybe OutType
parseOType s
    | "pp."    `isPrefixOf` s =
	parseOType' (getPrettyType $ drop 3 s) PrettyPrint
    | "graph." `isPrefixOf` s =
	parseOType' (getGraphType $ drop 6 s) Graph
    | "ast."   `isPrefixOf` s =
	parseOType' (getOutFormat $ drop 4 s) (HetCASLOut OutASTree)
    | "fdg.nax."   `isPrefixOf` s =
	parseOType' (getOutFormat $ drop 8 s) 
		      (HetCASLOut $ OutDGraph Flattened True)
    | "fdg."   `isPrefixOf` s =
	parseOType' (getOutFormat $ drop 4 s)
		      (HetCASLOut $ OutDGraph Flattened False)
    | "hdg.nax."   `isPrefixOf` s =
	parseOType' (getOutFormat $ drop 8 s) 
		      (HetCASLOut $ OutDGraph HidingOutside True)
    | "hdg."   `isPrefixOf` s =
	parseOType' (getOutFormat $ drop 4 s)
		      (HetCASLOut $ OutDGraph HidingOutside False)
    | "dg.nax."    `isPrefixOf` s =
	parseOType' (getOutFormat $ drop 7 s)
		      (HetCASLOut $ OutDGraph Full True)
    | "dg."    `isPrefixOf` s =
	parseOType' (getOutFormat $ drop 3 s)
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
{-    getOutFormat s  
	| "nax." `isPrefixOf` s = 
	    parseOType' (getOutFormat' $ drop 4 s) (True)
	| otherwise             = 
	    parseOType' (getOutFormat' s) (False) -} -- too confusing ;)
    getOutFormat "het"  = Just Ascii
    getOutFormat "taf"  = Just Term
    getOutFormat "trm"  = Just Taf
    getOutFormat "html" = Just Html
    getOutFormat "xml"  = Just Xml
    getOutFormat _      = Nothing
    parseOType' getter typ =
	case getter of
		    (Just t) -> Just (typ t)
		    Nothing  -> Nothing

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
        (opts,non_opts,[]) -> do withOpts <- formOpts opts
				 withIns  <- formInFiles non_opts
				 return $ (withIns . withOpts) 
					defaultHetcatsOpts
        (_,_,errs) -> fail (concat errs ++ hetsUsage)

-- TODO!
formInFiles :: [String] -> IO (HetcatsOpts -> HetcatsOpts)
formInFiles fs = do ifs <- checkInFiles fs
		    case ifs of
			     [x] -> return (inFile x)
			     []  -> return $ 
				    error' "No valid input file specified"
			     _   -> return $ error'
				    "Only one input file may be specified at a time"
-- at least for now - will be implemented later
    where
    inFile x opts = opts { infile = x }
    error' e = (\_ -> hetsError User e)

-- TODO: implement some kind of sequence...
formOpts :: [Flag] -> IO (HetcatsOpts -> HetcatsOpts)
formOpts fs = do if (hasHelp fs)
		    then do putStrLn hetsUsage
			    exitWith ExitSuccess
		    else return () -- fall through
		 if (hasVersion fs)
		    then do putStrLn ("version of hetcats: " 
				      ++ hetcats_version)
			    exitWith ExitSuccess
		    else return () -- fall through
		 fs' <- return $ (collectOutTypes . collectVerbosity) fs
		 checkOutDirs fs'
		 return (\x -> x) -- TODO!
    where
    hasVersion xs = Version `elem` xs
    hasHelp xs = Help `elem` xs


-- auxiliary functions: FileSystem interaction --

-- sanity check for all input files
checkInFiles :: [FilePath] -> IO [FilePath]
checkInFiles = filterM checkInFile

-- sanity check for a single input file
checkInFile :: FilePath -> IO Bool
checkInFile file = do exists <- doesFileExist file
		      perms  <- catch (getPermissions file)
				(\_ -> return
 				 (Permissions { readable = False
					      , writable = False
					      , executable = False
					      , searchable = False
					      } ))
		      if (exists && (readable perms))
			 then return True
			 else return False

-- sanity check for all output directories
checkOutDirs :: [Flag] -> IO [FilePath]
checkOutDirs = (filterM checkOutDir) . (map extrOutDir) . (filter isOutDir)
    where
    isOutDir (OutDir _ ) = True
    isOutDir _           = False
    extrOutDir (OutDir x) = x
    extrOutDir _          = hetsError Intern "error in checkOutDirs"

-- sanity check for a single output directory
checkOutDir :: String -> IO Bool
checkOutDir file = do exists <- doesDirectoryExist file
		      perms  <- catch (getPermissions file)
				(\_ -> return
				 (Permissions { readable = False
					      , writable = False
					      , executable = False
					      , searchable = False
					      } ))
		      if (exists && (writable perms))
			 then return True
			 else return False


-- auxiliary functions: collect flags -- 
-- should work kinda like sorting -- TODO!

collectVerbosity :: [Flag] -> [Flag]
collectVerbosity fs = fs

collectOutTypes :: [Flag] -> [Flag]
collectOutTypes fs = fs

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


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
{-
-- sets the corect output type(s)
out_types :: String -> Flag
out_types s | ',' `elem` s = case merge_out_types $ split_types s of
			     [x] -> x
			     _ -> error "internal error after merging OutTypes"
	    | s == "hetcasl-latex"  = OutTypes [HetCASLOut Latex]
	    | s == "hetcasl-ascii"  = OutTypes [HetCASLOut Ascii]
	    | s == "global-env-xml" = OutTypes [Global_Env XML]
	    | otherwise = error $ hetcats_error ("unknown output type: " ++ s)
    where split_types = map out_types . splitOn ',' 
-}
{-
-- merges [OutTypes[a]] into OutTypes[a]
merge_out_types :: [Flag] -> [Flag]
merge_out_types flags = 
    let (ots,flags') = partition is_out_type flags 
	is_out_type f = case f of
			OutTypes _ -> True
			_          -> False
	concatTypes l ot = case ot of
			   OutTypes l' -> l++l'
			   _ -> error "internal error in merging OutTypes"
	ots' = foldl concatTypes [] ots
    in if null ots' then flags' else (OutTypes ots'):flags'  
-}
{-
-- This function parses all options
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
   case (getOpt Permute options argv) of
      (opts,non_opts,[]  ) -> form_opt_rec (merge_out_types opts) non_opts
      (_,_,errs) -> fail (concat errs ++ hetcats_usage)
-}
{-
form_opt_rec :: [Flag] -> [String] -> IO HetcatsOpts
form_opt_rec flags inp_files = 
    let req_in_file = case inp_files of
		      [] -> error $ "one input filename is required\n" ++
				    hetcats_usage
		      [x] -> x
		      _   -> error $ "Only one input filename allowed\n" ++ 
				     hetcats_usage
	verb' = foldl collect_verb 0 flags
	    where collect_verb v f = case f of 
				     Verbose i -> i + v
				     _       -> v
	outTypes = if null flags then
		      defaultOt
		   else case head flags of
		          OutTypes ot -> ot
			  _           -> defaultOt
	    where defaultOt = outtypes default_HetcatsOpts
    in do if Help `elem` flags -- called with --help
	     then do putStrLn $ "\n" ++ hetcats_usage
		     exitWith ExitSuccess
	     else if Version `elem` flags -- called with --version
		  then do putStrLn $ "version of hetcats: " ++ hetcats_version
		          exitWith ExitSuccess
	          else return () -- called w/o --help or --version
	  in_file <- check_in_file req_in_file
	  od <- check_out_dir flags in_file
	  return $ default_HetcatsOpts { infile  = in_file 
				       , outdir  = od 
				       , verbose = verb'
				       , rawoptions = flags
				       , outtypes = outTypes
				       }
-}
{-
-- some suffixes to try in turn 
-- TODO: implement perm_in_file
perm_in_file :: FilePath -> [FilePath]
perm_in_file f = [f]

-- check if one of the possible files exists and is readable
-- TODO: implement check_in_file
check_in_file :: FilePath -> IO FilePath
check_in_file = return . head . perm_in_file
-}

-- check the output directory and choose a default one if none is specified
-- TODO: implement the checking of the out_dir
{-
check_out_dir :: [Flag] -> FilePath -> IO FilePath
check_out_dir flags in_file = 
    let ods = filter (\f -> case f of
		            OutDir _ -> True
		            _ -> False) flags
	default_dir = dirname in_file
	od = if null ods then 
	        if    null default_dir 
		   || all isSpace default_dir
		then 
		   "."
		else
		   default_dir
	     else 
	        ( \ (OutDir fp) -> fp) $ last ods
    in do od' <- if od == "." then
                    getCurrentDirectory
	         else
		    return od
	  existsDir <- doesDirectoryExist od'
          perms <- if existsDir then getPermissions od'
		   else error $ "requested nonexistent output directory \"" ++ 
			       od' ++ "\"\n" ++ hetcats_usage
	  if existsDir && writable perms then 
	     return od'
	   else
	     fail $ "no writeable output directory available\n" ++
		    hetcats_usage
-}
