
{-| 
   
 > HetCATS/hetcats/Options.hs
 > $Id$
 > Author: Klaus Lüttich
 > Year:   2002

   Datatypes for options, a list of options hetcats understands.
   Useful functions to parse and check the user-provided functions
   and for filling in default values.

   A record datatype for fast and easy access and modification \/
   extension of the options. 

   TODO:
     - Posix Spezifikation zu command line interfaces \/
     - Dokumentation zu System.Console.GetOpt vom ghc \/
     - Flag und HetCATSOpts Datentyp anpassen \/
     - options Liste erweitern
     - parse funktionen schreiben
     - form_opt_rec anpassen
     - perm_infile und check_in_file implemetieren

   Optionen:

Usage: hetcats [OPTION...] file ... file
  -v[Int]  --verbose[=Int]      chatty output on stderr
  -V       --version            show version number
  -h       --help               show usage information
  -i ITYPE  --input-type=ITYPE    ITYPE of input file: casl | het | tree.gen_trm
  -p       --just-parse         just parse -- no analysis
  -O DIR   --output-dir=DIR     output DIR
  -o OTYPES  --output-types=OTYPES  select OTYPES of output files
...?  -l id id? --output-logic=id id?  select output logic and optional logic coding
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

import Data.Char (isSpace)
import Data.List
import System.Console.GetOpt

{- | 'Flag' describes the raw options -}
data Flag = Verbose Int        -- how verbose shall we be?
	  | Version            -- print version number
	  | Help               -- print usage message
	  | InType   InType    -- type of input file
	  | OutDir FilePath    -- destination directory for output files
	  | OutTypes [OutType] -- types of output to generate
	  | Analysis [AnaFlag] -- to analyse or not to analyse
	  | Pretty [PrettyOpt] -- options for the pretty-printer
	  | LibDir FilePath    -- CASL library directory
	    deriving (Show,Eq)

{- | 'HetcatsOpts' describes the interpreted options -}
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

default_HetcatsOpts :: HetcatsOpts
default_HetcatsOpts = 
    HcOpt { verbose = 0
	  , infile = ""
	  , intype   = SML_Gen_ATerm NonBAF
	  , outdir = "."
	    -- ...or like cats: same as that of the input file
	  , outtypes = [HetCASLOut Ascii]
            {- better default options, but 
	    the underlying functions are not yet implemented:
	  , intype   = HetCASLIn
	  , outtypes = [Global_Env [XML]]
	    -}
	  , analysis = True
	  , libdir  = ""
	  , rawoptions = []
	  }

-- valid input types
data InType = SML_Gen_ATerm ATFlag | CASLIn | HetCASLIn
	      deriving (Show,Eq)

-- valid types of AT (BAF or not BAF)
data ATFlag = BAF | NonBAF
	      deriving (Show,Eq)

-- ...differences between HetCASLOut and Global_Env ??
-- TODO:  Pretty, AST, dg, het..., graph
-- valid output types
data OutType = HetCASLOut OutFormat | Global_Env OutFormat
	       deriving (Show,Eq)

-- valid output formats
data OutFormat = XML | Ascii | Latex
		 deriving (Show,Eq)

-- valid analysis flags: (static or no analysis)
data AnaFlag = Static | None
	       deriving (Show,Eq)

-- valid pretty-printing options (width for LateX, Ascii width)
data PrettyOpt = Tex String | Het Int
		 deriving (Show, Eq)
	       
-- this list describes all options and gives usage Information
options :: [OptDescr Flag]
options =
    [ Option ['v'] ["verbose"] (OptArg parse_verb "Int")       
      "chatty output on stderr"
    , Option ['V'] ["version"] (NoArg Version)       
      "show version number"
    , Option ['h'] ["help", "usage"] (NoArg Help) 
      "show usage information"
    , Option ['i'] ["input-type"]  (ReqArg inp_type "TYPE")  
      "TYPE of input file: tree.gen_trm(_baf)? | het(casl)? | casl"
    , Option ['O'] ["output-dir"]  (ReqArg (\x -> OutDir x) "DIR")  
      "destination directory for output files"
    , Option ['o'] ["output-types"] (ReqArg out_types "TYPE") 
      "TYPE of output files: hetcasl-latex | hetcasl-ascii | global-env"
    , Option ['p'] ["just-parse"]  (NoArg (Analysis [None]))
      "skip static analysis - just parse"
    , Option ['L'] ["casl-libdir"]  (ReqArg (\x -> LibDir x) "DIR") 
      "CASL library directory"
    ]

-- a String describing the Options of hetcats
hetcats_usage :: String
hetcats_usage = usageInfo header options
    where header = "Usage: hetcats [OPTION...] file"

-- custom error-message prepended to our usage info
hetcats_error :: String -> IO String
hetcats_error s = error (s ++ "\n" ++ hetcats_usage)

-- parses the optional Argument to --verbose
parse_verb :: Maybe String -- optional Argument to --verbose
	   -> Flag -- Parsed verbose flag 
parse_verb Nothing  = Verbose 1
parse_verb (Just s) = Verbose $
		      case reads s of
				   []   -> error'
				   [(i,"")] -> i
				   _    -> error'
    where error' = hetcats_error ("\""++ s ++"\" is not a valid Int")

-- sets the correct input-type
inp_type :: String -> Flag
inp_type s 
    | s == "casl"                   = InType CASLIn
    | s == "hetcasl"                = InType HetCASLIn
    | s == "het"                    = InType HetCASLIn
    | "gen_trm"      `isPrefixOf` s = InType $ trm_type s
    | "tree.gen_trm" `isPrefixOf` s = InType $ trm_type s
    | otherwise      = hetcats_error ("unknown input type: " ++ s)
    where trm_type trm 
	      | "baf" `isSuffixOf` trm = SML_Gen_ATerm BAF 
	      | otherwise              = SML_Gen_ATerm NonBAF
	      -- ouch: gen_trm_bogus_grrrrr_meep gives SML_Gen_ATerm NonBAF!

-- sets the corect output type(s)
out_types :: String -> Flag
out_types s | ',' `elem` s = case merge_out_types $ split_types s of
			     [x] -> x
			     _ -> error "internal error after merging OutTypes"
	    | s == "hetcasl-latex"  = OutTypes [HetCASLOut Latex]
	    | s == "hetcasl-ascii"  = OutTypes [HetCASLOut Ascii]
	    | s == "global-env-xml" = OutTypes [Global_Env XML]
	    | otherwise = hetcats_error ("unknown output type: " ++ s)
    where split_types = map out_types . splitOn ',' 

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

-- This function parses all options
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
   case (getOpt Permute options argv) of
      (opts,non_opts,[]  ) -> form_opt_rec (merge_out_types opts) non_opts
      (_,_,errs) -> fail (concat errs ++ hetcats_usage)

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

-- some suffixes to try in turn 
-- TODO: implement perm_in_file
perm_in_file :: FilePath -> [FilePath]
perm_in_file f = [f]

-- check if one of the possible files exists and is readable
-- TODO: implement check_in_file
check_in_file :: FilePath -> IO FilePath
check_in_file = return . head . perm_in_file

-- check the output directory and choose a default one if none is specified
-- TODO: implement the checking of the out_dir
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
	        (\(OutDir fp) -> fp) $ last ods
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

