
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
-}

module Options where

import Version
import Utils

import Directory
import System

import Char (isSpace)
import List
import GetOpt

import GHC.Read (readEither)

{- | 'Flag' describes the raw options -}
data Flag = Verbose Int
	  | Version
	  | Help
	  | InType   InType
	  | OutTypes [OutType] 
	  | Analysis [AnaFlag]
	  | LibDir FilePath
	  | OutDir FilePath
	    deriving (Show,Eq)

data HetcatsOpts = HcOpt { verbose  :: Int     -- ^greater than null for 
			                       -- turning verbosity on.  
			 , libdir   :: FilePath
			 , outdir   :: FilePath
			 , infile   :: FilePath
			 , intype   :: InType
			 , outtypes :: [OutType]
			 , rawoptions :: [Flag]
			 } deriving (Show,Eq)

default_HetcatsOpts :: HetcatsOpts
default_HetcatsOpts = HcOpt { verbose = 0
			    , libdir  = ""
			    , outdir = "." -- or like cats the same as
			                   -- that of the input file	     
			    , infile = ""
			    , intype   = SML_Gen_ATerm NonBAF
			    , outtypes = [HetCASLOut Ascii]
                           {- better default options, but 
			      the unlying functions are not jet implemented :
			    , intype   = HetCASLIn
			    , outtypes = [Global_Env [XML]] -}
			    , rawoptions = []
			    }

data InType = SML_Gen_ATerm ATFlag | CASLIn | HetCASLIn
	      deriving (Show,Eq)

data ATFlag = BAF | NonBAF
	       deriving (Show,Eq)

data OutType = HetCASLOut OutFormat | Global_Env OutFormat
	       deriving (Show,Eq)

data OutFormat = XML | Ascii | Latex
	       deriving (Show,Eq)

data AnaFlag = Static
	       deriving (Show,Eq)


-- This function parses all options
hetcatsOpts :: [String] -> IO HetcatsOpts
hetcatsOpts argv =
   case (getOpt Permute options argv) of
      (o,n,[]  ) -> form_opt_rec (merge_out_types o) n
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
    in do if Help `elem` flags then 
	     do putStrLn $ "\n" ++ hetcats_usage
		exitWith ExitSuccess
	   else 
	     if Version `elem` flags then 
		do putStrLn $ "version of hetcats: " ++ hetcats_version
		   exitWith ExitSuccess
	     else
	        return ()
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

-- check if the on of the possible files exists and is readable
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

-- a String describing the Options of hetcats
hetcats_usage :: String
hetcats_usage = usageInfo header options
    where header = "Usage: hetcats [OPTION...] file"

-- this list describes all options and gives usage Information
options :: [OptDescr Flag]
options =
 [ Option ['v'] ["verbose"] (OptArg parse_verb "Int")       
            "chatty output on stderr"
 , Option ['V'] ["version"] (NoArg Version)       
            "show version number"
 , Option ['h'] ["help"] (NoArg Help) 
            "show usage information"
 , Option ['i'] ["input-type"]  (ReqArg inp_type "TYPE")  
            "TYPE of input file: gen-trm | gen-trm-baf | hetcasl (default) | casl (via cats)"
 , Option ['O'] ["output-dir"]  (ReqArg (\x -> OutDir x) "DIR")  
            "output DIR"
 , Option ['o'] ["output-types"] (ReqArg out_types "TYPE") 
            "select TYPE of output files: hetcasl-latex | hetcasl-ascii | global-env"
 , Option ['L'] ["casl-libdir"]  (ReqArg (\x -> LibDir x) "DIR") 
            "CASL library directory"
 ]

-- | parse the optional Argument to --verbose
parse_verb :: Maybe String -- ^ optional Argument to --verbose
	   -> Flag -- ^ Parsed verbose flag 
parse_verb Nothing  = Verbose 1
parse_verb (Just s) = Verbose (case readEither s of
			       Right i -> i
			       Left _  -> error $ "\""++ s
			                          ++"\" is not an Int\n"
			                          ++ hetcats_usage)

-- Just the function to get the input-type right
inp_type :: String -> Flag
inp_type s | "gen-trm" `isPrefixOf` s = InType $ trm_type s
	   | s == "casl"    = InType CASLIn
	   | s == "hetcasl" = InType HetCASLIn
	   | otherwise = error ("unknown input type: " ++ s ++ "\n" ++
				hetcats_usage)
    where trm_type trm | "baf" `isSuffixOf` trm = SML_Gen_ATerm BAF 
		       | otherwise = SML_Gen_ATerm NonBAF

out_types :: String -> Flag
out_types s | ',' `elem` s = case merge_out_types $ split_types s of
			     [x] -> x
			     _ -> error "another thing went wrong!!"
	    | s == "hetcasl-latex"  = OutTypes [HetCASLOut Latex]
	    | s == "hetcasl-ascii"  = OutTypes [HetCASLOut Ascii]
	    | s == "global-env-xml" = OutTypes [Global_Env XML]
	    | otherwise = error ("unknown output type: " ++ s ++ "\n" ++
				 hetcats_usage)
    where split_types = map out_types . splitOn ',' 


merge_out_types :: [Flag] -> [Flag]
merge_out_types flags = 
    let (ots,flags') = partition is_out_type flags 
	is_out_type f = case f of
			OutTypes _ -> True
			_          -> False
	concatTypes l ot = case ot of
			     OutTypes l' -> l++l'
			     _ -> error "something went very wrong!!"
	ots' = foldl concatTypes [] ots
    in if null ots' then flags' else (OutTypes ots'):flags'  


