
{---
  HetCATS/hetcats/WriteFn.hs
  @version $Id$
  @author Klaus L&uuml;ttich<BR>
  Year:   2002
  <p>
  This module provides functions to write a pretty printed abstract
  syntax and all the other formats.
  </p>
-}
module WriteFn where

import Options
import List

import IO 
import IOExts (trace)
import Print_HetCASL
import AS_Library (LIB_DEFN()) 

{---
  Write the given LIB_DEFN in every format that HetcatsOpts includes.
  Filenames are determined by the output formats.
  @param opt - Options Either default or given on the comandline
  @param ld  - a LIB_DEFN read as ATerm or parsed
-}
write_LIB_DEFN :: HetcatsOpts -> LIB_DEFN -> IO ()
write_LIB_DEFN opt ld = sequence_ $ map write_type $ outtypes opt
    where write_type :: OutType -> IO ()
	  write_type t = 
	      case t of 
	      CASLOut -> write_casl_asc (casl_asc_filename opt) ld
	      _ -> trace ( "the outtype \"" ++ 
		           show t ++ "\" is not implemented")
		         (return ())
{---
  Produces the filename of the pretty printed CASL-file.
  @param opt   - Options from the command line 
  @return path - full path to the generated file
-}
casl_asc_filename :: HetcatsOpts -> FilePath
casl_asc_filename opt =
    (outdir opt) ++ "/" ++ basename (infile opt) ++ ".pp.casl"
      -- maybe an optin out-file is better

basename :: FilePath -> FilePath
basename fp | ".tree.gen_trm" `isSuffixOf` fp = stripOf ".tree.gen_trm" fp 
	    | ".casl"         `isSuffixOf` fp = stripOf ".casl" fp
	    | otherwise = fp

stripOf :: (Show a, Eq a) => [a] -> [a] -> [a]
stripOf suf inp = reverse $ stripOf' (reverse suf) (reverse inp)
    where stripOf' []     i  = i
	  stripOf' (x:xs) [] = error $ 
			       concat ["suffix is longer than input string\n"
				      ,"input was: ", show suf, " ",show inp ]
	  stripOf' (x:xs) (y:ys) | x == y    = stripOf' xs ys
				 | otherwise = 
				     error $ concat ["suffix don't match input"
						    ," at "
						    ,show $ reverse (x:xs)
						    ," ",show $ reverse (y:ys)]

-- stripOfx suf = reverse . drop (length suf) . reverse

write_casl_asc :: FilePath -> LIB_DEFN -> IO ()
write_casl_asc oup ld =
    do hout <- openFile oup WriteMode
       hPutStr hout $ printLIB_DEFN_text ld
