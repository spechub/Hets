
{- HetCATS/hetcats/WriteFn.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   This module provides functions to write a pretty printed abstract
   syntax and all the other formats.

-}

module WriteFn where

import Options
import List

import IO
import Print_HetCASL
import AS_Library (LIB_DEFN(..))

write_LIB_DEFN :: HetcatsOpts -> LIB_DEFN -> IO ()
write_LIB_DEFN opt ld = sequence_ $ map write_type $ outtypes opt
    where write_type :: OutType -> IO ()
	  write_type t = 
	      case t of 
	      CASLOut -> write_casl_asc (casl_asc_filename opt) ld
	      _ -> error $ "the outtype \"" ++ 
		           show t ++ "\" is not implemented"

casl_asc_filename :: HetcatsOpts -> FilePath
casl_asc_filename opt =
    (outdir opt) ++ "/" ++ basename (infile opt) ++ ".pp.casl"
      -- maybe an optin out-file is better

basename :: FilePath -> FilePath
basename fp | ".tree.gen_trm" `isSuffixOf` fp = stripOf ".tree.gen_trm" fp 
	    | ".casl"         `isSuffixOf` fp = stripOf ".casl" fp
	    | otherwise = fp

stripOf :: [a] -> [a] -> [a]
stripOf suf = reverse . drop (length suf) . reverse

write_casl_asc :: FilePath -> LIB_DEFN -> IO ()
write_casl_asc oup ld =
    do hout <- openFile oup WriteMode
       hPutStr hout $ printLIB_DEFN_text ld
