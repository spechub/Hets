{-| 
   
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

  This module provides functions to write a pretty printed abstract
  syntax and all the other formats.

-}

module WriteFn where

import Options

import Common.Utils
import Common.Result

import System.IO
import System.IO.Error(try)
import Syntax.Print_HetCASL
import Syntax.AS_Library (LIB_DEFN(), LIB_NAME()) 
import Syntax.GlobalLibraryAnnotations
import Common.GlobalAnnotations (GlobalAnnos)
import Version
import Common.ConvertGlobalAnnos
import Common.ATerm.Lib
import qualified Common.Lib.Map as Map

import ATC.Proofs
import Proofs.Proofs

import Static.DevGraph
import ATC.DevGraph
import Common.SimpPretty (writeFileSDoc)
-- for debugging
import Debug.Trace

{---
  Write the given LIB_DEFN in every format that HetcatsOpts includes.
  Filenames are determined by the output formats.
  @param opt - Options Either default or given on the comandline
  @param ld  - a LIB_DEFN read as ATerm or parsed
-}
write_LIB_DEFN :: GlobalAnnos -> FilePath -> HetcatsOpts -> LIB_DEFN -> IO ()
write_LIB_DEFN ga file opt ld = sequence_ $ map write_type $ outtypes opt
    where
    write_type :: OutType -> IO ()
    write_type t = 
        case t of 
            HetCASLOut OutASTree OutAscii -> printAscii t
	    PrettyOut PrettyAscii -> printAscii t 
            PrettyOut PrettyLatex -> do
                putIfVerbose opt 3 ("Generating OutType: " ++ (show t))
                write_casl_latex opt ga (casl_latex_filename file opt) ld
	    EnvOut -> return () -- implemented in hets.hs 
				-- (requires environment)
            _ -> do putStrLn ( "Error: the OutType \"" ++ 
                        show t ++ "\" is not implemented")
                    return ()
    printAscii ty = do
                putIfVerbose opt 3 ("Generating OutType: " ++ (show ty))
                write_casl_asc opt ga (casl_asc_filename file opt) ld
{---
  Produces the filename of the pretty printed CASL-file.
  @param opt   - Options from the command line 
  @return path - full path to the generated file
-}
casl_asc_filename :: FilePath -> HetcatsOpts -> FilePath
casl_asc_filename file opt =
    let (base,_,_) = fileparse [".casl",".tree.gen_trm"] file
    in (outdir opt) ++ "/" ++ base ++ ".pp.casl"
      -- maybe an optin out-file is better

write_casl_asc :: HetcatsOpts -> GlobalAnnos -> FilePath -> LIB_DEFN -> IO ()
write_casl_asc opt ga oup ld =
    do hout <- openFile oup WriteMode
       putIfVerbose opt 3 (show (printText0_eGA ga))
       hPutStr hout $ printLIB_DEFN_text ga ld
       hClose hout

casl_latex_filename :: FilePath -> HetcatsOpts -> FilePath
casl_latex_filename file opt =
    let (base,_,_) = fileparse [".casl",".tree.gen_trm"] file
    in (outdir opt) ++ "/" ++ base ++ ".pp.tex"
      -- maybe an optin out-file is better

debug_latex_filename :: FilePath -> FilePath
debug_latex_filename = (\(b,p,_) -> p++ b ++ ".debug.tex") . 
                       fileparse [".pp.tex"]

write_casl_latex :: HetcatsOpts -> GlobalAnnos -> FilePath -> LIB_DEFN -> IO ()
write_casl_latex opt ga oup ld =
    do hout <- openFile oup WriteMode
       putIfVerbose opt 3 (show (printText0_eGA ga))
       hPutStr hout $ printLIB_DEFN_latex ga ld
       hClose hout
       doIfVerbose opt 5
        (do dout <- openFile (debug_latex_filename oup) WriteMode
            hPutStr dout $ printLIB_DEFN_debugLatex ga ld
            hClose dout)
       return ()

writeShATermFile :: (ATermConvertible a) => FilePath -> a -> IO ()
writeShATermFile fp atcon = writeFile fp $ toShATermString atcon 

writeShATermFileSDoc :: (ATermConvertible a) => FilePath -> a -> IO ()
writeShATermFileSDoc fp atcon =
   writeFileSDoc fp $ writeSharedATermSDoc (versionedATermTable atcon)

versionedATermTable :: (ATermConvertible a) => a -> ATermTable
versionedATermTable atcon =      
    case  {-# SCC "att0" #-} toShATerm emptyATermTable hetcats_version of
    (att0,versionnr) -> 
	case {-# SCC "att1" #-} toShATerm att0 atcon of
	(att1,aterm) ->  {-# SCC "att3" #-} 
	    fst $ addATerm (ShAAppl "hets" [versionnr,aterm] []) att1
                           
toShATermString :: (ATermConvertible a) => a -> String
toShATermString atcon = writeSharedATerm (versionedATermTable atcon)
                        

globalContexttoShATerm :: FilePath -> GlobalContext -> IO ()
globalContexttoShATerm fp gc = writeShATermFileSDoc fp gc

writeFileInfo :: HetcatsOpts -> [Diagnosis] -> String -> LIB_NAME -> LibEnv -> IO()
writeFileInfo opts diags file ln lenv = 
  if hasErrors diags then return ()
   else case Map.lookup ln lenv of
    Nothing -> putStrLn ("*** Error: Cannot find library "++show ln)
    Just gctx -> do
      let envFile = rmSuffix file ++ ".env"
      putIfVerbose opts 2 ("Writing "++envFile)
      res <- try (globalContexttoShATerm envFile gctx)
      case res of
       Right _ -> return ()
       Left ioErr -> do 
           putIfVerbose opts 2 (envFile++" not written")
	   putIfVerbose opts 3 ("see following error description:\n"
				++show ioErr++"\n")

write_casl_asc_stdout :: HetcatsOpts -> GlobalAnnos -> LIB_DEFN -> IO(String)
write_casl_asc_stdout opt ga ld =
    do putIfVerbose opt 3 (show (printText0_eGA ga))
       return $ printLIB_DEFN_text ga ld
       
write_casl_latex_stdout :: HetcatsOpts -> GlobalAnnos -> LIB_DEFN -> IO(String)
write_casl_latex_stdout opt ga ld =
    do putIfVerbose opt 3 (show (printText0_eGA ga))
       return $ printLIB_DEFN_latex ga ld
       {-doIfVerbose opt 5
        (do dout <- openFile (debug_latex_filename oup) WriteMode
            hPutStr dout $ printLIB_DEFN_debugLatex ga ld
            hClose dout)
       -}

proofStatusToShATerm :: FilePath -> ProofStatus -> IO()
proofStatusToShATerm filepath proofStatus =
  writeShATermFileSDoc filepath proofStatus