{-# OPTIONS -cpp #-}
{-|
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C.Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

This module provides functions to write a pretty printed abstract
  syntax and all the other formats.

-}

module Driver.WriteFn where

import System.IO
import Control.Monad
import Data.Maybe

import Text.PrettyPrint.HughesPJ(render)
import Common.Utils
import Common.Result
import Common.GlobalAnnotations (GlobalAnnos)
import Common.ConvertGlobalAnnos()
import qualified Common.Lib.Map as Map
import Common.SimpPretty (writeFileSDoc)

import Common.ATerm.Lib
import Common.ATerm.ReadWrite

import Logic.Coerce

import Syntax.Print_HetCASL
import Syntax.AS_Library (LIB_DEFN(), LIB_NAME())

import CASL.Logic_CASL
#ifdef UNI_PACKAGE
import CASL.CompositionTable.ComputeTable
import CASL.CompositionTable.CompositionTable
#endif

import Isabelle.CreateTheories

import Static.DevGraph
import Static.DGToSpec

import ATC.DevGraph()
import ATC.GlobalAnnotations()

import Driver.Version
import Driver.Options

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
            ThyFile -> return () -- (requires environment)
            ComptableXml -> return ()
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
    let (base,_,_) = fileparse [".casl",".tree.gen_trm",".het"] file
    in (outdir opt) ++ "/" ++ base ++ ".pp.het"
      -- maybe an optin out-file is better

write_casl_asc :: HetcatsOpts -> GlobalAnnos -> FilePath -> LIB_DEFN -> IO ()
write_casl_asc opt ga oup ld =
    do hout <- openFile oup WriteMode
       putIfVerbose opt 3 (show (printText0_eGA ga))
       hPutStr hout $ printLIB_DEFN_text ga ld
       hClose hout

casl_latex_filename :: FilePath -> HetcatsOpts -> FilePath
casl_latex_filename file opt =
    let (base,_,_) = fileparse [".casl",".tree.gen_trm",".het"] file
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

writeShATermFile :: (ShATermConvertible a) => FilePath -> a -> IO ()
writeShATermFile fp atcon = writeFile fp $ toShATermString atcon

writeShATermFileSDoc :: (ShATermConvertible a) => FilePath -> a -> IO ()
writeShATermFileSDoc fp atcon =
   writeFileSDoc fp $ writeSharedATermSDoc (versionedATermTable atcon)

versionedATermTable :: (ShATermConvertible a) => a -> ATermTable
versionedATermTable atcon =
    case  {-# SCC "att0" #-} toShATerm emptyATermTable hetcats_version of
    (att0,versionnr) ->
        case {-# SCC "att1" #-} toShATerm att0 atcon of
        (att1,aterm) ->  {-# SCC "att3" #-}
            fst $ addATerm (ShAAppl "hets" [versionnr,aterm] []) att1

toShATermString :: (ShATermConvertible a) => a -> String
toShATermString atcon = writeSharedATerm (versionedATermTable atcon)

globalContexttoShATerm :: FilePath -> GlobalContext -> IO ()
globalContexttoShATerm fp gc = writeShATermFileSDoc fp gc

writeFileInfo :: HetcatsOpts -> FilePath -> GlobalContext -> IO()
writeFileInfo opts file gctx =
  let envFile = rmSuffix file ++ ".env" in
  case analysis opts of
  Basic -> do
      putIfVerbose opts 2 ("Writing file: " ++ envFile)
      catch (globalContexttoShATerm envFile gctx) $ \ err -> do
              putIfVerbose opts 2 (envFile ++ " not written")
              putIfVerbose opts 3 ("see following error description:\n"
                                   ++ shows err "\n")
  _ -> putIfVerbose opts 2 ("Not writing " ++ envFile)

write_casl_asc_stdout :: HetcatsOpts -> GlobalAnnos -> LIB_DEFN -> IO(String)
write_casl_asc_stdout opt ga ld =
    do putIfVerbose opt 3 (show (printText0_eGA ga))
       return $ printLIB_DEFN_text ga ld

write_casl_latex_stdout :: HetcatsOpts -> GlobalAnnos -> LIB_DEFN -> IO(String)
write_casl_latex_stdout opt ga ld =
    do putIfVerbose opt 3 (show (printText0_eGA ga))
       return $ printLIB_DEFN_latex ga ld

proofStatusToShATerm :: FilePath -> ProofStatus -> IO()
proofStatusToShATerm filepath proofStatus =
  writeShATermFileSDoc filepath proofStatus

writeVerbFile :: HetcatsOpts -> FilePath -> String -> IO()
writeVerbFile opt f str = do
    putIfVerbose opt 2 $ "Writing file: " ++ f
    writeFile f str

writeSpecFiles :: HetcatsOpts -> FilePath -> LibEnv
               -> (LIB_NAME, GlobalEnv) -> IO()
writeSpecFiles opt file lenv (ln, gctx) = let
        ns = specNames opt
        allSpecs = null ns in
        mapM_ ( \ i -> case Map.lookup i gctx of
               Just (SpecEntry (_,_,_, NodeSig n _)) ->
                   case maybeResult $ computeTheory lenv (ln, n) of
                   Nothing -> putIfVerbose opt 0 $
                              "could not compute theory of spec " ++ show i
                   Just gTh@(G_theory lid sign0 sens0) ->
                       mapM_ ( \ t ->
                           let f = rmSuffix file ++ "_" ++ show i ++ "."
                                   ++ show t
                           in case t of
                                ThyFile -> case printTheory ln i gTh of
                                    Nothing -> putIfVerbose opt 0 $
                                        "could not translate to Isabelle " ++
                                         show i
                                    Just d -> writeVerbFile opt f $
                                              shows d "\n"
#ifdef UNI_PACKAGE
                                ComptableXml -> let
                                    th = (sign0, toNamedList sens0)
                                    r1 = coerceBasicTheory lid CASL "" th
                                  in case r1 of
                                     Nothing -> putIfVerbose opt 0 $
                                         "could not translate from CASL " ++
                                         show i
                                     Just th2 ->
                                       let Result d res =
                                               computeCompTable i th2
                                        in do showDiags opt d
                                              when (isJust res) $
                                                 writeVerbFile opt f $
                                                 render $ table_document $
                                                 fromJust res
#endif
                                _ -> return () -- ignore other file types
                             ) $ outtypes opt
               _ -> if allSpecs then return () else
                    putIfVerbose opt 0 $ "Unknown spec name: " ++ show i
              ) $ if allSpecs then Map.keys gctx else ns
