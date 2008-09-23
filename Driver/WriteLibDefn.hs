{- |
Module      :  $Header$
Description :  Writing out a HetCASL library
Copyright   :  (c) Klaus Luettich, C.Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

Writing out HetCASL env files as much as is needed for
the static analysis
-}

module Driver.WriteLibDefn where

import Common.Utils
import Common.Doc
import Common.DocUtils
import Common.LibName
import Common.PrintLaTeX
import Common.GlobalAnnotations (GlobalAnnos)
import Common.ConvertGlobalAnnos ()
import Common.SimpPretty (writeFileSDoc)

import Common.ATerm.Lib
import Common.ATerm.ReadWrite

import ATC.AS_Library ()
import ATC.DevGraph ()

import Syntax.AS_Library (LIB_DEFN())
import Syntax.Print_AS_Library ()

import Driver.Options

-- | compute the prefix for files to be written out
getFilePrefix :: HetcatsOpts -> FilePath -> (FilePath, FilePath)
getFilePrefix opts file =
    let odir' = outdir opts
        (base, path, _) = fileparse (envSuffix : downloadExtensions) file
        odir = if null odir' then path else odir'
    in (odir, pathAndBase odir base)

{- |
  Write the given LIB_DEFN in every format that HetcatsOpts includes.
  Filenames are determined by the output formats.
-}
write_LIB_DEFN :: GlobalAnnos -> FilePath -> HetcatsOpts -> LIB_DEFN -> IO ()
write_LIB_DEFN ga file opts ld = do
    let (odir, filePrefix) = getFilePrefix opts file
        filename ty = filePrefix ++ "." ++ show ty
        verbMesg ty = putIfVerbose opts 2 $ "Writing file: " ++ filename ty
        printAscii ty = do
          verbMesg ty
          write_casl_asc opts ga (filename ty) ld
        write_type :: OutType -> IO ()
        write_type t = case t of
            PrettyOut PrettyAscii -> printAscii t
            PrettyOut PrettyLatex -> do
                verbMesg t
                write_casl_latex opts ga (filename t) ld
            _ -> return () -- implemented elsewhere
    putIfVerbose opts 3 ("Current OutDir: " ++ odir)
    mapM_ write_type $ outtypes opts

write_casl_asc :: HetcatsOpts -> GlobalAnnos -> FilePath -> LIB_DEFN -> IO ()
write_casl_asc _ ga oup ld = writeFile oup $
          shows (useGlobalAnnos ga $ pretty ld) "\n"

debug_latex_filename :: FilePath -> FilePath
debug_latex_filename =
    ( \ (b, p, _) -> p ++ b ++ ".debug.tex") . fileparse [".pp.tex"]

write_casl_latex :: HetcatsOpts -> GlobalAnnos -> FilePath -> LIB_DEFN -> IO ()
write_casl_latex opts ga oup ld =
    do let ldoc = toLatex ga $ pretty ld
       writeFile oup $ renderLatex Nothing ldoc
       doDump opts "DebugLatex" $
           writeFile (debug_latex_filename oup) $
               debugRenderLatex Nothing ldoc

toShATermString :: (ShATermConvertible a) => a -> IO String
toShATermString atcon = fmap writeSharedATerm $ versionedATermTable atcon

writeShATermFile :: (ShATermConvertible a) => FilePath -> a -> IO ()
writeShATermFile fp atcon = toShATermString atcon >>= writeFile fp

versionedATermTable :: (ShATermConvertible a) => a -> IO ATermTable
versionedATermTable atcon = do
    att0 <- newATermTable
    (att1, versionnr) <- toShATermAux att0 hetsVersion
    (att2, aterm) <- toShATermAux att1 atcon
    return $ fst $ addATerm (ShAAppl "hets" [versionnr,aterm] []) att2

writeShATermFileSDoc :: (ShATermConvertible a) => FilePath -> a -> IO ()
writeShATermFileSDoc fp atcon = do
   att <- versionedATermTable atcon
   writeFileSDoc fp $ writeSharedATermSDoc att

writeFileInfo :: (ShATermConvertible a) => HetcatsOpts -> LIB_NAME
              -> FilePath -> LIB_DEFN -> a -> IO ()
writeFileInfo opts ln file ld gctx =
  let envFile = snd (getFilePrefix opts file) ++ envSuffix in
  case analysis opts of
  Basic -> do
      putIfVerbose opts 2 ("Writing file: " ++ envFile)
      catch (writeShATermFileSDoc envFile (ln, (ld, gctx))) $ \ err -> do
              putIfVerbose opts 2 (envFile ++ " not written")
              putIfVerbose opts 3 ("see following error description:\n"
                                   ++ shows err "\n")
  _ -> putIfVerbose opts 2 ("Not writing " ++ envFile)
