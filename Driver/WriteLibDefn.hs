{- |
Module      :  ./Driver/WriteLibDefn.hs
Description :  Writing out a DOL library
Copyright   :  (c) Klaus Luettich, C.Maeder, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

Writing out DOL env files as much as is needed for
the static analysis
-}

module Driver.WriteLibDefn
  ( getFilePrefix
  , getFilePrefixGeneric
  , writeLibDefn
  , writeLibDefnLatex
  , toShATermString
  , writeShATermFile
  , writeFileInfo
  ) where

import Common.Utils
import Common.Doc
import Common.LibName
import Common.PrintLaTeX
import Common.GlobalAnnotations (GlobalAnnos)
import Common.ConvertGlobalAnnos ()
import Common.IO

import Control.Exception as Exception

import ATerm.AbstractSyntax
import qualified ATerm.ReadWrite as AT

import ATC.AS_Library ()
import ATC.DevGraph ()
import ATC.Grothendieck

import Logic.Grothendieck

import Syntax.AS_Library (LIB_DEFN ())
import Syntax.Print_AS_Library ()
import Syntax.Print_AS_Structured
import Syntax.ToXml

import Text.XML.Light (ppTopElement)

import Driver.Options
import Driver.Version

import System.FilePath

-- | Compute the prefix for files to be written out
getFilePrefix :: HetcatsOpts -> FilePath -> (FilePath, FilePath)
getFilePrefix opts = getFilePrefixGeneric (envSuffix : downloadExtensions)
                     $ outdir opts

-- | Version of getFilePrefix with explicit parameters
getFilePrefixGeneric :: [String] -- ^ list of suffixes
                     -> FilePath -- ^ the outdir
                     -> FilePath -> (FilePath, FilePath)
getFilePrefixGeneric suffs odir' file =
    let (base, path, _) = fileparse suffs file
        odir = if null odir' then path else odir'
    in (odir, odir </> base)

{- |
  Write the given LIB_DEFN in every format that HetcatsOpts includes.
  Filenames are determined by the output formats.
-}
writeLibDefn :: LogicGraph -> GlobalAnnos -> FilePath -> HetcatsOpts
  -> LIB_DEFN -> IO ()
writeLibDefn lg ga file opts ld = do
    let (odir, filePrefix) = getFilePrefix opts file
        printXml fn = writeFile fn $ ppTopElement (xmlLibDefn lg ga ld)
        printAscii b fn = writeEncFile (ioEncoding opts) fn
          $ renderExtText (StripComment b) ga (prettyLG lg ld) ++ "\n"
        printHtml fn = writeEncFile (ioEncoding opts) fn
          $ renderHtml ga $ prettyLG lg ld
        write_type :: OutType -> IO ()
        write_type ty = case ty of
            PrettyOut pty -> do
              let fn = filePrefix ++ "." ++ show ty
              putIfVerbose opts 2 $ "Writing file: " ++ fn
              case pty of
                PrettyXml -> printXml fn
                PrettyAscii b -> printAscii b fn
                PrettyHtml -> printHtml fn
                PrettyLatex b -> writeLibDefnLatex lg b ga fn ld
            _ -> return () -- implemented elsewhere
    putIfVerbose opts 3 ("Current OutDir: " ++ odir)
    mapM_ write_type $ outtypes opts

writeLibDefnLatex :: LogicGraph -> Bool -> GlobalAnnos -> FilePath -> LIB_DEFN
  -> IO ()
writeLibDefnLatex lg lbl ga oup = writeFile oup . renderLatex Nothing
  . toLatexAux (StripComment False) (MkLabel lbl) ga . prettyLG lg

toShATermString :: ShATermLG a => a -> IO String
toShATermString = fmap AT.writeSharedATerm . versionedATermTable

writeShATermFile :: ShATermLG a => FilePath -> a -> IO ()
writeShATermFile fp atcon = toShATermString atcon >>= writeFile fp

versionedATermTable :: ShATermLG a => a -> IO ATermTable
versionedATermTable atcon = do
    (att1, versionno) <- toShATermLG emptyATermTable hetsVersionNumeric
    (att2, aterm) <- toShATermLG att1 atcon
    return $ fst $ addATerm (ShAAppl "hets" [versionno, aterm] []) att2

writeShATermFileSDoc :: ShATermLG a => FilePath -> a -> IO ()
writeShATermFileSDoc fp atcon =
   versionedATermTable atcon >>= AT.writeSharedATermFile fp

writeFileInfo :: ShATermLG a => HetcatsOpts -> LibName
              -> FilePath -> LIB_DEFN -> a -> IO ()
writeFileInfo opts ln file ld gctx =
  let envFile = snd (getFilePrefix opts file) ++ envSuffix in
  case analysis opts of
  Basic -> do
      putIfVerbose opts 2 ("Writing file: " ++ envFile)
      Exception.catch (writeShATermFileSDoc envFile (ln, (ld, gctx)))
           $ \ err -> do
              putIfVerbose opts 2 (envFile ++ " not written")
              putIfVerbose opts 3 ("see following error description:\n"
                                   ++ shows (err :: SomeException) "\n")
  _ -> putIfVerbose opts 2 ("Not writing " ++ envFile)
