{- |
Module      :  $Header$
Description :  reading and parsing ATerms, CASL, HetCASL files
Copyright   :  (c) Klaus Luettich, C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(DevGraph)

reading and parsing ATerms, CASL, HetCASL files as much as is needed for the
static analysis
-}

module Driver.ReadFn where

import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.Parse_AS_Library

import ATC.Grothendieck
import ATC.Sml_cats
import ATC.LibName ()


import Driver.Options

import ATerm.AbstractSyntax
import ATerm.ReadWrite

import Common.AnnoState
import Common.Id
import Common.Result
import Common.DocUtils
import Common.LibName

import Text.ParserCombinators.Parsec

import System.FilePath

import Data.List (isPrefixOf)
import Data.Maybe

readLibDefnM :: Monad m => LogicGraph -> HetcatsOpts -> FilePath -> String
  -> m LIB_DEFN
readLibDefnM lgraph opts file input =
    if null input then fail ("empty input file: " ++ file) else
    case intype opts of
    ATermIn _  -> return $ from_sml_ATermString input
    _ -> case runParser (library lgraph { currentLogic = defLogic opts })
          (emptyAnnos ()) file input of
         Left err  -> fail (showErr err)
         Right ast -> return ast

readShATermFile :: ShATermLG a => LogicGraph -> FilePath -> IO (Result a)
readShATermFile lg fp = do
    str <- readFile fp
    return $ fromShATermString lg str

fromVersionedATT :: ShATermLG a => LogicGraph -> ATermTable -> Result a
fromVersionedATT lg att =
    case getATerm att of
    ShAAppl "hets" [versionnr,aterm] [] ->
        if hetsVersion == snd (fromShATermLG lg versionnr att)
        then Result [] (Just $ snd $ fromShATermLG lg aterm att)
        else Result [Diag Warning
                     "Wrong version number ... re-analyzing"
                     nullRange] Nothing
    _  ->  Result [Diag Warning
                   "Couldn't convert ShATerm back from ATermTable"
                   nullRange] Nothing

fromShATermString :: ShATermLG a => LogicGraph -> String -> Result a
fromShATermString lg str = if null str then
    Result [Diag Warning "got empty string from file" nullRange] Nothing
    else fromVersionedATT lg $ readATerm str

readVerbose :: ShATermLG a => LogicGraph -> HetcatsOpts -> LibName -> FilePath
            -> IO (Maybe a)
readVerbose lg opts ln file = do
    putIfVerbose opts 1 $ "Reading " ++ file
    Result ds mgc <- readShATermFile lg file
    showDiags opts ds
    case mgc of
      Nothing -> return Nothing
      Just (ln2, a) -> if ln2 == ln then return $ Just a else do
        putIfVerbose opts 0 $ "incompatible library names: "
               ++ showDoc ln " (requested) vs. "
               ++ showDoc ln2 " (found)"
        return Nothing

-- | create a file name without suffix from a library name
libNameToFile :: LibName -> FilePath
libNameToFile ln = case getLibId ln of
  IndirectLink file _ ofile _ ->
      if null ofile then file
      else rmSuffix ofile
  DirectLink _ _ -> error "libNameToFile"

findFileOfLibName :: HetcatsOpts -> FilePath -> IO (Maybe FilePath)
findFileOfLibName opts file = do
          let fs = map (</> file) $ "" : libdirs opts
          ms <- mapM (existsAnSource opts { intype = GuessIn }) fs
          return $ case catMaybes ms of
            [] -> Nothing
            f : _ -> Just f

-- | convert a file name that may have a suffix to a library name
fileToLibName :: HetcatsOpts -> FilePath -> LibName
fileToLibName opts efile =
    let paths = libdirs opts
        file = rmSuffix efile -- cut of extension
        pps = filter snd $ map (\ p -> (p, isPrefixOf p file)) paths
        nfile = dropWhile (== '/') $         -- cut off leading slashes
                case pps of
                  [] -> file
                  (path, _) : _ -> drop (length path) file
                   -- cut off libdir prefix
    in emptyLibName $ filter (`notElem` ". ") nfile
