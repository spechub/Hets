{- |
Module      :  ./TPTP/ParseAsLibDefn.hs
Description :  Methods to parse TPTP as a LibDefn
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional
Portability :  non-portable (imports Logic)

-}

module TPTP.ParseAsLibDefn (parseTPTP) where

import TPTP.AS as AS
import TPTP.Common
import TPTP.Logic_TPTP as Logic
import TPTP.Parser

import Common.AnnoState
import Common.AS_Annotation (Annoted (..), item)
import Common.Id
import Common.IRI
import Common.LibName
import Common.Parsec
import Common.Result (fatal_error)
import Common.ResultT
import Driver.Options
import Logic.Grothendieck
import Syntax.AS_Library
import Syntax.AS_Structured

import Data.Maybe
import Data.List
import qualified Data.Map as Map
import System.FilePath.Posix
import Text.ParserCombinators.Parsec

parseTPTP :: HetcatsOpts -> FilePath -> String -> ResultT IO [LIB_DEFN]
parseTPTP opts file input = do
  let tptpParser = many (parseBasicSpec Map.empty) << eof
  case runParser tptpParser (emptyAnnos ())  file input of
    Left err -> do
      liftR $ fatal_error (show err) nullRange
      return $ [emptyLibDefn file]
    Right basicSpecs -> return $ map (convertToLibDefn opts file) basicSpecs
  where

convertToLibDefn :: HetcatsOpts -> FilePath -> BASIC_SPEC -> LIB_DEFN
convertToLibDefn opts filepath spec = Lib_defn libName libItems nullRange []
  where
    -- For the library name, use the part of the @filepath@ that comes after the
    -- library directory.
    -- The lirary directory is the first of the libdirs given by the command
    -- line option --hets-libdirs. If there is no such option, then it is the
    -- directory of the @filepath@.
    libName = iriLibName specName
    specName' = fromJust $ parseIRICurie $ escapeTPTPFilePath filename
    specName = unescapeTPTPFileIRI specName'
    filename = case stripPrefix libdir filepath of
      Just suffix -> suffix
      Nothing -> filename'
    libdir = case libdirs opts of
      l : _ -> if isSuffixOf "/" l then l else l ++ "/"
      [] -> dirname
    (dirname, filename') = splitFileName filepath

    libItems = makeLogicItem Logic.TPTP : includedLibs ++ [specItem]
    includedLibs = map (addDownload False) includes
    includes = directIncludes spec
    specItem = makeSpecItem specName annotedSpec
    annotedSpec = addImports includes . makeSpec $ G_basic_spec Logic.TPTP spec

emptyLibDefn :: FilePath -> LIB_DEFN
emptyLibDefn filepath =
  Lib_defn (emptyLibName (convertFileToLibStr filepath)) [] nullRange []

-- Retrieves all includes from a basic spec, without recursing into the
-- included documents
directIncludes :: BASIC_SPEC -> [SPEC_NAME]
directIncludes (AS.Basic_spec itemsTPTP) = importsTPTP $ map item itemsTPTP
  where
    importsTPTP :: [AS.TPTP] -> [SPEC_NAME]
    importsTPTP = concatMap includesInTPTP

    includesInTPTP :: AS.TPTP -> [SPEC_NAME]
    includesInTPTP = concatMap includes . inputsFromTPTP

    inputsFromTPTP :: AS.TPTP -> [TPTP_input]
    inputsFromTPTP (AS.TPTP inputs) = inputs

    includes :: TPTP_input -> [SPEC_NAME]
    includes tptp_input = case tptp_input of
      TPTP_include (Include filename _) -> [filename]
      _ -> []
