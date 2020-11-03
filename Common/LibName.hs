{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./Common/LibName.hs
Description :  library names for DOL and development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Abstract syntax of HetCASL/DOL specification library names.
   Follows Sect. II:2.2.5 of the CASL Reference Manual
   and 9.7 of the OMG standard DOL.
-}

module Common.LibName
  ( LibName (LibName, getLibId, locIRI, mimeType, libVersion)
  , VersionNumber (VersionNumber)
  , isQualNameFrom
  , isQualName
  , mkQualName
  , unQualName
  , setFilePath
  , libToFileName
  , getFilePath
  , iriLibName
  , filePathToLibId
  , emptyLibName
  , convertFileToLibStr
  , mkLibStr
  , setMimeType
  , mkLibName
  , libNameToId
  ) where

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.IRI
import Common.Keywords
import Common.Percent
import Common.Utils

import Data.Char
import Data.Data
import Data.List
import Data.Maybe
import Data.Ord
import Data.Hashable
import GHC.Generics (Generic)

import System.FilePath

omTs :: [Token]
omTs = [genToken "OM"]

mkQualName :: SIMPLE_ID -> LibName -> Id -> Id
mkQualName nodeId ln i =
  Id omTs [i, simpleIdToId nodeId, libNameToId ln] $ posOfId i

isQualNameFrom :: SIMPLE_ID -> LibName -> Id -> Bool
isQualNameFrom nodeId ln i@(Id _ cs _) = case cs of
  _ : n : l : _ | isQualName i ->
    n == simpleIdToId nodeId && libNameToId ln == l
  _ -> True

isQualName :: Id -> Bool
isQualName (Id ts cs _) = case cs of
  _ : _ : _ -> ts == omTs
  _ -> False

unQualName :: Id -> Id
unQualName j@(Id _ cs _) = case cs of
  i : _ | isQualName j -> i
  _ -> j

libNameToId :: LibName -> Id
libNameToId ln = let
  path = splitOn '/' $ libToFileName ln
  toTok s = Token s $ getRange ln
  in mkId $ map toTok $ intersperse "/" path

data LibName = LibName
    { getLibId :: IRI
    , locIRI :: Maybe IRI
    , mimeType :: Maybe String
    , libVersion :: Maybe VersionNumber }
  deriving (Typeable, Data, Generic)

instance Hashable LibName

iriLibName :: IRI -> LibName
iriLibName i = LibName i Nothing Nothing Nothing

mkLibName :: IRI -> Maybe VersionNumber -> LibName
mkLibName i v = (iriLibName i) { libVersion = v }

emptyLibName :: String -> LibName
emptyLibName s = iriLibName .
  fromMaybe (if null s then nullIRI else error $ "emptyLibName: " ++ s)
  $ parseIRICurie s

-- | convert file name to IRI reference
filePathToIri :: FilePath -> IRI
filePathToIri fp = fromMaybe (error $ "filePathToIri: " ++ fp)
  . parseIRIReference $ encodeBut (\ c -> isUnreserved c || elem c reserved) fp

-- | use file name as library IRI
filePathToLibId :: FilePath -> IRI
filePathToLibId = setAngles True . filePathToIri

-- | insert file name as location IRI
setFilePath :: FilePath -> LibName -> LibName
setFilePath fp ln = ln { locIRI = Just $ filePathToIri fp }

-- | insert optional mime type
setMimeType :: Maybe String -> LibName -> LibName
setMimeType m ln = ln { mimeType = m }

-- | interpret library IRI as file path
libToFileName :: LibName -> FilePath
libToFileName = iriToStringUnsecure . setAngles False . getLibId

-- | extract location IRI as file name
getFilePath :: LibName -> FilePath
getFilePath = maybe "" iriToStringUnsecure . locIRI

data VersionNumber = VersionNumber [String] Range
  deriving (Typeable, Data, Generic)
                    -- pos: "version", start of first string

instance Hashable VersionNumber

instance GetRange LibName where
  getRange = getRange . getLibId

instance Show LibName where
  show = show . hsep . prettyLibName

prettyVersionNumber :: VersionNumber -> [Doc]
prettyVersionNumber (VersionNumber v _) =
  [keyword versionS, hcat $ punctuate dot $ map codeToken v]

prettyLibName :: LibName -> [Doc]
prettyLibName ln =
  pretty (getLibId ln) : maybe [] prettyVersionNumber (libVersion ln)

instance Eq LibName where
  ln1 == ln2 = compare ln1 ln2 == EQ

instance Ord LibName where
  compare = comparing getLibId

instance Pretty LibName where
    pretty = fsep . prettyLibName

convertFileToLibStr :: FilePath -> String
convertFileToLibStr = mkLibStr . takeBaseName

stripLibChars :: String -> String
stripLibChars = filter (\ c -> isAlphaNum c || elem c "'_/")

mkLibStr :: String -> String
mkLibStr = dropWhile (== '/') . stripLibChars
