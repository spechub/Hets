{- |
Module      :  $Header$
Description :  library names for HetCASL and development graphs
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Abstract syntax of HetCASL specification libraries
   Follows Sect. II:2.2.5 of the CASL Reference Manual.
-}

module Common.LibName where

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Keywords
import Common.Utils

import Data.List
import System.Time

omTs :: [Token]
omTs = [genToken "OM"]

mkQualName :: SIMPLE_ID -> LIB_ID -> Id -> Id
mkQualName nodeId libId i =
  Id omTs [i, simpleIdToId nodeId, libIdToId libId] $ posOfId i

isQualNameFrom :: SIMPLE_ID -> LIB_ID -> Id -> Bool
isQualNameFrom nodeId libId i@(Id _ cs _) = case cs of
  _ : n : l : _ | isQualName i ->
      n == simpleIdToId nodeId && libIdToId libId == l
  _ -> True

isQualName :: Id -> Bool
isQualName (Id ts cs _) = case cs of
  _ : _ : _ -> ts == omTs
  _ -> False

getLibId :: Id -> Id
getLibId j@(Id _ cs _) = case cs of
  [_, _, i] | isQualName j -> i
            | otherwise ->
                error "Check by isQualName before calling getLibId!"
  _ -> error "Check by isQualName before calling getLibId!"

getNodeId :: Id -> Id
getNodeId j@(Id _ cs _) = case cs of
  [_, i, _] | isQualName j -> i
            | otherwise ->
                error "Check by isQualName before calling getNodeId!"
  _ -> error "Check by isQualName before calling getNodeId!"


unQualName :: Id -> Id
unQualName j@(Id _ cs _) = case cs of
  i : _ | isQualName j -> i
  _ -> j

libIdToId :: LIB_ID -> Id
libIdToId li = let
  path = splitOn '/' $ show li
  toTok s = Token s $ getRange li
  in mkId $ map toTok $ intersperse "/" path

data LIB_NAME = Lib_version
    { getLIB_ID :: LIB_ID
    , libVersion :: VERSION_NUMBER }
    | Lib_id { getLIB_ID :: LIB_ID }

data LIB_ID = Direct_link URL Range
              -- pos: start of URL
            | Indirect_link PATH Range FilePath ClockTime
              -- pos: start of PATH

noTime :: ClockTime
noTime = TOD 0 0

-- | Returns the LIB_ID of a LIB_NAME
getModTime :: LIB_ID -> ClockTime
getModTime li = case li of
    Direct_link _ _ -> noTime
    Indirect_link _ _ _ m -> m

updFilePathOfLibId :: FilePath -> ClockTime -> LIB_ID -> LIB_ID
updFilePathOfLibId fp mt li = case li of
  Direct_link _ _ -> li
  Indirect_link p r _ _ -> Indirect_link p r fp mt

data VERSION_NUMBER = Version_number [String] Range deriving (Show, Eq)
                      -- pos: "version", start of first string

type URL = String
type PATH = String

instance GetRange LIB_ID where
  getRange li = case li of
    Direct_link _ r -> r
    Indirect_link _ r _ _ -> r

instance Show LIB_ID where
  show li = case li of
    Direct_link s _ -> s
    Indirect_link s1 _ _ _ -> s1

instance Show LIB_NAME where
  show ln = case ln of
    Lib_version li (Version_number vs _) ->
      shows li $ " version " ++ intercalate "." vs
    Lib_id li -> show li

instance Eq LIB_ID where
  Direct_link s1 _ == Direct_link s2 _ = s1 == s2
  Indirect_link s1 _ _ _ == Indirect_link s2 _ _ _ = s1 == s2
  _ == _ = False

instance Ord LIB_ID where
  Direct_link s1 _ <= Direct_link s2 _ = s1 <= s2
  Indirect_link s1 _ _ _ <= Indirect_link s2 _ _ _ = s1 <= s2
  Direct_link _ _ <= _ = True
  Indirect_link _ _ _ _ <= _ = False

instance Eq LIB_NAME where
  ln1 == ln2 = compare ln1 ln2 == EQ

instance Ord LIB_NAME where
  compare ln1 ln2 = compare (getLIB_ID ln1) $ getLIB_ID ln2

instance Pretty LIB_NAME where
    pretty l = case l of
        Lib_version i v ->
            fsep [pretty i, keyword versionS, pretty v]
        Lib_id i -> pretty i

instance Pretty LIB_ID where
    pretty l = structId $ case l of
        Direct_link u _ -> u
        Indirect_link p _ _ _ -> p

instance Pretty VERSION_NUMBER where
    pretty (Version_number aa _) =
        hcat $ punctuate dot $ map codeToken aa
