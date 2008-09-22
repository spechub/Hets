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

import Common.Id
import Common.Doc
import Common.DocUtils
import Common.Keywords
import System.Time
import Data.List

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

instance Show LIB_ID where
  show (Direct_link s1 _) = s1
  show (Indirect_link s1 _ _ _) = s1

instance Show LIB_NAME where
  show (Lib_version libid (Version_number vs _)) =
      shows libid " version " ++ concat (intersperse "." vs)
  show (Lib_id libid) = show libid

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
  ln1 == ln2 = getLIB_ID ln1 == getLIB_ID ln2

instance Ord LIB_NAME where
  ln1 <= ln2 = getLIB_ID ln1 <= getLIB_ID ln2

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
