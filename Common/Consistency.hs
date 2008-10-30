{- |
Module      :  $Header$
Description :  data types for consistency
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Data types for consistency
-}

module Common.Consistency where

import Data.Char (toLower)
import Common.Doc
import Common.DocUtils

data ConsistencyStatus =
  Inconsistent | Conservative | Monomorphic | Definitional | Unknown String
  deriving (Show, Eq, Ord)

showConsistencyStatus :: ConsistencyStatus -> String
showConsistencyStatus cs = case cs of
  Inconsistent -> "not conservative"
  Unknown str  -> "unkown if being conservative. Cause is : " ++ str
  _ -> map toLower $ show cs

instance Pretty ConsistencyStatus where
  pretty = text . showConsistencyStatus
