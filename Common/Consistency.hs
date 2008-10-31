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
import Common.AS_Annotation
import Common.Result

data ConsistencyStatus =
  Inconsistent | Conservative | Monomorphic | Definitional | Unknown String
  deriving (Show, Eq, Ord)

showToComply :: ConsistencyStatus -> String
showToComply cons =
    case cons of
      Conservative -> "Cons"
      Monomorphic  -> "Mono"
      Definitional -> "Def"
      _            -> "dunno"

showConsistencyStatus :: ConsistencyStatus -> String
showConsistencyStatus cs = case cs of
  Inconsistent -> "not conservative"
  Unknown str  -> "unkown if being conservative. Cause is : " ++ str
  _ -> map toLower $ show cs

instance Pretty ConsistencyStatus where
  pretty = text . showConsistencyStatus

data ConservativityChecker sign sentence morphism = ConservativityChecker
                           {
                             checker_id          :: String
                           , checkConservativity :: (sign, [Named sentence])
                                                 -> morphism
                                                 -> [Named sentence]
                                                 -> Result
                                                    (Maybe
                                                     (ConsistencyStatus
                                                     ,[sentence]))
                           }
