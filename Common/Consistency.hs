{- |
Module      :  $Header$
Description :  data types for consistency aka conservativity
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Data types for conservativity
-}

module Common.Consistency where

import Data.Char (toLower)
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation
import Common.Result

{- | Conservativity annotations. For compactness, only the greatest applicable
     value is used in a DG. PCons stands for prooftheoretic conservativity as
     required for extending imports (no confusion) in Maude -}
data Conservativity =
    Inconsistent
  | Unknown String
  | None
  | PCons
  | Cons
  | Mono
  | Def
    deriving (Show, Eq, Ord)

showToComply :: Conservativity -> String
showToComply = show

showConsistencyStatus :: Conservativity -> String
showConsistencyStatus cs = case cs of
  Inconsistent -> "not conservative"
  Unknown str  -> "unkown if being conservative. Cause is : " ++ str
  _ -> map toLower $ show cs

instance Pretty Conservativity where
  pretty = text . showConsistencyStatus

data ConservativityChecker sign sentence morphism = ConservativityChecker
    { checker_id :: String
    , checkConservativity
        :: (sign, [Named sentence])
        -> morphism
        -> [Named sentence]
        -> Result (Maybe (Conservativity, [sentence])) }
