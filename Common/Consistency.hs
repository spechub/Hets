{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./Common/Consistency.hs
Description :  data types for consistency aka conservativity
Copyright   :  (c) Christian Maeder, DFKI GmbH 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Data types for conservativity
-}

module Common.Consistency where

import Common.Doc
import Common.DocUtils
import Common.AS_Annotation
import Common.Result

import GHC.Generics (Generic)
import Data.Hashable
import Data.Data

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
    deriving (Show, Read, Eq, Ord, Typeable, Data, Generic)

instance Hashable Conservativity

showConsistencyStatus :: Conservativity -> String
showConsistencyStatus cs = case cs of
  Inconsistent -> "not conservative"
  Unknown str -> "unknown if being conservative. Cause is : " ++ str
  None -> "unknown if being conservative"
  Cons -> "conservative"
  PCons -> "proof-theoretically conservative"
  Mono -> "monomorphic"
  Def -> "definitional"

instance Pretty Conservativity where
  pretty = text . showConsistencyStatus

{- | All target sentences must be implied by the source translated
along the morphism. They are axioms only and not identical to any
translated sentence of the source. -}
data ConservativityChecker sign sentence morphism = ConservativityChecker
    { checkerId :: String
    , checkerUsable :: IO (Maybe String)
    , checkConservativity
        :: (sign, [Named sentence])
        -> morphism
        -> [Named sentence]
        -> IO (Result (Conservativity, [sentence])) }
