{- |
Module      :  $Header$
Description :  signatures with symbol sets
Copyright   :  (c) DFKI GmbH, Uni Bremen 2002-2007
License     :  GPLv2 or higher
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Some functions that operate over signatures need to be extended to work over
signatures with symbol sets for every logic
-}

module Common.ExtSign where

import qualified Data.Set as Set
import Common.Doc
import Common.DocUtils

-- | signatures with symbol sets.
-- (The Ord instance is needed for the ATC generation)
data ExtSign sign symbol = ExtSign
  { plainSign :: sign
  , nonImportedSymbols :: Set.Set symbol
  } deriving Show

instance (Ord sign) => Eq (ExtSign sign symbol) where
    a == b = compare a b == EQ

instance (Ord sign) => Ord (ExtSign sign symbol) where
  compare (ExtSign s1 _) (ExtSign s2 _) = compare s1 s2

instance (Pretty sign, Pretty symbol)
    => Pretty (ExtSign sign symbol) where
  pretty (ExtSign s sys) =
    sep [pretty s, if Set.null sys then empty else pretty sys]

mkExtSign :: sign -> ExtSign sign symbol
mkExtSign s = ExtSign s Set.empty
