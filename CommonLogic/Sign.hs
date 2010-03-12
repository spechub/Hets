{- |
Module      :  $Header$
Description :  Signature for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for common logic
-}

module CommonLogic.Sign
    (Sign (..)                     --
    ,pretty                        -- pretty printing
    ,emptySig                      -- empty signature
    ) where

import qualified Data.Set as Set
import Common.Id
import Common.Doc
import Common.DocUtils

-- | Datatype for propositional Signatures
-- Signatures are just sets
newtype Sign = Sign {items :: Set.Set Id} deriving (Eq, Ord, Show)

instance Pretty Sign where
    pretty = printSign

-- | The empty signature
emptySig :: Sign
emptySig = Sign {items = Set.empty}

-- | pretty printing for Signatures
printSign :: Sign -> Doc
printSign s =
    hsep [text "prop", sepByCommas $ map pretty $ Set.toList $ items s]
