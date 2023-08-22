{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./CommonLogic/Sign.hs
Description :  Signature for common logic
Copyright   :  (c) Karl Luc, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for common logic
-}

module CommonLogic.Sign
    (Sign (..)
    , pretty                        -- pretty printing
    , allItems                      -- union of all signature-fields
    , emptySig                      -- empty signature
    , isSubSigOf                    -- sub signature of signature
    , sigDiff                       -- Difference of Signatures
    , unite                         -- union of signatures
    , uniteL                        -- union of a list ofsignatures
    , sigUnion                      -- Union for Logic.Logic
    , sigUnionL                     -- union of a list ofsignatures
    , isSeqMark                     -- is an Id a sequence marker?
    ) where

import qualified Data.Set as Set
import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

import Data.Data
import Data.List (isPrefixOf)

-- | Datatype for common logic Signatures

data Sign = Sign { discourseNames :: Set.Set Id
                 , nondiscourseNames :: Set.Set Id
                 , sequenceMarkers :: Set.Set Id
                 } deriving (Eq, Ord, Show, Typeable)

instance Pretty Sign where
    pretty = printSign

-- | union of all signature-fields
allItems :: Sign -> Set.Set Id
allItems s = Set.unions $ map (\ f -> f s) [ discourseNames
                                          , nondiscourseNames
                                          , sequenceMarkers
                                          ]

-- | The empty signature
emptySig :: Sign
emptySig = Sign { discourseNames = Set.empty
                , nondiscourseNames = Set.empty
                , sequenceMarkers = Set.empty
                }

-- | pretty printing for Signatures
printSign :: Sign -> Doc
printSign s =
  vsep [ text "%{"
       , text "discourseNames: "
          <+> sepByCommas (map pretty $ Set.toList $ discourseNames s)
       , text "nondiscourseNames: "
          <+> sepByCommas (map pretty $ Set.toList $ nondiscourseNames s)
       , text "sequenceMarkers: "
          <+> sepByCommas (map pretty $ Set.toList $ sequenceMarkers s)
       , text "}%"]

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 =
  Set.isSubsetOf (discourseNames sig1) (discourseNames sig2)
  && Set.isSubsetOf (nondiscourseNames sig1) (nondiscourseNames sig2)
  && Set.isSubsetOf (sequenceMarkers sig1) (sequenceMarkers sig2)

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = Sign {
  discourseNames = Set.difference (discourseNames sig1) (discourseNames sig2),
  nondiscourseNames = Set.difference (nondiscourseNames sig1) (nondiscourseNames sig2),
  sequenceMarkers = Set.difference (sequenceMarkers sig1) (sequenceMarkers sig2)
}

-- | Unite Signatures
sigUnion :: Sign -> Sign -> Result Sign
sigUnion s1 = Result [Diag Debug "All fine sigUnion" nullRange]
      . Just . unite s1

-- | Unite Signature in a list
sigUnionL :: [Sign] -> Result Sign
sigUnionL (sig : sigL) = sigUnion sig (uniteL sigL)
sigUnionL [] = return emptySig

-- | Union of two signatures. Behaves like Set.union, i.e. is fast with @bigsig `union` smallsig@.
unite :: Sign -> Sign -> Sign
unite sig1 sig2 = Sign
  { discourseNames = discourseNames sig1 `Set.union` discourseNames sig2
  , nondiscourseNames = nondiscourseNames sig1 `Set.union` nondiscourseNames sig2
  , sequenceMarkers = sequenceMarkers sig1 `Set.union` sequenceMarkers sig2
  }

-- | Union of a list of signatures.
uniteL :: [Sign] -> Sign
uniteL = foldr unite emptySig

isSeqMark :: Id -> Bool
isSeqMark = isStringSeqMark . tokStr . idToSimpleId

-- | Checks whether a String is a sequence marker
isStringSeqMark :: String -> Bool
isStringSeqMark s = "..." `isPrefixOf` s
