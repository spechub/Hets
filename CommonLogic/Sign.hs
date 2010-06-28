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
    ,isSubSigOf                    -- 
    ,sigDiff                       -- Difference of Signatures
    ,unite                         -- union of signatures
    ,uniteL                        -- union of a list ofsignatures
    ,sigUnion                      -- Union for Logic.Logic
    ,isSeqMark                     -- is sequence marker?
    ,sigUnionL                     -- union of a list ofsignatures
    ) where

import qualified Data.Set as Set
import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

-- | Datatype for common logic Signatures
--TODO: function testing whether an ID is a sequence marker
newtype Sign = Sign {items :: Set.Set Id} deriving (Eq, Ord, Show)

instance Pretty Sign where
    pretty = printSign

-- | The empty signature
emptySig :: Sign
emptySig = Sign {items = Set.empty}

-- | pretty printing for Signatures
printSign :: Sign -> Doc
printSign s =
    hsep [text "vocabulary", sepByCommas $ map pretty $ Set.toList $ items s]

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 = Set.isSubsetOf (items sig1) $ items sig2

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = Sign{items = Set.difference (items sig1) $ items sig2}

-- | 
sigUnion :: Sign -> Sign -> Result Sign
sigUnion s1 = Result [Diag Debug "All fine sigUnion" nullRange]
      . Just . unite s1

-- | 
sigUnionL :: [Sign] -> Result Sign
sigUnionL (sig : sigL) = sigUnion sig (uniteL sigL)
sigUnionL [] = return emptySig

unite :: Sign -> Sign -> Sign
unite sig1 sig2 = Sign {items = Set.union (items sig1) $ items sig2}

--TODO:
isSeqMark :: Id -> Bool
isSeqMark _ = True

uniteL :: [Sign] -> Sign
uniteL = foldr unite emptySig