{- |
Module      :  $Header$
Description :  Signature for propositional logic
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

Definition of signatures for CSL logic, which are just lists of operators
-}

module CSL.Sign
    (Sign (..)                     -- Propositional Signatures
    ,pretty                        -- pretty printing
    ,isLegalSignature              -- is a signature ok?
    ,addToSig                      -- adds an id to the given Signature
    ,unite                         -- union of signatures
    ,emptySig                      -- empty signature
    ,isSubSigOf                    -- is subsiganture?
    ,sigDiff                       -- Difference of Signatures
    ,sigUnion                      -- Union for Logic.Logic
    ,lookupSym
    ) where

import qualified Data.Set as Set
import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

-- | Datatype for CSL Signatures
-- Signatures are just sets of Tokens for the operators
newtype Sign = Sign {items :: Set.Set Id} deriving (Eq, Ord, Show)

instance Pretty Sign where
    pretty = printSign

-- | checks whether a Id is declared in the signature
lookupSym :: Sign -> Id -> Bool
lookupSym (Sign s) item = Set.member item s

-- | pretty printer for CSL signatures
printSign :: Sign -> Doc
printSign s =
    hsep [text "operator", sepByCommas $ map pretty $ Set.toList $ items s]

-- | determines whether a signature is valid. all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True

-- | Basic function to extend a given signature by adding an item (id) to it
addToSig :: Sign -> Id -> Sign
addToSig sig tok = Sign {items = Set.insert tok $ items sig}

-- | Union of signatures
unite :: Sign -> Sign -> Sign
unite sig1 sig2 = Sign {items = Set.union (items sig1) $ items sig2}

-- | The empty signature
emptySig :: Sign
emptySig = Sign {items = Set.empty}

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 = Set.isSubsetOf (items sig1) $ items sig2

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = Sign{items = Set.difference (items sig1) $ items sig2}

-- | union of Signatures
-- or do I have to care about more things here?
sigUnion :: Sign -> Sign -> Result Sign
sigUnion s1 = Result [Diag Debug "All fine sigUnion" nullRange]
    . Just . unite s1
