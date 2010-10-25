{- |
Module      :  $Header$
Description :  Signature for HolLight logic
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

Definition of signatures for HolLight logic

  Ref.

  <http://www.cl.cam.ac.uk/~jrh13/hol-light/>

-}

module HolLight.Sign
    (Sign (..)                     -- HolLight Signatures
    ,pretty                        -- pretty printing
    ,emptySig                      -- empty signature
    ,isSubSig                    -- is subsignature?
    ,sigUnion
    ) where

import qualified Data.Set as Set
import Common.DocUtils
import Common.Doc

-- | Datatype for HolLight Signatures
--
newtype Sign = Sign {items :: Set.Set String} deriving (Eq, Ord, Show)

instance Pretty Sign where
    pretty _ = empty

-- | determines whether a signature is vaild
-- all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True

-- | The empty signature
emptySig :: Sign
emptySig = Sign {items = Set.empty}

-- | Determines if sig1 is subsignature of sig2
isSubSig :: Sign -> Sign -> Bool
isSubSig sig1 sig2 = Set.isSubsetOf (items sig1) $ items sig2

sigUnion :: Sign -> Sign -> Sign
sigUnion s1 s2 = Sign (Set.union (items s1) (items s2))
