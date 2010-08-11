{- |
Module      :  $Header$
Description :  Signature for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for propositional logic
-}
{-
  Ref.

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.Sign
    (Sign (..)                     -- Propositional Signatures
    ,id2SimpleId
    ,pretty                        -- pretty printing
    ,isLegalSignature              -- is a signature ok?
    ,addToSig                      -- adds an id to the given Signature
    ,unite                         -- union of signatures
    ,emptySig                      -- empty signature
    ,isSubSigOf                    -- is subsiganture?
    ,sigDiff                       -- Difference of Signatures
    ,sigUnion                      -- Union for Logic.Logic
    ) where

import qualified Data.Set as Set
import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

-- | Datatype for propositional Signatures
-- Signatures are just sets
newtype Sign = Sign {items :: Set.Set Id} deriving (Eq, Ord, Show)

instance Pretty Sign where
    pretty = printSign

id2SimpleId :: Id -> Token
id2SimpleId i = case filter (not . isPlace) $ getTokens i of
  [] -> error "id2SimpleId"
  c : _ -> c

-- | determines whether a signature is vaild
-- all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True

-- | pretty printing for Signatures
printSign :: Sign -> Doc
printSign s =
    hsep [text "prop", sepByCommas $ map pretty $ Set.toList $ items s]

-- | Adds an Id to the signature
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
