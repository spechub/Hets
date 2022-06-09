{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./NeSyPatterns/Sign.hs
Description :  Signatures for syntax for neural-symbolic patterns
Copyright   :  (c) Till Mossakowski, Uni Magdeburg 2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till.mossakowski@ovgu.de
Stability   :  experimental
Portability :  portable

Definition of signatures for neural-symbolic patterns
-}

module NeSyPatternsl.Sign
    (Sign (..)                      -- Signatures
    , id2SimpleId
    , pretty                        -- pretty printing
    , isLegalSignature              -- is a signature ok?
    , addToSig                      -- adds an id to the given Signature
    , unite                         -- union of signatures
    , emptySig                      -- empty signature
    , isSubSigOf                    -- is subsignature?
    , sigDiff                       -- Difference of Signatures
    , sigUnion                      -- Union for Logic.Logic
    ) where

import Data.Data
import Data.List as List
import qualified Data.Set as Set
import qualified Data.Relation as Rel

import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils

import NeSyPatterns.AS


{- | Datatype for propositional Signatures
Signatures are graphs over nodes from the abstract syntax -}
newtype Sign = Sign {nodes :: Set.Set Node,
                     edges :: Rel.Relation Node Node}
  deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty Sign where
    pretty = printSign

id2SimpleId :: Id -> Token
id2SimpleId i = case filter (not . isPlace) $ getTokens i of
  [] -> error "id2SimpleId"
  c : _ -> c

{- | determines whether a signature is vaild -}
isLegalSignature :: Sign -> Bool
isLegalSignature s =
  Rel.dom (edges s) `Set.isSubsetOf` nodes s
  && Rel.ran (edges s) `Set.isSubsetOf` nodes s

-- | pretty printing for Signatures
printSign :: Sign -> Doc
printSign s =
    hsep [sepBySemis $ map pretty $ Set.toList $ nodes s,
          sepBySemis $ map pretty $ Rel.toList $ edges s]

-- | Adds a node to the signature
addToSig :: Sign -> Node -> Sign
addToSig sig node = Sign {nodes = Set.insert node $ nodes sig}

-- | Union of signatures
unite :: Sign -> Sign -> Sign
unite sig1 sig2 = Sign {nodes = Set.union (nodes sig1) $ nodes sig2,
                        edges = Rel.union (edges sig1) $ edges sig2}

-- | The empty signature
emptySig :: Sign
emptySig = Sign {nodes = Set.empty, edges = Rel.empty}

relToSet :: Rel.Relation a b -> Set.Set (a,b)
relToSet r = Set.fromList $ Rel.toList r

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 =
  nodes sig1 `Set.isSubsetOf` nodes sig2
  && relToSet $ edges sig1 `Set.isSubsetOf` relToSet $ edges sig2

relDiff :: Rel.Relation a b -> Rel.Relation a b -> Rel.Relation a b
relDiff r1 r2 = Rel.fromList (l1 List.\\ l2)
   where l1 = Rel.toList r1
         l2 = Rel.toList r2

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = Sign
  {nodes = Set.difference (nodes sig1) $ nodes sig2,
   edges = relDiff (edges sig1) $ edges sig2}

{- | union of Signatures, using Result -}
sigUnion :: Sign -> Sign -> Result Sign
sigUnion s1 = return $ unite s1
