{-# LANGUAGE StandaloneDeriving, DeriveDataTypeable #-}
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

module NeSyPatterns.Sign
    (Sign (..)                      -- Signatures
    , ResolvedNode(..)
    , id2SimpleId
    , pretty                        -- pretty printing
    , isLegalSignature              -- is a signature ok?
    , addToSig                      -- adds an id to the given Signature
    , addEdgeToSig                  -- adds an edge to the given signature
    , unite                         -- union of signatures
    , emptySig                      -- empty signature
    , isSubSigOf                    -- is subsignature?
    , sigDiff                       -- Difference of Signatures
    , sigUnion                      -- Union for Logic.Logic
    , nesyIds                       -- extracts the ids of all nodes of a signature
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
import NeSyPatterns.Print()


data ResolvedNode = ResolvedNode {
    resolvedOTerm :: Token,
    resolvedNeSyId :: Token,
    resolvedNodeRange :: Range
  } deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty ResolvedNode where
  pretty (ResolvedNode o i r) = pretty $ Node (Just o) (Just i) r

instance GetRange ResolvedNode where
  getRange = const nullRange
  rangeSpan x = case x of
    ResolvedNode a b c -> joinRanges [rangeSpan a, rangeSpan b, rangeSpan c]

{- | Datatype for propositional Signatures
Signatures are graphs over nodes from the abstract syntax -}
data Sign = Sign { nodes :: Set.Set ResolvedNode,
                    edges :: Rel.Relation ResolvedNode ResolvedNode}
  deriving (Show, Eq, Ord, Typeable)

instance Pretty Sign where
    pretty = printSign

nesyIds :: Sign -> Set.Token
nesyIds = fmap resolvedNeSyId . nodes

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
addToSig :: Sign -> ResolvedNode -> Sign
addToSig sig node = sig {nodes = Set.insert node $ nodes sig}

-- | Adds an edge to the signature. Nodes are not added. See addEdgeToSig' 
addEdgeToSig' :: Sign -> (ResolvedNode, ResolvedNode) -> Sign
addEdgeToSig sig (f, t) = sig {edges = Rel.insert f t $ edges sig}

-- | Adds an edge with its nodes to the signature
addEdgeToSig' :: Sign -> (ResolvedNode, ResolvedNode) -> Sign
addEdgeToSig' sig (f, t) = addToSig (addToSig (sig {edges = Rel.insert f t $ edges sig}) f) t

-- | Union of signatures
unite :: Sign -> Sign -> Sign
unite sig1 sig2 = Sign {nodes = Set.union (nodes sig1) $ nodes sig2,
                        edges = Rel.union (edges sig1) $ edges sig2}

-- | The empty signature
emptySig :: Sign
emptySig = Sign {nodes = Set.empty, edges = Rel.empty}

relToSet :: (Ord a, Ord b) => Rel.Relation a b -> Set.Set (a,b)
relToSet r = Set.fromList $ Rel.toList r

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 =
  nodes sig1 `Set.isSubsetOf` nodes sig2
  && relToSet (edges sig1) `Set.isSubsetOf` relToSet (edges sig2)

relDiff :: (Ord a, Ord b) => Rel.Relation a b -> Rel.Relation a b -> Rel.Relation a b
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
sigUnion s = return . unite s
