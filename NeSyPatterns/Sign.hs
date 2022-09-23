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

module NeSyPatterns.Sign
    (Sign (..)                      -- Signatures6
    , ResolvedNode(..)
    , resolved2Node
    , findNodeId
    , nesyIdMap
    , pretty                        -- pretty printing
    , isLegalSignature              -- is a signature ok?
    , addToSig                      -- adds an id to the given Signature
    , addEdgeToSig                  -- adds an edge to the given signature
    , addEdgeToSig'                 -- adds an edge and its nodes to the given signature
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
import qualified Data.Map as Map

import Common.Id
import Common.Result
import Common.Doc
import Common.DocUtils
import Common.SetColimit
import Common.IRI
import Common.Keywords

import NeSyPatterns.AS
import NeSyPatterns.Print()

import OWL2.AS
import OWL2.Pretty


data ResolvedNode = ResolvedNode {
    resolvedOTerm :: IRI,
    resolvedNeSyId :: IRI,
    resolvedNodeRange :: Range
  } deriving (Show, Eq, Ord, Typeable, Data)

instance SymbolName ResolvedNode where
  addString (ResolvedNode t1 t2 r, s) = ResolvedNode t1 (addSuffixToIRI s t2) r

instance Pretty ResolvedNode where
  pretty (ResolvedNode o i r) = pretty $ Node o (Just i) r

instance GetRange ResolvedNode where
  getRange = const nullRange
  rangeSpan x = case x of
    ResolvedNode a b c -> joinRanges [rangeSpan a, rangeSpan b, rangeSpan c]

{- | Datatype for propositional Signatures
Signatures are graphs over nodes from the abstract syntax -}
data Sign = Sign { owlClasses :: Set.Set IRI,
                   owlTaxonomy :: Rel.Relation IRI IRI,
                   nodes :: Set.Set ResolvedNode,
                   edges :: Rel.Relation ResolvedNode ResolvedNode,
                   idMap :: Map.Map IRI IRI }
  deriving (Show, Eq, Ord, Typeable)

instance Pretty Sign where
    pretty = printSign

findNodeId :: IRI -> Set.Set ResolvedNode -> Set.Set ResolvedNode
findNodeId t = Set.filter (\(ResolvedNode _ t1 _) -> t == t1 )

nesyIds :: Sign -> Set.Set IRI
nesyIds = Set.map resolvedNeSyId . nodes

nesyIdMap :: Set.Set ResolvedNode -> Map.Map IRI IRI
nesyIdMap ns = Map.fromList [(i, o) | ResolvedNode o i _ <- Set.toList ns]

resolved2Node :: ResolvedNode -> Node
resolved2Node (ResolvedNode t i r) = Node t (Just i) r

-- | Builds the owl2 ontology from a signature
getOntology :: Sign -> OntologyDocument
getOntology s = let
    decls = Declaration [] . mkEntity Class <$> Set.toList (owlClasses s)
    subClasses = fmap (\(a,b) -> SubClassOf [] (Expression a) (Expression b)) $ Rel.toList (owlTaxonomy s)
    subClassAxs = ClassAxiom <$> subClasses
    axs = decls ++ subClassAxs
  in emptyOntologyDoc { ontology = emptyOntology { axioms = axs}}

{- | determines whether a signature is vaild -}
isLegalSignature :: Sign -> Bool
isLegalSignature s =
  Rel.dom (edges s) `Set.isSubsetOf` nodes s
  && Rel.ran (edges s) `Set.isSubsetOf` nodes s

-- | pretty printin for edge e.g. tuple (ResolvedNode, ResolvedNode)
printEdge :: (ResolvedNode, ResolvedNode) -> Doc
printEdge (node1, node2) = pretty node1 <+> text "->" <+> pretty node2 <> semi
  -- (fsep . punctuate (text " ->") $ map pretty [node1, node2]) <> semi

-- | pretty printing for Signatures
printSign :: Sign -> Doc
printSign s = keyword dataS <+> (specBraces . toDocAsMS . getOntology $ s) $+$
    (vcat . map printEdge . Rel.toList . edges $ s) $+$
    (vcat . map ((<> semi) . pretty) . Set.toList $ (nodes s Set.\\ Set.union (Rel.dom . edges $ s) (Rel.ran . edges $ s)))

-- | Adds a node to the signature
addToSig :: Sign -> ResolvedNode -> Sign
addToSig sig node = sig {nodes = Set.insert node $ nodes sig}

-- | Adds an edge to the signature. Nodes are not added. See addEdgeToSig' 
addEdgeToSig :: Sign -> (ResolvedNode, ResolvedNode) -> Sign
addEdgeToSig sig (f, t) = sig {edges = Rel.insert f t $ edges sig}

-- | Adds an edge with its nodes to the signature
addEdgeToSig' :: Sign -> (ResolvedNode, ResolvedNode) -> Sign
addEdgeToSig' sig (f, t) = addToSig (addToSig (sig {edges = Rel.insert f t $ edges sig}) f) t

-- | Union of signatures
unite :: Sign -> Sign -> Sign
unite sig1 sig2 = Sign {owlClasses = Set.union (owlClasses sig1) $ owlClasses sig2,
                        owlTaxonomy = Rel.union (owlTaxonomy sig1) $ owlTaxonomy sig2,
                        nodes = Set.union (nodes sig1) $ nodes sig2,
                        idMap = Map.union (idMap sig1) $ idMap sig2,
                        edges = Rel.union (edges sig1) $ edges sig2}

-- | The empty signature
emptySig :: Sign
emptySig = Sign { owlClasses = Set.empty
                , owlTaxonomy = Rel.empty
                , nodes = Set.empty
                , edges = Rel.empty
                , idMap = Map.empty}

relToSet :: (Ord a, Ord b) => Rel.Relation a b -> Set.Set (a,b)
relToSet r = Set.fromList $ Rel.toList r

-- | Determines if sig1 is subsignature of sig2
isSubSigOf :: Sign -> Sign -> Bool
isSubSigOf sig1 sig2 =
     owlClasses sig1 `Set.isSubsetOf` owlClasses sig2
  && nodes sig1 `Set.isSubsetOf` nodes sig2
  && relToSet (edges sig1) `Set.isSubsetOf` relToSet (edges sig2)
  && relToSet (owlTaxonomy sig1) `Set.isSubsetOf` relToSet (owlTaxonomy sig2)

relDiff :: (Ord a, Ord b) => Rel.Relation a b -> Rel.Relation a b -> Rel.Relation a b
relDiff r1 r2 = Rel.fromList (l1 List.\\ l2)
   where l1 = Rel.toList r1
         l2 = Rel.toList r2

-- | difference of Signatures
sigDiff :: Sign -> Sign -> Sign
sigDiff sig1 sig2 = Sign
  {owlClasses = Set.difference (owlClasses sig1) $ owlClasses sig2,
   owlTaxonomy = relDiff (owlTaxonomy sig1) $ owlTaxonomy sig2,
   nodes = Set.difference (nodes sig1) $ nodes sig2,
   idMap = Map.difference (idMap sig1) $ idMap sig2,
   edges = relDiff (edges sig1) $ edges sig2}

{- | union of Signatures, using Result -}
sigUnion :: Sign -> Sign -> Result Sign
sigUnion s1 s2 = return $ unite s1 s2
