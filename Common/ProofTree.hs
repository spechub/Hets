{-# LANGUAGE DeriveDataTypeable, FlexibleInstances #-}
{- |
Module      :  ./Common/ProofTree.hs
Description :  a simple proof tree
Copyright   :  (c) DFKI GmbH, Uni Bremen 2002-2008, Tom Kranz 2021-2022
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via DeriveDataTypeable, FlexibleInstances)

Datatype for storing of the proof tree.
  Actual proof tree (dag) structures can be printed as dot (Graphviz) digraphs.
-}

module Common.ProofTree ( ProofTree(ProofTree,ProofGraph)
                        , ProofGraphNode
                        , emptyProofTree
                        ) where

import Data.Data
import Data.List (intercalate)
import Data.Graph.Inductive.PatriciaTree (Gr)
import Data.Graph.Inductive.Graph
import ATerm.Lib

import Text.Printf

-- This should be
-- data ProofgraphNode = ProofGraphInference String | ProofGraphSentence String String
-- but ShATermConvertible doens't like to be instantiated this way.
type ProofGraphNode = Either String (String,String)
data ProofTree = ProofTree String | ProofGraph (Gr ProofGraphNode Int) deriving (Eq, Typeable)

instance Ord ProofTree where
  compare (ProofTree _) (ProofGraph _) = LT
  compare (ProofGraph _) (ProofTree _) = GT
  compare (ProofTree s) (ProofTree s') = compare s s'
  compare (ProofGraph g) (ProofGraph g') = compare (OrdGr g) (OrdGr g')

instance ShATermConvertible (Gr ProofGraphNode Int) where
  toShATermAux att0 xv = do
    (att1, a') <- toShATerm' att0 (labNodes xv, labEdges xv)
    return $ addATerm (ShAAppl "PatriciaTree.Gr" [a'] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
    ShAAppl "PatriciaTree.Gr" [a] _ ->
      case fromShATerm' a att0 of
      { (att1, (aNodes,aEdges)) ->
      (att1, mkGraph aNodes aEdges) }
    u -> fromShATermError "PatriciaTree.Gr" u

instance Show ProofTree where
  show (ProofTree st) = st
  -- This is a dot graph description
  show (ProofGraph gr) =
    "digraph {\n"
    ++ concatMap dotNode (labNodes gr)
    ++ concatMap dotEdge (labEdges gr)
    ++ dotSubgraph (axiomInferences gr)
    ++ dotSubgraph (axiomSentences gr)
    ++ "}\n"
      where
        dotNode :: LNode ProofGraphNode -> String
        dotNode (i,l) = (printf :: String -> Int -> String -> String -> String -> String) "%d [shape=%s,tooltip=\"%s\",label=\"%s\"];\n" i (nShape l) (xShow l) (lShow l)
        dotEdge :: LEdge Int -> String
        dotEdge (s,t,i) = (printf :: String -> Int -> Int -> Int -> String) "%d -> %d [label=\"%d\"];\n" s t i
        dotSubgraph :: [Node] -> String
        dotSubgraph [] = ""
        dotSubgraph ns = (printf :: String -> String -> String) "subgraph { rank = same; %s }\n" (intercalate "; " (map show ns))
        axiomInferences :: Graph g => g a b -> [Node]
        axiomInferences g = filter ((==0).indeg g) (nodes g)
        axiomSentences :: Graph g => g a b -> [Node]
        axiomSentences g = concatMap (suc g) (axiomInferences g)
        escape :: String -> String
        escape = concatMap (\c->(if c=='"' || c=='\\' then "\\" else [])++[c])
        lString :: ProofGraphNode -> String
        lString (Left s) = s
        lString (Right (s,_)) = s
        lShow :: ProofGraphNode -> String
        lShow = escape.lString
        xString :: ProofGraphNode -> String
        xString (Left _) = ""
        xString (Right (_,s)) = s
        xShow :: ProofGraphNode -> String
        xShow = escape.xString
        nShape :: ProofGraphNode -> String
        nShape (Left _) = "box"
        nShape (Right _) = "oval"

emptyProofTree :: ProofTree
emptyProofTree = ProofGraph empty
