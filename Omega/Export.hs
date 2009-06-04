{- |
Module      :  $Header$
Description :  export a development graph to an omega library
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

A given development graph will be exported to an omega library.
The structure of the development graph is expected to satisfy additional
requirements. The form of the specs should be the following:

spec <name> = spec-ref_1 and ... and spec-ref_n then basic-spec

n can also be 0 or 1.
-}

module Omega.Export
    ( exportDGraph
    , exportNodeLab
    ) where

import Logic.Coerce
import qualified Logic.Prover as P
--import Logic.Logic
--import Logic.Grothendieck
--import Logic.Comorphism

import HasCASL.Logic_HasCASL
import qualified HasCASL.Le as Le

import Static.DevGraph
import Static.GTheory

import Common.Id
import Common.ExtSign
import Common.LibName
import Common.AS_Annotation

import Omega.DataTypes
import Omega.Terms

import Data.Graph.Inductive.Graph
import Data.List
import Data.Maybe
import qualified Data.Map as Map

-- | DGraph to Omega Library translation
exportDGraph :: LIB_NAME -> DGraph -> Library
exportDGraph ln dg =
    let libid = (getLIB_ID ln)
    in
      Library (show libid)
                  $ catMaybes $ map (exportNodeLab libid dg)
                  $ topsortedNodes dg

-- | DGNodeLab to Theory translation
exportNodeLab :: LIB_ID -> DGraph -> LNode DGNodeLab -> Maybe Theory
exportNodeLab _ dg (n, lb) =
    justWhen (not $ isDGRef lb) $
    case dgn_theory lb of
      G_theory lid (ExtSign sign _) _ sens _ ->
          let theoryname = getDGNodeName lb
              msg = "Omega Export: Try to coerce to HasCASL!"
              e = error msg
              (signature, sentences) =
                  fromMaybe e $
                  coerceBasicTheory lid HasCASL msg (sign, P.toNamedList sens)
          in Theory theoryname
                 (catMaybes (map (makeImport dg) $ innDG dg n))
                 $ exportSign signature ++ exportSens sentences

exportSign :: Le.Env -> [TCElement]
-- need to filter the elements which are not locally defined but imported!
exportSign Le.Env{ Le.assumps = ops } = map (TCSymbol . show) $ Map.keys ops

exportSens :: [Named Le.Sentence] -> [TCElement]
exportSens = catMaybes . (map exportSen)

exportSen :: (Named Le.Sentence) -> Maybe TCElement
exportSen SenAttr
  { senAttr = name
  , isAxiom = isAx
  , sentence = (Le.Formula t) }
    = Just $ TCAxiomOrTheorem (not isAx) name $ toTerm t
exportSen _ = Nothing

makeImport :: DGraph -> LEdge DGLinkLab -> Maybe String
makeImport dg (from, _, lbl) =
  justWhen (isGlobalDef $ dgl_type lbl) $ getDGNodeName $ labDG dg from

