{-| 
   
Module      :  $Header$
Copyright   :  (c) Jorina F. Gerken, Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  jfgerken@tzi.de
Stability   :  provisional
Portability :  non-portable(Logic)

   data types for proofs in development graphs.

-}

module Proofs.Proofs where

import Static.DevGraph
import Data.Graph.Inductive.Graph
import qualified Common.Lib.Map as Map
import Syntax.AS_Library

{-
   proof status = (DG0,[(R1,DG1),...,(Rn,DGn)])
   DG0 is the development graph resulting from the static analysis
   Ri is a list of rules that transforms DGi-1 to DGi
   With the list of intermediate proof states, one can easily implement
    an undo operation
-}

{-type ProofStatus = (GlobalContext,LibEnv,[([DGRule],[DGChange])],DGraph)
umstellen auf:-}

type ProofHistory = [([DGRule],[DGChange])]
type ProofStatus = (LIB_NAME,LibEnv,Map.Map LIB_NAME ProofHistory) 

data DGChange = InsertNode (LNode DGNodeLab)
              | DeleteNode (LNode DGNodeLab)
              | InsertEdge (LEdge DGLinkLab)
              | DeleteEdge (LEdge DGLinkLab)
  deriving (Eq,Show)