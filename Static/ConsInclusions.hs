{- |
Module      :  $Header$
Description :  dump conservative inclusion links
Copyright   :  (c) C. Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}
module Static.ConsInclusions (dumpConsInclusions) where

import Static.DevGraph

import Driver.Options

import Data.Graph.Inductive.Graph as Graph

dumpConsInclusions opts dg =
  mapM (dumpConsIncl opts dg )
  $ filter (\ (_, _, l) -> let e = getRealDGLinkType l in
               isInc e && edgeTypeModInc e == GlobalDef
           )
  $ labEdgesDG dg

dumpConsIncl :: HetcatsOpts -> DGraph -> LEdge DGLinkLab -> IO ()
dumpConsIncl = undefined

