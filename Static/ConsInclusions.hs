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
import Static.GTheory

import Driver.Options
import Driver.WriteFn

import Common.Consistency
import Common.Doc
import Common.DocUtils

import Data.Graph.Inductive.Graph as Graph
import Data.Maybe

dumpConsInclusions :: HetcatsOpts -> DGraph -> IO ()
dumpConsInclusions opts dg =
  mapM_ (dumpConsIncl opts dg)
  $ filter (\ (_, _, l) -> let e = getRealDGLinkType l in
               isInc e && edgeTypeModInc e == GlobalDef
           && getCons (dgl_type l) == Cons
           )
  $ labEdgesDG dg

dumpConsIncl :: HetcatsOpts -> DGraph -> LEdge DGLinkLab -> IO ()
dumpConsIncl opts dg (s, t, l) = do
   let src = labDG dg s
       tar = labDG dg t
       ga = globalAnnos dg
       nm = showEdgeId (dgl_id l)
       file = "ConsIncl_" ++ nm ++ ".het"
       g1 = fromMaybe (dgn_theory src) $ globalTheory src
       g2 = fromMaybe (dgn_theory tar) $ globalTheory tar
   writeVerbFile opts file
             $ show $ useGlobalAnnos ga $ vcat
             [ text $ "spec source_" ++ nm ++ " ="
             , prettyGTheory g1
             , text "end"
             , text $ "spec target_" ++ nm ++ " = source_" ++ nm
             , text "then %cons"
             , prettyGTheory g2 ]
