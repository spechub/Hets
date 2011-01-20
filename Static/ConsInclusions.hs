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

import Logic.Coerce
import Logic.Logic
import Logic.Prover

import Common.Consistency
import Common.Doc
import Common.DocUtils
import Common.ExtSign

import Data.Graph.Inductive.Graph as Graph
import Data.Maybe
import qualified Data.Set as Set

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
   case g1 of
     G_theory lid1 sig1 _ _ _ -> case dgn_theory tar of
       G_theory lid2 sig2 _ sens2 _ -> do
           insig <- coerceSign lid1 lid2 "dumpConsIncl" sig1
           let syms = concatMap (Set.toList .
                     (`Set.difference` symset_of lid2 (plainSign insig)))
                       (sym_of lid2 $ plainSign sig2)
               sens = toNamedList sens2
           writeVerbFile opts file
             $ show $ useGlobalAnnos ga $ vcat
             [ text $ "spec source_" ++ nm ++ " ="
             , prettyGTheory g1
             , text "end"
             , text $ "spec target_" ++ nm ++ " = source_" ++ nm
             , text "then %cons"
             , if null syms && null sens then text "{}" else
                   vcat $ map pretty syms ++ map (print_named lid2) sens ]
