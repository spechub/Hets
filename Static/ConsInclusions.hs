{- |
Module      :  ./Static/ConsInclusions.hs
Description :  dump conservative inclusion links
Copyright   :  (c) C. Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via imports)

-}
module Static.ConsInclusions (dumpConsInclusions) where

import Static.DevGraph
import Static.DgUtils
import Static.GTheory

import Driver.Options
import Driver.WriteFn

import Logic.Coerce
import Logic.Grothendieck
import Logic.Logic

import Common.Consistency
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.Result
import qualified Common.OrderedMap as OMap

import Data.Graph.Inductive.Graph as Graph
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
       file = "ConsIncl_" ++ nm ++ ".dol"
       g1 = globOrLocTh src
       g2 = globOrLocTh tar
   case g1 of
     G_theory lid1 _ sig1 _ sens1 _ -> case g2 of
       G_theory lid2 syn sig2 _ sens2 _ -> do
           insig <- coerceSign lid1 lid2 "dumpConsIncl1" sig1
           inSens <- coerceThSens lid1 lid2 "dumpConsIncl2" sens1
           let pSig2 = plainSign sig2
               diffSig = propagateErrors "dumpConsIncl3"
                  $ signatureDiff lid2 pSig2 (plainSign insig)
               inSensSet = Set.fromList $ OMap.elems inSens
               sens = OMap.filter (`Set.notMember` inSensSet) sens2
           writeVerbFile opts file
             $ show $ useGlobalAnnos ga $ vcat
             [ text $ "spec source_" ++ nm ++ " ="
             , pretty g1
             , text "end\n"
             , text $ "spec target_" ++ nm ++ " = source_" ++ nm
             , text "then %cons"
             , pretty
               $ G_theory lid2 syn (mkExtSign diffSig) startSigId sens startThId
             ]
