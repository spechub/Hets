
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

This module provides the access to Achim Mahnke's taxonomy
visualisation for subsort hierarchies.

-}

module GUI.Taxonomy where


import Logic.Logic
import Logic.Prover
import Static.GTheory

import Taxonomy.MMiSSOntology
import Taxonomy.MMiSSOntologyGraph
import GUI.AbstractGraphView (OurGraph)

import Common.Taxonomy
import Common.Result as Res
import Common.ExtSign

import Driver.Options

displayConceptGraph :: String -> G_theory -> IO ()
displayConceptGraph s th = do displayGraph KConcept s th
                              return ()
    -- putStrLn "display of Concept Graph not yet implemented"

displaySubsortGraph :: String -> G_theory -> IO ()
displaySubsortGraph s th = do displayGraph KSubsort s th
                              return ()

displayGraph :: TaxoGraphKind -> String -> G_theory -> IO (Maybe OurGraph)
displayGraph kind thyName (G_theory lid (ExtSign sign _) _ sens _) =
    case theory_to_taxonomy lid kind
                       (emptyMMiSSOntology thyName AutoInsert)
                       sign $ toNamedList sens of
     Res.Result [] (Just taxo) -> fmap Just $ displayClassGraph taxo Nothing
     Res.Result dias _ -> do showDiags defaultHetcatsOpts dias
                             return Nothing
