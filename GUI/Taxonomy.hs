
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

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
import GUI.Utils

import Common.Taxonomy
import Common.Result as Res
import Common.ExtSign

displayConceptGraph :: String -> G_theory -> IO ()
displayConceptGraph = displayGraph KConcept

displaySubsortGraph :: String -> G_theory -> IO ()
displaySubsortGraph = displayGraph KSubsort

displayGraph :: TaxoGraphKind -> String -> G_theory -> IO ()
displayGraph kind thyName (G_theory lid (ExtSign sign _) _ sens _) =
    case theory_to_taxonomy lid kind
                       (emptyMMiSSOntology thyName AutoInsert)
                       sign $ toNamedList sens of
     Res.Result [] (Just taxo) -> do
       displayClassGraph taxo Nothing
       return ()
     Res.Result dias _ -> errorDialog "Error" $ showRelDiags 2 dias
