
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

This module provides the access to Achim Mahnke's taxonomy
visualisation for subsort hierarchies.

-}

module GUI.Taxonomy where


import Logic.Logic
import Logic.Grothendieck
import Static.DevGraph

import Taxonomy.MMiSSOntology
import Taxonomy.MMiSSOntologyGraph

import Common.Taxonomy
import Common.Result as Res

import Driver.Options

displayConceptGraph :: String -> G_theory -> IO ()
displayConceptGraph  = displayGraph KConcept
    -- putStrLn "display of Concept Graph not yet implemented"

displaySubsortGraph :: String -> G_theory -> IO ()
displaySubsortGraph = displayGraph KSubsort

displayGraph :: TaxoGraphKind -> String -> G_theory -> IO ()
displayGraph kind thyName (G_theory lid sign sens) = 
    case theory_to_taxonomy lid kind 
                       (emptyMMiSSOntology thyName AutoInsert) 
                       sign $ toNamedList sens of
     Res.Result [] (Just taxo) -> displayClassGraph taxo Nothing
     Res.Result dias _ -> showDiags defaultHetcatsOpts dias
