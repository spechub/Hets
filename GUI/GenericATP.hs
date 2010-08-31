{-# LANGUAGE CPP #-}
{- |
Module      :  $Header$
Description :  Generic Prover GUI.
Copyright   :  (c) Thiemo Wiedemeyer, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Generic GUI for automatic theorem provers. CPP between HTk and Gtk.
-}

module GUI.GenericATP (genericATPgui) where

import Interfaces.GenericATPState

import Logic.Prover

#ifdef GTKGLADE
import qualified GUI.GtkGenericATP as Gtk
#elif defined UNI_PACKAGE
import qualified GUI.HTkGenericATP as HTk
#endif

{- |
  Invokes the prover GUI. Users may start the batch prover run on all goals,
  or use a detailed GUI for proving each goal manually.
-}
genericATPgui :: (Ord proof_tree, Ord sentence)
              => ATPFunctions sign sentence mor proof_tree pst
              -- ^ prover specific -- functions
              -> Bool -- ^ prover supports extra options
              -> String -- ^ prover name
              -> String -- ^ theory name
              -> Theory sign sentence proof_tree -- ^ theory consisting of a
                 -- signature and a list of Named sentence
              -> [FreeDefMorphism sentence mor] -- ^ freeness constraints
              -> proof_tree -- ^ initial empty proof_tree
              -> IO([ProofStatus proof_tree]) -- ^ proof status for each goal
#ifdef GTKGLADE
genericATPgui = Gtk.genericATPgui
#elif defined UNI_PACKAGE
genericATPgui = HTk.genericATPgui
#else
genericATPgui = error "not implemented"
#endif
