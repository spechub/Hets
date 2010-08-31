{- |
Module      :  $Id$
Description :  graphical user interface modules
Copyright   :  (c) Uni Bremen 2005-2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  raider@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (uses uni and development graphs)

Graphical user interface for Hets. The GUI is based on the
UniForM Workbench <http://www.informatik.uni-bremen.de/uniform/wb>.
The UniForm Workbench provides an event system and encapsulations of
TclTk <http://www.informatik.uni-bremen.de/htk/> and uDraw(Graph)
<http://www.informatik.uni-bremen.de/uDrawGraph/en/index.html> (see
module "GraphDisp").

"GUI.AbstractGraphView" is a graph interface, based on the Workbench
encapsulation of uDraw(Graph). Provides additional functions
for hiding and redisplaying (groups of) nodes and edges. (Obsolete, use
GraphAbstraction instead)

"GUI.ConsoleUtils" are similar utilities for using without "HTk" (only
console).

"GUI.GenericATP" is a generic graphical interface for automatic
theorem provers. Decides between Gtk and HTk implementation.

"GUI.GraphAbstraction" provides an interface to uDrawGraph.

"GUI.GraphDisplay" provides functions to display a DevGraph in a new window.

"GUI.GraphLogic" provides the functionality for the menus created with
"GUI.GraphMenu"

"GUI.GraphMenu" creates the File and the Edit menu of uDrawGraph, as well as the
local node and edge menus and types.

"GUI.GraphTypes" defines the types used in "GUI.GraphDisplay", "GUI.GraphLogic"
and "GUI.GraphMenu".

"GUI.GtkConsistencyChecker" gui for checking consistency.

"GUI.GtkGenericATP" gtk version of generic prove gui.

"GUI.GtkLinkTypeChoice" small window letting the user select the link types that
should be displayed or hidden.

"GUI.GtkProverGUI" prover gui implementation in gtk.

"GUI.GtkUtils" a bunch of utility functions for use in and outside of gtk.

"GUI.HTkGenericATP" htk version of generic prove gui.

"GUI.HTkProofDetails" sets an additional window used by "GUI.ProverGUI" for
displaying and saving proof details (prover output, tactic script, proof tree).

"GUI.HTkProverGUI" is a goal management GUI for the structured level.

"GUI.HTkUtils" provides some utilities on top of "HTk".

"GUI.ProverGUI" is a goal management GUI for the structured level. Decides
between Gtk and HTk implementation.

"GUI.ShowGraph" displays the final graph.

"GUI.ShowLibGraph" displays the library graph.

"GUI.ShowLogicGraph" displays the logic graph.

"GUI.Taxonomy" displays a subsort relation (taxonomy).

"GUI.Utils" are either "GUI.HTkUtils", "GUI.GtkUtils" or "GUI.ConsoleUtils".

"GUI.UDGUtils" just imports and exports uDrawGraph modules.
-}

module GUI where
