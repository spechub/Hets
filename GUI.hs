{- |
Module      :  $Id$
Description :  graphical user interface modules
Copyright   :  (c) Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
for hiding and redisplaying (groups of) nodes and edges.

"GUI.ConsistencyChecker" provides generic GUI for consistency checker. Based
upon "GUI.GenericATP" GUI.

"GUI.ConsoleUtils" are similar utilities for using without "HTk" (only
console).

"GUI.DGTranslations" provides funtions to display the logic graph.

"GUI.GenericATP" is a generic graphical interface for automatic
theorem provers.

"GUI.GenericATPState" provides data structures and initialising functions for
prover state and configurations.

"GUI.GraphAbstraction" provides an interface to the uDrawGraph

"GUI.GraphDisplay" provides functions to display a DevGraph in a new window.

"GUI.GraphLogic" provides the functionality for the menus created with
"GUI.GraphMenu"

"GUI.GraphMenu" creates all the menu functions for the File and the Edit menu of the uDrawGraph window.

"GUI.GraphTypes" defines the types used in "GUI.GraphDisplay", "GUI.GraphLogic"
and "GUI.GraphMenu".

"GUI.History" provides a history of commands in proof-script format.

"GUI.HTkUtils" provides some utilities on top of "HTk".

"GUI.PrintUtils" are pretty printing functions used by "GUI.GenericATP".

"GUI.ProofDetails" sets an additional window used by "GUI.ProofManagement" for
displaying and saving proof details (prover output, tactic script, proof tree).

"GUI.ProofManagement" is a goal management GUI for the structured level.

"GUI.ShowGraph" displays the final graph.

"GUI.ShowLibGraph" displays the library graph.

"GUI.ShowLogicGraph" displays the logic graph.

"GUI.Taxonomy" displays a subsort relation (taxonomy).

"GUI.Utils" are either "GUI.HTkUtils" or "GUI.ConsoleUtils".
-}

module GUI where
