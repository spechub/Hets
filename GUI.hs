{- | Graphical user interface for Hets. The GUI is based on the
UniForM Workbench <http://www.informatik.uni-bremen.de/uniform/wb>.
The UniForm Workbench provides an event system and encapsulations of
TclTk <http://www.informatik.uni-bremen.de/htk/> and uDraw(Graph)
<http://www.informatik.uni-bremen.de/uDrawGraph/en/index.html> (see
module "GraphDisp").

"GUI.AbstractGraphView" is a graph interface, based on the Workbench
encapsulation of uDraw(Graph). Provides additional functions
for hiding and redisplaying (groups of) nodes and edges.

"GUI.ConvertDevToAbstractGraph"
displays development graphs, using abstract graph interface.

"GUI.GenericATP" is a generic graphical interface for automatic theorem provers.

"GUI.GenericATPState" provides data structures and initialising functions for
prover state and configurations.

"GUI.ProofManagement" is a goal management GUI for the structured level.

"GUI.ProofDetails" sets an additional window used by "GUI.ProofManagement" for
displaying and saving proof details (prover output, tactic script, proof tree).

"GUI.HTkUtils" provides some utilities on top of "HTk".

"GUI.ConsoleUtils" are similar utilities for using without "HTk" (only console).

"GUI.PrintUtils" are pretty printing functions used by "GUI.GenericATP".

"GUI.Utils" are either "GUI.HTkUtils" or "GUI.ConsoleUtils".

"GUI.ShowGraph" displays the final graph.

"GUI.ShowLogicGraph" displays the logic graph.

"GUI.DGTranslations" displays the logic graph.

"GUI.Taxonomy" displays a subsort relation (taxonomy).
-}

module GUI where
