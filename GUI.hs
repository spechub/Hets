{- | Graphical user interface for Hets. The GUI is based on the
UniForM Workbench <http://www.informatik.uni-bremen.de/uniform/wb>.
The UniForm Workbench provides an event system and encapsulations of
TclTk <http://www.informatik.uni-bremen.de/htk/> and uDraw(Graph)
<http://www.informatik.uni-bremen.de/uDrawGraph/en/index.html> (see
module "GraphDisp").

"GUI.AbstractGraphView" graph interface, based on the Workbench
encapsulation of uDraw(Graph). Provides additional functions
for hiding and redisplaying (groups of) nodes and edges.

"GUI.ConvertDevToAbstractGraph"
display of development graphs, using abstract graph interface

"GUI.HTkUtils"  some utilities for "HTk"

"GUI.ConsoleUtils" similar utilities for using without "HTk"

"GUI.Utils" either "GUI.HTkUtils" or "GUI.ConsoleUtils"

"GUI.ShowLogicGraph" display of logic graph

"GUI.Taxonomy" display of subsort relation (taxonomy)

"GUI.WebInterface" driver for web interface, 
which is accessible through <http://www.informatik.uni-bremen.de/cgi-bin/cgiwrap/luettich/hets.cgi>

-}

module GUI where
