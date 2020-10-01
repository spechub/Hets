{- |
Description :  Visualisation of taxonomies
Copyright   :  (c) Otto-von-Guericke University of Magdeburg
License     :  GPLv2 or higher, see LICENSE.txt

This folder provides visualisation of taxonomies in the same style as the
MMiSSOntology tool written by Achim Mahnke. In fact his modules where only
slightly changed. The visualisation is done through uDraw(Graph)
<http://www.informatik.uni-bremen.de/uDrawGraph/en/index.html>
 and its Haskell encapsulation as provided by the UniForM Workbench
<http://www.informatik.uni-bremen.de/uniform/wb> (see
module "GraphDisp" and "GUI.AbstractGraphView").

Module "Taxonomy.OntoParser" provides some parsing function for
MMiSSOntology LaTeX files (maybe outdated).

Module "Taxonomy.MMiSSOntologyGraph" provides the display function and
uDraw(Graph) construction functions.

Module "Taxonomy.MMiSSOntology" provides storage classes for MMiSSOntology
graphs and some build and access functions.

Module Taxonomy\/taxonomyTool.hs provides a test program
for the parser provided by "Taxonomy.OntoParser" (maybe outdated).

-}

module Taxonomy where
