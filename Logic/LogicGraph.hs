{- HetCATS/Logic/LogicGraph.hs
   $Id$
   Till Mossakowski
   
   Assembles all the logics and representations into a graph.
   The modules for the Grothendieck logic are logic graph indepdenent,
   and here is the logic graph that is used to instantiate these.
   Since the logic graph depends on a large number of modules for the
   individual logics, this separation of concern (and possibility for
   separate compilation) is quite useful.

   References:

   T. Mossakowski:
   Relating CASL with Other Specification Languages:
        the Institution Level
   Theoretical Computer Science, July 2003

   Todo:
   Add many many logics.

   Wiebke: Modallogiken

   Logic-Representations (Sublogic immer = top)

-}

module Logic.LogicGraph
where

import Logic.Grothendieck
import CASL.Logic_CASL  -- also serves as default logic
-- import Logic_HasCASL
--import Logic_Haskell

logicGraph :: LogicGraph
logicGraph = ([Logic CASL],[])

defaultLogic :: AnyLogic
defaultLogic = Logic CASL
