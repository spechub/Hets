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
import Logic.Logic (language_name)
import CASL.Logic_CASL  -- also serves as default logic
import HasCASL.Logic_HasCASL
import Haskell.Logic_Haskell
import qualified Common.Lib.Map as Map

logicList :: ([AnyLogic],[AnyRepresentation])
logicList = ([Logic CASL, Logic HasCASL, Logic Haskell],[])

logicGraph :: LogicGraph
logicGraph = (Map.fromList logicTupel, Map.fromList representationTupel)
    where logicTupel = 
	      map (\(Logic lid) -> (language_name lid, 
				    Logic lid)) 
		      (fst logicList)
	  representationTupel = 
	      map (\rep -> ("",rep)) (snd logicList)

defaultLogic :: AnyLogic
defaultLogic = Logic CASL

lookupLogic_in_LG :: String -> String -> AnyLogic
lookupLogic_in_LG errorPrefix logname =
    lookupLogic errorPrefix (logname) logicGraph