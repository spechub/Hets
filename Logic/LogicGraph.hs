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


   Logic-Representations (Sublogic always = top)

-}

module Logic.LogicGraph
where

import Logic.Logic 
import Logic.Grothendieck
import CASL.Logic_CASL  -- also serves as default logic
import HasCASL.Logic_HasCASL
import Haskell.Logic_Haskell
import CspCASL.Logic_CspCASL
import Comorphisms.CASL2HasCASL
import qualified Common.Lib.Map as Map
import CASL.ATC_CASL

logicList :: ([AnyLogic],[AnyComorphism])
logicList = ([Logic CASL, Logic HasCASL, Logic Haskell, Logic CspCASL],
             [Comorphism CASL2HasCASL])

logicGraph :: LogicGraph
logicGraph = (Map.fromList logicTuple, Map.fromList representationTuple)
    where logicTuple = 
	      map (\(Logic lid) -> (language_name lid, 
				    Logic lid)) 
		      (fst logicList)
	  representationTuple = 
	      map (\rep -> ("",rep)) (snd logicList)

defaultLogic :: AnyLogic
defaultLogic = Logic CASL

lookupLogic_in_LG :: String -> String -> AnyLogic
lookupLogic_in_LG errorPrefix logname =
    lookupLogic errorPrefix (logname) logicGraph

lookupComorphism_in_LG :: String -> String -> AnyComorphism
lookupComorphism_in_LG error_prefix coname =
    lookupComorphism error_prefix coname logicGraph




