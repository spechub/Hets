module TheLogicGraph
where

import LogicGraph
import Logic_CASL  -- also serves as default logic
import Logic_HasCASL

logicGraph :: LogicGraph
logicGraph = ([Logic CASL, Logic HasCASL],[])

defaultLogic :: AnyLogic
defaultLogic = Logic CASL