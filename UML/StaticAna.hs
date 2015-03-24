module UML.StaticAna where

import UML.UML
import UML.Sign
import UML.UML2CL
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.AS_Annotation

basicAna :: (CM, Sign, GlobalAnnos) -> Result (CM, ExtSign Sign (), [Named MultForm])
basicAna (cm, _, _) =  return (cm, mkExtSign (retrieveSign cm), map (makeNamed "") $ retrieveSen cm)
