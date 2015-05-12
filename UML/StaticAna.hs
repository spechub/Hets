module UML.StaticAna where

import           Common.AS_Annotation
import           Common.ExtSign
import           Common.GlobalAnnotations
import           Common.Result
import           UML.Sign
import           UML.UML
import           UML.UML2CL

basicAna :: (CM, Sign, GlobalAnnos) -> Result (CM, ExtSign Sign (), [Named MultForm])
basicAna (cm, _, _) =  return (cm, mkExtSign (retrieveSign cm), map (makeNamed "") $ retrieveSen cm)
