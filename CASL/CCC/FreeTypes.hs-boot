module CASL.CCC.FreeTypes where

import CASL.Sign                -- Sign, OpType
import CASL.Morphism              
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import CASL.CCC.SignFuns
import CASL.CCC.TermFormula
import CASL.CCC.TerminationProof
import Common.AS_Annotation
import Common.PrettyPrint
import Common.Result
import Common.Id
import Maybe
import Debug.Trace
import System.Cmd
import System.IO.Unsafe
import Logic.Comorphism
import Logic.Logic
import Comorphisms.HasCASL2Haskell 

checkFreeType ::  (Sign () (),[Named (FORMULA ())]) -> Morphism () () () 
                 -> [Named (FORMULA ())] -> Result (Maybe (Bool,[FORMULA ()]))