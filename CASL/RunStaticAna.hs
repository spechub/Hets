module CASL.RunStaticAna where

import CASL.Static
import Common.AnnoState
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import CASL.Parse_AS_Basic
import CASL.PrintSign

instance PrettyPrint LocalEnv where
    printText0 ga l = (printText0 ga $ getSign l)
		     $$ (text $ show $ getPsi l)

runAna :: AParser (Result LocalEnv)
runAna = 
    do b <- basicSpec
       return $ ana_BASIC_SPEC emptyLocalEnv b
