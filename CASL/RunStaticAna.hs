module CASL.RunStaticAna where

import CASL.StaticAna
import Common.AnnoState
import Common.GlobalAnnotations
import Common.Result
import Common.Lib.State
import CASL.Parse_AS_Basic
import CASL.AS_Basic_CASL

localAnalysis :: GlobalAnnos -> BASIC_SPEC -> Result BASIC_SPEC
localAnalysis ga bs = 
    let (newbs, sig) = runState (ana_BASIC_SPEC ga bs) emptyEnv
	in Result (envDiags sig) $ Just newbs

runAna :: GlobalAnnos -> AParser (Result BASIC_SPEC)
runAna ga = 
    do b <- basicSpec
       return $ localAnalysis ga b
