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

localAna :: GlobalAnnos -> BASIC_SPEC -> Result Sign
localAna ga bs = 
    let (_, sig) = runState (ana_BASIC_SPEC ga bs) emptyEnv
	ds = filter ((<= Error)  . diagKind) $ envDiags sig
	in Result ds $ Just sig

getSign :: GlobalAnnos -> AParser (Result Sign)
getSign ga = 
    do b <- basicSpec
       return $ localAna ga b
