{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

make static analysis checkable by RunParsers 

-}

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
    let (newBs, sig) = runState (ana_BASIC_SPEC ga bs) emptyEnv
	in Result (envDiags sig) $ Just newBs

runAna :: GlobalAnnos -> AParser (Result BASIC_SPEC)
runAna ga = 
    do b <- basicSpec
       return $ localAnalysis ga b

localAna :: GlobalAnnos -> BASIC_SPEC -> Result Sign
localAna ga bs = 
    let Result ds (Just (_newBs, difSig, _accSig, _sents)) = 
	    basicAnalysis (bs, emptyEnv, ga)
	es = filter ((<= Error)  . diagKind) ds
	in Result es $ Just difSig

getSign :: GlobalAnnos -> AParser (Result Sign)
getSign ga = 
    do b <- basicSpec
       return $ localAna ga b
