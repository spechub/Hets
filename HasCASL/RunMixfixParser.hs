{- |
Module      :  $Header$
Copyright   :  (c) Klaus L�ttich, Christian Maeder and Uni Bremen 2002-2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

make mixfix analysis checkable by RunParsers

-}

module HasCASL.RunMixfixParser where

import Common.AnnoState
import Common.Earley
import HasCASL.MixAna
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.ParseTerm
import HasCASL.Le
import Common.GlobalAnnotations
import Common.Lib.Set
import Common.Id
import Common.Anno_Parser
import Common.Result
import Common.Lexer
import Common.Lib.State
import Common.Lib.Set as Set
import Common.PPUtils
import Common.PrettyPrint

-- start testing
stdOpsL, stdPredsL :: [String]

stdOpsL = ["__^__", "__*__", "__+__", "[__]","__div__","__mod__", "__rem__", 
        "__-__", "+__", "__E__", "__@@__", "[]", "__::__", "__:::__",
	"-__", "__!"] ++ 
          [ "____p", "q____","____x____", "{____}",
          "repeat__until__", "while__do__od", 
	    "__where__but__", "__where__done",
           "__ --> __", "__{__}--__-->{__}__", 
           "Pl7","folge_dem_Gang","nicht_wenden","Pl3","RS3", "RS6"] ++
        map (:[]) 
        "0123456789abcdefghijklmnoABCDEFGHIJKLMNO"
         ++ ["A[a[c,d],b]", "B[a[c,d],b]", "__B[a[c,d],b]__", 
	     "a[c,d]", "__a[c,d]__", "A[a]", "A__B", 
	     "A__", "__[a]", "__p", 
	     "__[__]__", "[__]__", "__[__]"] 

stdPredsL = ["__<__", "__<=__", "__>__", "__>=__", "__!=__", "__<>__",
	     "__/=__", "even__", "odd__", "__isEmpty","not__", "def__",
	     "__=__", "__=>__", "__/\\__", "__\\/__", "__<=>__",
	     "__if__", "__when__else__", "if__then__else__",
	    "__<=__<=__"] ++ map (:[]) "pqrstuvwxyzPQRSTUVWXYZ" 

mkIds :: [String] -> Set Id
mkIds = fromList . map (parseString some_id)

stdOps, stdPreds :: Set Id
stdOps = mkIds stdOpsL
stdPreds = mkIds stdPredsL 

resolveTerm :: GlobalAnnos -> AParser (Result Term)
resolveTerm ga = do 
       trm <- term  
       let ids = stdOps `Set.union` stdPreds
           chart = evalState (iterateCharts (addBuiltins ga 
					     stdOps stdPreds) [trm] $ 
	    initChart (initTermRules stdPreds ids) Set.empty) initialEnv 
       return $ getResolved showPretty (posOfTerm trm) 
			  toMixTerm chart

testTermMix :: GlobalAnnos -> AParser WrapString
testTermMix ga = do Result ds mt <- resolveTerm ga
		    return $ WrapString $ 
			case mt of Just t -> show $ printText0 ga t
				   _ -> show ds

