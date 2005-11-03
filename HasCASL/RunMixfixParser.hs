{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

make mixfix analysis checkable by RunParsers
-}

module HasCASL.RunMixfixParser where

import Common.AnnoState
import Common.Earley
import HasCASL.Builtin
import HasCASL.MixAna
import HasCASL.As
import HasCASL.PrintAs
import HasCASL.ParseTerm
import HasCASL.Le
import Common.GlobalAnnotations
import Common.Id
import Common.Anno_Parser
import Common.Result
import Common.Lexer
import Common.Lib.State
import qualified Common.Lib.Set as Set

-- start testing
stdOpsL, stdPredsL :: [String]

stdOpsL = ["__^__", "__*__", "__+__", "[__]","__div__","__mod__", "__rem__", 
        "__-__", "+__", "__E__", "__@@__", "[]", "__::__", "__:::__",
        "-__", "__!"] ++ 
          [ "____p", "q____","____x____", "{____}",
          "repeat__until__", "while__do__od", 
            "__none__but__", "__one__done",
           "__ --> __", "__{__}--__-->{__}__", 
           "Pl7","folge_dem_Gang","nicht_wenden","Pl3","RS3", "RS6"] ++
        map (:[]) 
        "#0123456789abcdefghijklmnoABCDEFGHIJKLMNO"
         ++ ["A[a[c,d],b]", "B[a[c,d],b]", "__B[a[c,d],b]__", 
             "a[c,d]", "__a[c,d]__", "A[a]", "A__B", 
             "A__", "__[a]", "__p", "__#", "D__",
             "__[__]__", "[__]__", "__[__]", 
             "not__", "def__", "__if__", 
             "__=__", "__=>__", "__/\\__", "__\\/__", "__<=>__",
             "__when__else__", "if__then__else__"] 

stdPredsL = ["__<__", "__<=__", "__>__", "__>=__", "__!=__", "__<>__",
             "__/=__", "even__", "odd__", "__isEmpty",
             "__<=__<=__"] ++ map (:[]) "pqrstuvwxyzPQRSTUVWXYZ" 

mkIds :: [String] -> Set.Set Id
mkIds = Set.fromList . map (parseString some_id)

stdOps, stdPreds :: Set.Set Id
stdOps = mkIds stdOpsL
stdPreds = mkIds stdPredsL 

resolveTerm :: GlobalAnnos -> AParser () (Result Term)
resolveTerm ga = do 
       trm <- term  
       let ids = stdOps `Set.union` stdPreds
           newGa = addBuiltins ga 
           prec@(_, _, m) = mkPrecIntMap $ prec_annos newGa
           chart = evalState (iterateCharts newGa [trm] $ 
                              initChart (const []) 
                                        (partitionRules $ 
                                         listRules (m+2) newGa ++
                                         initRules (prec, stdPreds) 
                                         builtinIds (Set.toList ids))
                              Set.empty) 
                   initialEnv { preIds = (prec, stdPreds) }
       return $ getResolved (shows . printTerm emptyGlobalAnnos . parenTerm)
                  (getRange trm) toMixTerm chart

