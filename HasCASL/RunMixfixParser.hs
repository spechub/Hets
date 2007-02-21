{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

make mixfix analysis checkable by RunParsers
-}

module HasCASL.RunMixfixParser where

import Common.AnnoState
import Common.Earley
import Common.Prec
import Common.GlobalAnnotations
import Common.Id
import Common.Anno_Parser
import Common.Result
import Common.Lexer
import Common.Lib.State
import Common.Doc
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Map

import HasCASL.MixAna
import HasCASL.As
import HasCASL.PrintAs
import HasCASL.ParseTerm
import HasCASL.Le
import HasCASL.AsToLe

-- start testing
stdOpsL, stdPredsL :: [String]

stdOpsL = ["__^__", "__*__", "__+__", "[__]","__div__","__mod__", "__rem__",
        "__-__", "+__", "__E__", "__@@__", "[]", "__::__", "__:::__",
        "-__", "__!"] ++
          [ "____p", "q____","____x____", "{____}",
          "repeat__until__", "while__do__od",
            "__none__but__", "__one__done",
           "__ --> __", "__{__}--__-->{__}__"]
         ++ map (:[]) "#0123456789abcdefghijklmnopqxABCDEFGHIJKLMNO"
         ++ ["A[a[c,d],b]", "B[a[c,d],b]", "__B[a[c,d],b]__",
             "a[c,d]", "__a[c,d]__", "A[a]", "A__B",
             "A__", "__[a]", "__p", "__#", "D__",
             "__[__]__", "[__]__", "__[__]", "if__then__else__"]

stdPredsL = ["__<__", "__<=__", "__>__", "__>=__", "__!=__", "__<>__",
             "__/=__", "even__", "odd__", "__isEmpty",
             "__<=__<=__"]

mkIds :: [String] -> Set.Set Id
mkIds = Set.fromList . map (parseString some_id)

stdOps, stdPreds :: Set.Set Id
stdOps = mkIds stdOpsL
stdPreds = mkIds stdPredsL

resolveTerm :: GlobalAnnos -> AParser () (Result Term)
resolveTerm ga = do
       trm <- term
       let ps = (mkPrecIntMap $ prec_annos ga, stdPreds)
           iEnv = (addPreDefs initialEnv) { preIds = ps, globAnnos = ga }
           ids = Set.union stdPreds $ Set.union stdOps
                 $ Map.keysSet $ assumps iEnv
           (addRule, ruleS, _) = makeRules ga ps ids
           (chart, fEnv) = runState (iterateCharts ga [trm]
                             $ initChart addRule ruleS) iEnv
       return $ do
           Result (filter isErrorDiag $ envDiags fEnv) $ Just ()
           getResolved (shows . toText ga . printTerm . parenTerm)
                    (getRange trm) toMixTerm chart
