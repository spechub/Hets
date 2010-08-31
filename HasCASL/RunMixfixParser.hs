{- |
Module      :  $Header$
Description :  test driver for mixfix resolution
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
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
import Common.Result
import Common.Lib.State
import Common.Doc
import Common.ExampleMixIds
import qualified Data.Set as Set
import qualified Data.Map as Map

import HasCASL.MixAna
import HasCASL.As
import HasCASL.Builtin
import HasCASL.PrintAs
import HasCASL.ParseTerm
import HasCASL.Le

stdOps :: Set.Set Id
stdOps = mkIds $ stdOpsL ++ ["__#", "D__", "if__then__else__"]
  ++ map (:[]) "#0123456789abcdefghijklmnopqxABCDEFGHIJKLMNO"

resolveTerm :: GlobalAnnos -> AParser () (Result Term)
resolveTerm ga = do
       trm <- term
       let ps = (mkPrecIntMap $ prec_annos ga, stdPreds)
           iEnv = preEnv { preIds = ps, globAnnos = ga }
           ids = Set.union stdPreds $ Set.union stdOps
                 $ Map.keysSet $ assumps iEnv
           (addRule, ruleS, sIds) = makeRules ga ps (getPolyIds $ assumps iEnv)
                                 ids
           (chart, fEnv) = runState (iterateCharts ga sIds
                                     (getCompoundLists iEnv) [trm]
                                    $ initChart addRule ruleS) iEnv
       return $ do
           Result (filter isErrorDiag $ envDiags fEnv) $ Just ()
           getResolved (shows . toText ga . printTerm . parenTerm)
                    (getRange trm) (toMixTerm iEnv) chart
