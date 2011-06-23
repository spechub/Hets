{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Static analysis for THF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Instance of class Logic for THF.
-}

module THF.StaticAnalysisTHF where

import THF.Cons

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.ExtSign


basicAnalysis :: (BasicSpecTHF, SignTHF, GlobalAnnos) ->
        Result (BasicSpecTHF, ExtSign SignTHF SymbolTHF, [Named SentenceTHF])
basicAnalysis = undefined
