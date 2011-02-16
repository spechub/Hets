{- |
Module      :  $Header$
Description :  static basic analysis for FPL
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable
-}

module Fpl.StatAna where

import Fpl.As
import Fpl.Sign

import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Quantification

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Keywords
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Lib.State
import Common.Id
import Common.Result
import Common.ExtSign
import Data.List as List

type FplSign = Sign TermExt SignExt

basicFplAnalysis
  :: (FplBasicSpec, FplSign, GlobalAnnos)
  -> Result (FplBasicSpec, ExtSign FplSign Symbol, [Named FplForm])
basicFplAnalysis =
    basicAnalysis minFplTerm anaFplExt (const return) mixFplAna

mixFplAna :: Mix () FplExt TermExt SignExt
mixFplAna = emptyMix
    { getSigIds = fplIds
    , putParen = mapTermExt
    , mixResolve = resolveTermExt
    }

fplIds = undefined

instance FreeVars TermExt where
  freeVarsOfExt s _ = Set.empty

minFplTerm :: Min TermExt SignExt
minFplTerm s form = undefined

mapTermExt = undefined
resolveTermExt = undefined
anaFplExt = undefined
