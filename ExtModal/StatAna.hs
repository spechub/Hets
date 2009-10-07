{- |
Module      :  ./ExtModal/StatAna.hs
Copyright   :  
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  
Stability   :  experimental
Portability :  

static analysis of modal logic parts
-}

module ExtModal.StatAna where

import ExtModal.AS_ExtModal
import ExtModal.Print_AS()
import ExtModal.ExtModalSign

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


