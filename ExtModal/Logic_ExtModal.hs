{- |
Module      :  ./ExtModal/Logic_ExtModal.hs
Description :  Instance of class Logic for ExtModal
Copyright   :  
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  
Stability   :  experimental
Portability :  

Instance of class Logic for ExtModal
-}

module ExtModal.Logic_ExtModal where

import ExtModal.AS_ExtModal
import ExtModal.ExtModalSign
import ExtModal.ATC_ExtModal()
import ExtModal.Parse_AS
import ExtModal.StatAna

import CASL.Sign
import CASL.Morphism
import CASL.SymbolMapAnalysis
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Parse_AS_Basic
import CASL.MapSentence
import CASL.SymbolParser
import CASL.Sublogic
import CASL.Logic_CASL ()
import Logic.Logic


