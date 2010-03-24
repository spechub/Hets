{- |
Module      :  $Header$
Description :  Basic analysis for common logic
Copyright   :  (c) Karl Luc, Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for common logic
-}

module CommonLogic.Analysis
    (
     basicCommonLogicAnalysis
    )
    where

import Common.ExtSign
import Common.Result
import CommonLogic.Sign as Sign
import CommonLogic.Symbol
import qualified CommonLogic.AS_CommonLogic as CL
import qualified Common.AS_Annotation as AS_Anno

basicCommonLogicAnalysis :: ([CL.SENTENCE], Sign.Sign, a)
  -> Result ([CL.SENTENCE], 
             ExtSign Sign.Sign Symbol, 
             [AS_Anno.Named (CL.SENTENCE)])
basicCommonLogicAnalysis (_, _, _) = Result [] $ if False then Nothing else 
                                                       Nothing