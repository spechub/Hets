{- |
Module      :  $Header$
Description :  static analysis for Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis for Relational Schemes
-}

module RelationalScheme.StaticAnalysis where

import RelationalScheme.AS
import RelationalScheme.Sign
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Result
import Common.AS_Annotation
import Data.Set as Set

basic_Rel_analysis :: (RSScheme, Sign,GlobalAnnos) ->
                      Result (RSScheme, ExtSign Sign (),[Named Sentence])
basic_Rel_analysis (spec, sign, _) =
    return  (spec, ExtSign
                    {
                        plainSign = sign
                    ,   nonImportedSymbols = Set.empty
                    },
                    [])
