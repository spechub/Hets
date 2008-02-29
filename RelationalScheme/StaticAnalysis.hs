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
import qualified Data.Set as Set

getRels :: RSScheme -> [Annoted RSRel]
getRels spec = case spec of
            RSScheme _ (RSRelationships rels _) _ -> rels
            
getSignature :: RSScheme -> RSTables
getSignature spec = case spec of
            RSScheme tb _ _ -> tb

basic_Rel_analysis :: (RSScheme, Sign,GlobalAnnos) ->
                      Result (RSScheme, ExtSign Sign (),[Named Sentence])
basic_Rel_analysis (spec, sign, _) =
    let
        sens = getRels spec
    in
    do
        os <- (getSignature spec) `uniteSig` sign
        return  (spec, ExtSign
                    {
                        plainSign = os
                    ,   nonImportedSymbols = Set.empty
                    },
                    map makeNamedSen sens)
