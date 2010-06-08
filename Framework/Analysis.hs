{- |
Module      :  $Header$
Description :  Analyzes a logic definition 
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Analysis ( basicAnalysis ) where

import Framework.AS

import qualified Data.Set as Set

import Common.ExtSign
import Common.GlobalAnnotations
import Common.Result
import qualified Common.AS_Annotation as Anno

-- analyzes a logic definition
basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos) -> 
  Result (BASIC_SPEC, ExtSign Sign (), [Anno.Named ()])
basicAnalysis (bs,_,_) = Result [] $ Just (bs, ExtSign bs Set.empty, [])
