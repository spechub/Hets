{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

static analysis for ConstraintCASL specifications
 Follows Chaps. III:2 and III:3 of the CASL Reference Manual.
-}

module ConstraintCASL.StaticAna where

import ConstraintCASL.AS_ConstraintCASL
import ConstraintCASL.Print_AS
import CASL.StaticAna
import CASL.Sign
import CASL.Morphism
import CASL.MixfixParser
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Result
import Common.AS_Annotation
import Common.GlobalAnnotations
import Data.Maybe
import Data.List

type ConstraintCASLSign = Sign ConstraintFORMULA () 
type ConstraintCASLMor = Morphism ConstraintFORMULA () ()

basicConstraintCASLAnalysis :: 
        (ConstraintCASLBasicSpec, ConstraintCASLSign, GlobalAnnos)
                  -> Result (ConstraintCASLBasicSpec,
                             ConstraintCASLSign, [Named ConstraintCASLFORMULA])
basicConstraintCASLAnalysis =
    basicAnalysis (const return) (const return) (const return) emptyMix
