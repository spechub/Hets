{- |
Module      :  $Header$
Description :  Generation of Verification Conditions
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module provides functionality for the generation of verification conditions
during program evaluation.
-}

module CSL.Verification where

import qualified Data.Map as Map
import CSL.Interpreter
import CSL.AS_BASIC_CSL

-- ----------------------------------------------------------------------
-- * Verification Conditions
-- ----------------------------------------------------------------------

{- | Given an instantiated constant this data structure keeps 

* the value of this constant looked up in the assignment store

* for function constants its definition (looked up in the assignment store)

* the for this constant generated verification condition

-}
data VCData = VCData
    { vcValue :: EXPRESSION
    , vcDef :: Maybe AssDefinition
    , vcCondition :: EXPRESSION
    }

type VCMap = Map.Map InstantiatedConstant VCData

-- | Extra functionality of 'AssignmentStore's for VC generation
class AssignmentStore m => VCGenerator m where
    resetVCs :: m ()
    getVCMap :: m VCMap 

dependentVCs :: (VCGenerator m) =>
             ConstantName -> AssDefinition -> m VCMap
dependentVCs _ ad = do
  resetVCs
  generateVCs $ getDefiniens ad
  getVCMap

generateVCs :: (VCGenerator m) => EXPRESSION -> m ()
generateVCs exp = return ()

