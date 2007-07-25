{- |
Module      :  $Header$
Description :  Some utilities for SPASS and TPTP.
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Some utilities for SPASS and TPTP

-}

module SoftFOL.Utils where

import qualified CASL.Sign as CSign
import CASL.AS_Basic_CASL (SORT)


-- | A data type for storing the type of a CASL Id; needed for SPASS and TPTP
data CType = CSort
           | CVar SORT
           | CPred CSign.PredType
           | COp   CSign.OpType
             deriving (Eq,Ord,Show)
