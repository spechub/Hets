{- |
Module      :  $Header$
Description :  This module is for selecting the favoured EP representation
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module re-exports one of the following modules

GeneralExtendedParameter
SimpleExtendedParameter
 -}

module CSL.ExtendedParameter ( module EP ) where

-- import CSL.GeneralExtendedParameter
import CSL.SimpleExtendedParameter as EP
