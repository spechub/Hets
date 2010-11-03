{- |
Module      :  $Header$
Description :  Some basic types for Extended Parameters
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

This module defines some basic types for Extended Parameters
 -}

module CSL.EPBasic where

-- ----------------------------------------------------------------------
-- * General Datatypes for Extended Parameters
-- ----------------------------------------------------------------------

data BoolRep = Not BoolRep | Impl BoolRep BoolRep | And [BoolRep]
             | Or [BoolRep] | Fun String [String]

