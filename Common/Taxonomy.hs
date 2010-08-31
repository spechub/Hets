
{- |
Module      :  $Header$
Description :  type for selecting different kinds of taxonomy graphs
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Type for selecting different kinds of taxonomy graphs

This module only provides a small type for selecting different kinds
of taxonomy graphs.

-}

module Common.Taxonomy where

data TaxoGraphKind = KSubsort | KConcept
     deriving (Show, Enum, Eq)

data OntoObjectType =
    OntoClass | OntoObject | OntoPredicate deriving (Show, Eq)
