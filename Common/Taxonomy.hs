
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable 

This module only provides a small type for selecting different kinds
of taxonomy graphs.

-}


module Common.Taxonomy where


import Common.Result

data TaxoGraphKind = KSubsort | KConcept 
     deriving (Show,Enum,Eq)

withErrorToResult :: Either String a -> Result a
withErrorToResult = 
    either (\err -> fail err) (\x -> return x) 