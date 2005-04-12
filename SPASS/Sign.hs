{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  unknown

   Data structures representing SPASS signatures.

-}

module SPASS.Sign where

import Common.AS_Annotation

type SPIdentifier = String

type SPFormula = Named SPTerm

data SPOriginType =
        SPOriginAxioms
      | SPOriginConjectures
      deriving (Eq, Show)

data SPTerm = 
        SPQuantTerm { quantSym :: SPQuantSym,
                      termList :: [SPTerm],
                      term     :: SPTerm }
      | SPSimpleTerm SPSymbol
      | SPComplexTerm { symbol    :: SPSymbol,
                        arguments :: [SPTerm]}
      deriving (Eq, Show)

data SPQuantSym =
        SPForall
      | SPExists
      | SPCustomQuantSym SPIdentifier
      deriving (Eq, Show)

data SPSymbol =
        SPEqual
      | SPTrue 
      | SPFalse 
      | SPOr 
      | SPAnd
      | SPNot
      | SPImplies
      | SPImplied
      | SPEquiv
      | SPCustomSymbol SPIdentifier
      deriving (Eq, Show)
