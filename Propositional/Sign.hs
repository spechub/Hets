{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Definition of signatures for propositional logic
-}
{-
  Ref.

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
  2005.
-}

module Propositional.Sign 
    (
     Sign (..)                     -- Propositional Signatures
    ,pretty                        -- pretty printing
    ,isLegalSignature              -- is a signature ok?
    ,addToSig                      -- adds an id to the given Signature
    ) where

import qualified Data.Set as Set
import qualified Common.Id as Id
import Common.Doc
import Common.DocUtils

-- | Datatype for propositional Signatures
-- Signatures are just sets
data Sign = Sign {items :: Set.Set Id.Id}
          deriving (Eq, Show)

instance Pretty Sign where
    pretty = printSign

-- | determines whether a signature is vaild
-- all sets are ok, so glued to true
isLegalSignature :: Sign -> Bool
isLegalSignature _ = True

printSign :: Sign -> Doc
printSign s = specBraces $ (sepByCommas $ map pretty (Set.toList $ items s))

-- | Adds an Id to the signature
addToSig :: Sign -> Id.Id -> Sign 
addToSig sig tok = Sign {items = Set.insert tok $ items sig}
