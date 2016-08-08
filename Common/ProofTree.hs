{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./Common/ProofTree.hs
Description :  a simple proof tree
Copyright   :  (c) DFKI GmbH, Uni Bremen 2002-2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Datatype for storing of the proof tree
-}

module Common.ProofTree where

import Data.Data

{- |
  Datatype for storing of the proof tree. The Show class is instantiated.
-}
data ProofTree = ProofTree String deriving (Eq, Ord, Typeable, Data)

instance Show ProofTree where
  show (ProofTree st) = st

emptyProofTree :: ProofTree
emptyProofTree = ProofTree ""
