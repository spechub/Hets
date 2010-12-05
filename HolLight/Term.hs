{- |
Module      :  $Header$
Description :  Tern for HolLight logic
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

Definition of terms for HolLight logic

  Ref.

  <http://www.cl.cam.ac.uk/~jrh13/hol-light/>

-}

module HolLight.Term where

data HolType = TyVar String | TyApp String [HolType]
  deriving  (Eq, Ord, Show, Read)

data HolProof = NoProof deriving (Eq, Ord, Show)

data HolParseType = Normal | Prefix | InfixL Int | InfixR Int | Binder deriving (Eq, Ord, Show, Read)

data Term = Var String HolType HolParseType
     | Const String HolType HolParseType
     | Comb Term Term
     | Abs Term Term deriving (Eq, Ord, Show, Read)
