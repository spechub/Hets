{- |
Module      :  $Header$
Description :  abstract AD syntax
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CSMOF.As where

import qualified Data.Set as Set

data NamedElement = NamedElement
 { name :: String
 , typeOrTypedElem :: TypeOrTypedElem }
 deriving (Eq, Ord, Show)

data TypeOrTypedElem = Type { getType :: Type }
  | TypedElement
  deriving (Eq, Ord, Show)

data Type = DataType | Class { getClass :: Class }
  deriving (Eq, Ord, Show)

data Class = MkClass { isAbstract :: Bool, superClasses :: Set.Set Class }
  deriving (Eq, Ord, Show)
