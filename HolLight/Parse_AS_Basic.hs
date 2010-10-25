{- |
Module      :  $Header$
Description :  Parser for basic specs
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <jonathan.von_schroeder@dfki.de>
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for propositional logic

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
-}

module HolLight.Parse_AS_Basic
  ( basicSpec                      -- Parser for basic specs
  ) where

import qualified Common.AnnoState as AnnoState

data BasicSpec = BasicSpec

basicSpec :: AnnoState.AParser st AS_BASIC.BASICSPEC
basicSpec = error "not implemented"

