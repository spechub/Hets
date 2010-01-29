{- |
Module      :  $Header$
Description :  Pathify all names
Copyright   :  (c) Ewaryst Schulz, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

Pathify all signature names
-}

module CASL.Pathify
  ( pathifyNames
  ) where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Monoton

import Common.AS_Annotation
import Common.Id
import Common.LibName
import Common.Result

import Control.Monad
import qualified Data.Map as Map
import qualified Data.Set as Set

pathifyNames :: LibId -> Sign f e -> [(Int, Morphism f e m)]
                 -> Result (Map.Map Symbol [LinkPath Symbol])
pathifyNames libid sig l = return $ Map.empty
