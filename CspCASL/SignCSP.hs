{- |
Module      :  $Header$
Copyright   :  (c) Markus Roggenbach and Till Mossakowski and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable


  signatures for CSP-CASL

-}

{- todo:
 
-}

module CspCASL.SignCSP where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

data CSPAddSign = CSPAddSign { channelNames :: Map.Map Id SORT
                             , processNames :: Map.Map Id (Maybe SORT)}
                  deriving Show

type CSPSign = Sign () CSPAddSign

emptyCSPAddSign :: CSPAddSign
emptyCSPAddSign = CSPAddSign { channelNames = Map.empty
                       , processNames = Map.empty
                       }

emptyCSPSign :: CSPSign
emptyCSPSign = emptySign emptyCSPAddSign

data CSPAddMorphism = 
     CSPAddMorphism { channelMap :: Map.Map Id Id
                    , processMap :: Map.Map Id Id
                    }
     deriving Show

type CSPMorphism = Morphism () CSPAddSign CSPAddMorphism
