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
import Data.Dynamic
import Common.DynamicUtils
import Common.PrettyPrint
import Common.PrintLaTeX

data CSPAddSign = CSPAddSign { channelNames :: Map.Map Id SORT
                             , processNames :: Map.Map Id (Maybe SORT)}
                  deriving (Eq, Show)

type CSPSign = Sign () CSPAddSign

emptyCSPAddSign :: CSPAddSign
emptyCSPAddSign = CSPAddSign { channelNames = Map.empty
                       , processNames = Map.empty
                       }

diffCSPAddSign :: CSPAddSign -> CSPAddSign -> CSPAddSign
diffCSPAddSign a b = 
    a { channelNames = channelNames a `Map.difference` channelNames b,
        processNames = processNames a `Map.difference` processNames b
      }

emptyCSPSign :: CSPSign
emptyCSPSign = emptySign emptyCSPAddSign

data CSPAddMorphism = 
     CSPAddMorphism { channelMap :: Map.Map Id Id
                    , processMap :: Map.Map Id Id
                    }
     deriving (Eq, Show)


type CSPMorphism = Morphism () CSPAddSign CSPAddMorphism


signTc      = mkTyCon "CspCASL.SignCSP.CSPAddSign"
instance Typeable CSPAddSign where
  typeOf _ = mkTyConApp signTc []

morTc      = mkTyCon "CspCASL.SignCSP.CSPAddMorphism"
instance Typeable CSPAddMorphism where
  typeOf _ = mkTyConApp morTc []

-- dummy instances, need to be elaborated!
instance PrettyPrint CSPAddSign where
instance PrettyPrint CSPAddMorphism where
instance PrintLaTeX CSPAddSign where
instance PrintLaTeX CSPAddMorphism where