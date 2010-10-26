module HolLight.Sign where

import qualified Data.Map as Map

data HolType = TyVar String | TyApp String [HolType]

data HolKind = TyAbstractApp [HolKind] | Kind


data Sign = Sign {
               types :: [HolType],
               ops :: Map.Map String HolType } 
