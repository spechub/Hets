module HolLight.Sign where

import qualified Data.Map as Map
import Common.DocUtils
import Common.Doc

data HolType = TyVar String | TyApp String [HolType]
  deriving  (Eq, Ord, Show, Read)

data HolKind = TyAbstractApp [HolKind] | Kind


data Sign = Sign {
               types :: [HolType],
               ops :: Map.Map String HolType }
  deriving (Eq, Ord, Show)

instance Pretty Sign where
  pretty _ = empty -- TO DO!

emptySig :: Sign
emptySig = Sign{types =[], ops = Map.empty}

isSubSig :: Sign -> Sign -> Bool
isSubSig _s1 _s2 = True -- for now!
