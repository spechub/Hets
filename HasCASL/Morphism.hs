{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (via imports)
    
Morphism on 'Env' (as for CASL)
-}

module HasCASL.Morphism where

import HasCASL.Le
import HasCASL.Merge
import Common.Result
import Data.Dynamic

data Morphism = Morphism {msource,mtarget :: Env}
                         deriving (Eq, Show)

morphismTc :: TyCon
morphismTc       = mkTyCon "HasCASL.Morphism.Morphism"
instance Typeable Morphism where
  typeOf _ = mkAppTy morphismTc []

mkMorphism :: Env -> Env -> Morphism
mkMorphism e1 e2 = Morphism e1 e2

ideMor :: Env -> Morphism
ideMor e = mkMorphism e e  -- plus identity functions
compMor :: Morphism -> Morphism -> Morphism
compMor m1 m2 = Morphism (msource m1) (mtarget m2) -- plus composed functions

legalEnv :: Env -> Bool
legalEnv _ = True -- maybe a closure test?
legalMor :: Morphism -> Bool
legalMor m = legalEnv (msource m) && legalEnv (mtarget m)  -- and what else?

morphismUnion :: Morphism -> Morphism -> Result Morphism
morphismUnion m1 m2 = do s <- merge (msource m1) $ msource m2
			 t <- merge (mtarget m1) $ mtarget m2
			 return $ mkMorphism s t



