{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./RigidCASL/Morphism.hs
Description :  Morphisms in RigidCASL
Copyright   :  (c) R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.cm
Stability   :  experimental
Portability :  portable

  Definition of morphisms for RigidCASL
  
-}

module RigidCASL.Morphism where

import qualified CASL.Morphism as CMor
import RigidCASL.Sign

type RigidMor = CMor.Morphism () RigidExt (CMor.DefMorExt RigidExt)

caslMor :: RigidMor -> CMor.CASLMor
caslMor m = CMor.Morphism  
             (caslSign $ CMor.msource m)
             (caslSign $ CMor.mtarget m)
             (CMor.sort_map m)
             (CMor.op_map m)
             (CMor.pred_map m)
             ()

toRigidMor :: CMor.CASLMor -> RigidExt -> RigidExt -> RigidMor
toRigidMor m extS extT = CMor.Morphism  
             (toRSign (CMor.msource m) extS)
             (toRSign (CMor.mtarget m) extT)
             (CMor.sort_map m)
             (CMor.op_map m)
             (CMor.pred_map m)
             (CMor.DefMorExt emptyRigidExt)
