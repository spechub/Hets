{- |
Module      :  ./Comorphisms/DynComorphismList.hs
Description :  Automatically modified file, includes the user-defined
               comorphisms in the Hets logic list. Do not change.
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable -}

module Comorphisms.DynComorphismList where

import Logic.Logic
import Logic.Comorphism
import Comorphisms.RigidCASL2HRigidCASLQuant
import Comorphisms.RigidCASL2HRigidCASLQuantConstr
import Comorphisms.HRigid2CASL

dynComorphismList :: [AnyComorphism]
dynComorphismList = [Comorphism RigidCASL2HRigidCASLQuant, Comorphism RigidCASL2HRigidCASLQuantConstr, Comorphism HRigid2CASL]