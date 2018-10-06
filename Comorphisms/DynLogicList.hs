{- |
Module      :  ./Comorphisms/DynLogicList.hs
Description :  Automatically modified file, includes the user-defined
               logics in the Hets logic list. Do not change.
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable -}

module Comorphisms.DynLogicList where

import Common.Id
import Logic.Logic
import Logic.HDef
import Logic.SemConstr
import HRigidCASLQuant.Logic_HRigidCASLQuant
import HRigidCASLQuantConstr.Logic_HRigidCASLQuantConstr

dynLogicList :: [AnyLogic]
dynLogicList = [Logic HRigidCASLQuant, Logic HRigidCASLQuantConstr]

dynHLogicList :: [(String, HLogicDef)]
dynHLogicList = [
   ("HRigidCASLQuant", HLogicDef "HRigidCASLQuant" ("RigidCASL", Nothing) False [] [("const", Nothing)])
  ,("HRigidCASLQuantConstr", HLogicDef "HRigidCASLQuantConstr" ("RigidCASL",Nothing) True [SameInterpretation "rigid sort",SameInterpretation "rigid op",SameDomain True] [("const",Nothing)]) ]