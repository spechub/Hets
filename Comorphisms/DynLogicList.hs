{- |
Module      :  ./Comorphisms/DynLogicList.hs
Description :  Automatically modified file, includes the user-defined
               logics in the Hets logic list. Do not change.
Copyright   :  (c) Mihai Codescu, IMAR 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable -}

module Comorphisms.DynLogicList where

import Common.Id
import Logic.Logic
import Logic.HDef
import Logic.SemConstr
import HRigidCASL.Logic_HRigidCASL
import HRigidCASLQuant.Logic_HRigidCASLQuant

dynLogicList :: [AnyLogic]
dynLogicList = [Logic HRigidCASL, Logic HRigidCASLQuant]

dynHLogicList :: [(String, HLogicDef)]
dynHLogicList = [
   ("HRigidCASL", HLogicDef "HRigidCASL" ("RigidCASL", Nothing) False [] [("const", Nothing),("nominal", Nothing)])
  ,("HRigidCASLQuant", HLogicDef "HRigidCASLQuant" ("RigidCASL",Nothing) True [SameInterpretation "rigid sort",SameInterpretation "rigid op",SameInterpretation "rigid pred",SameDomain True] [("const",Nothing),("nominal",Nothing)]) ]