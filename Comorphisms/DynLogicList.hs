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

dynLogicList :: [AnyLogic]
dynLogicList = []

dynHLogicList :: [(String, HLogicDef)]
dynHLogicList = []
