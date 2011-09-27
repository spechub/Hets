{- |
Module      :  $Header$
Description :  apply xupdate changes to a development graph
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

adjust development graph according to xupdate information
-}

module Static.ApplyChanges (dgXUpdate) where

import Static.DevGraph
import Static.ToXml
import Static.FromXml
import Static.XSimplePath

import Driver.Options

import Common.LibName
import Common.ResultT

dgXUpdate :: HetcatsOpts -> String -> LibEnv -> LibName -> DGraph
  -> ResultT IO (LibName, LibEnv)
dgXUpdate opts xs le ln dg = do
  xml <- liftR $ changeXml (dGraph le ln dg) xs
  rebuiltDgXml opts le xml
