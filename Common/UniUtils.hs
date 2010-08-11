{- |
Module      :  $Header$
Description :  wrapper for utilities from the uniform workbench
Copyright   :  (c) Christian Maeder DFKI Bremen 2008
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

(child) processes, (sync) events and destruction
-}

module Common.UniUtils
  ( module Posixutil.ChildProcess
  , module Posixutil.ProcessClasses
  , module Events.Events
  , module Events.Destructible
  ) where

import Posixutil.ChildProcess
import Posixutil.ProcessClasses
import Events.Events
import Events.Destructible
