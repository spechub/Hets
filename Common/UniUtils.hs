{- |
Module      :  $Header$
Description :  wrapper for utilities from the uniform workbench
Copyright   :  (c) Christian Maeder DFKI Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

(child) processes, (sync) events and destruction
-}

module Common.UniUtils (module X) where

import Posixutil.ChildProcess as X
import Posixutil.ProcessClasses as X
import Events.Events as X
import Events.Destructible as X
