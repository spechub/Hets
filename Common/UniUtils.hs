{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  wrapper for utilities from the uniform workbench
Copyright   :  (c) Christian Maeder DFKI Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable

(child) processes, (sync) events and destruction
-}

module Common.UniUtils
  ( module ChildProcess
  , module ProcessClasses
  , module Events
  , module Destructible
  ) where

#ifdef UNIVERSION2
import Posixutil.ChildProcess as ChildProcess
import Posixutil.ProcessClasses as ProcessClasses
import Events.Events as Events
import Events.Destructible as Destructible
#else
import ChildProcess
import ProcessClasses
import Events
import Destructible
#endif
