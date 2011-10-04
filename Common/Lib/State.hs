{- |
Module      :  $Header$
Description :  State type from Control.Monad.State but no class MonadState
Copyright   :  C. Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

State type from Control.Monad.State but no class MonadState

This module was a replacement of the (non-haskell98) module
Control.Monad.State, but now Control.Monad.Trans.State can be used instead.

-}

module Common.Lib.State (module Control.Monad.Trans.State) where

import Control.Monad.Trans.State
