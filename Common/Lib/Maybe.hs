{- |
Module      :  ./Common/Lib/Maybe.hs
Description :  MaybeT monad transformer without the non-portable features
Copyright   :  C. Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

This module is a replacement of module Control.Monad.Maybe
and only contains the Monad instance for the newtype MaybeT m.

-}

module Common.Lib.Maybe (MaybeT (..), liftToMaybeT) where

import Control.Applicative
import Control.Monad

-- | A monad transformer which adds Maybe semantics to an existing monad.
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance Monad m => Functor (MaybeT m) where
  fmap = liftM

instance Monad m => Applicative (MaybeT m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (MaybeT m) where
  fail _ = MaybeT $ return Nothing
  return = MaybeT . return . Just
  x >>= f = MaybeT $ runMaybeT x >>= maybe (return Nothing) (runMaybeT . f)

liftToMaybeT :: Monad m => m a -> MaybeT m a
liftToMaybeT = MaybeT . liftM Just
