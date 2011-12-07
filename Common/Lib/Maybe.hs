{- |
Module      :  $Header$
Description :  MaybeT monad transformer without the non-portable features
Copyright   :  C. Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

This module is a replacement of the non-portable module Control.Monad.Maybe

Does *not* contain instance declarations for MonadFix & MonadReader
 & MonadWriter & MonadState

-}

module Common.Lib.Maybe ( MaybeT (..),lift ) where

import Control.Monad ()
import Control.Monad.Trans ()
import Control.Monad.Cont

-- | A monad transformer which adds Maybe semantics to an existing monad.
newtype MaybeT m a = MaybeT { runMaybeT :: m (Maybe a) }

instance (Functor m) => Functor (MaybeT m) where
  fmap f = MaybeT . fmap (fmap f) . runMaybeT

instance (Monad m) => Monad (MaybeT m) where
  fail _ = MaybeT (return Nothing)
  return = lift . return
  x >>= f = MaybeT (runMaybeT x >>= maybe (return Nothing) (runMaybeT . f))

instance (Monad m) => MonadPlus (MaybeT m) where
  mzero = MaybeT (return Nothing)
  mplus x y = MaybeT $ do
                          v <- runMaybeT x
                          case v of
                            Nothing -> runMaybeT y
                            Just _ -> return v


instance MonadTrans MaybeT where
  lift x = MaybeT (liftM Just x)

instance (MonadCont m) => MonadCont (MaybeT m) where
  -- Again, I hope this is correct.
  callCC f = MaybeT (callCC (runMaybeT . f . wrap))
    where wrap :: (Maybe a -> m (Maybe b)) -> a -> MaybeT m b
          wrap c = MaybeT . c . Just

instance (MonadIO m) => MonadIO (MaybeT m) where
  liftIO = lift . liftIO
