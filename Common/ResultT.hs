{- |
Module      :  ./Common/ResultT.hs
Description :  ResultT type and a monadic transformer instance
Copyright   :  (c) T. Mossakowski, C. Maeder, Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

'ResultT' type and a monadic transformer instance
-}

module Common.ResultT where

import Common.Result
import Control.Applicative ()
import Control.Monad
import qualified Control.Monad.Fail as MFail
import Control.Monad.Trans

newtype ResultT m a = ResultT { runResultT :: m (Result a) }

instance Monad m => Functor (ResultT m) where
    fmap f m = ResultT $ do
        r <- runResultT m
        return $ fmap f r

instance Monad m => Applicative (ResultT m) where
    pure = return
    (<*>) = ap

instance Monad m => Monad (ResultT m) where
    return = ResultT . return . return
    m >>= k = ResultT $ do
        r@(Result e v) <- runResultT m
        case v of
          Nothing -> return $ Result e Nothing
          Just a -> do
                s <- runResultT $ k a
                return $ joinResult r s
    fail = ResultT . return . fail

instance Monad m => MFail.MonadFail (ResultT m) where
  fail = ResultT . return . fail

instance MonadTrans ResultT where
    lift m = ResultT $ do
        a <- m
        return $ return a

-- | Inspired by the MonadIO-class
class Monad m => MonadResult m where
    liftR :: Result a -> m a

instance Monad m => MonadResult (ResultT m) where
    liftR = ResultT . return

instance MonadIO m => MonadIO (ResultT m) where
    liftIO = ResultT . liftM return . liftIO
