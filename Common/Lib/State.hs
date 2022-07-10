{- |
Module      :  ./Common/Lib/State.hs
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

module Common.Lib.State where

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Fail as Fail

-- | Our fixed state monad
newtype State s a = State { runState :: s -> (a, s) }

state :: (s -> (a, s)) -> State s a
state = State

instance Functor (State s) where
        fmap = liftM

instance Applicative (State s) where
        pure  = return
        (<*>) = ap

instance Monad (State s) where
        return a = State $ \ s -> (a, s)
        State f >>= k = State $ \ s ->
                let (a, s') = f s in runState (k a) s'

instance Fail.MonadFail (State s) where
  fail str = State $ \_ -> error str

-- put and get are non-overloaded here!

get :: State s s
get = State $ \ s -> (s, s)

put :: s -> State s ()
put s = State $ const ((), s)

modify :: (s -> s) -> State s ()
modify f = get >>= put . f

gets :: (s -> a) -> State s a
gets f = liftM f get

evalState :: State s a -> s -> a
evalState m = fst . runState m

execState :: State s a -> s -> s
execState m = snd . runState m

mapState :: ((a, s) -> (b, s)) -> State s a -> State s b
mapState f m = State $ f . runState m

withState :: (s -> s) -> State s a -> State s a
withState f m = State $ runState m . f
