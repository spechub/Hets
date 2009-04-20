{- |
Module      :  $Header$
Description :  State type from Control.Monad.State but no class MonadState
Copyright   :  C. Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

State type from Control.Monad.State but no class MonadState

This module may be replaced by the (non-nhc98 module) Control.Monad.State

-}


module Common.Lib.State where

-- ---------------------------------------------------------------------------
-- Our fixed state monad
newtype State s a = State { runState :: s -> (a, s) }

instance Functor (State s) where
        fmap f m = State $ \s -> let
                (a, s') = runState m s
                in (f a, s')

instance Monad (State s) where
        return a = State $ \s -> (a, s)
        m >>= k  = State $ \s -> let
                (a, s') = runState m s
                in runState (k a) s'

-- put and get are non-overloaded here!

get :: State s s
get   = State $ \s -> (s, s)

put :: s -> State s ()
put s = State $ const ((), s)

modify :: (s -> s) -> State s ()
modify f = get >>= put . f

gets :: (s -> a) -> State s a
gets f = fmap f get

evalState :: State s a -> s -> a
evalState m = fst . runState m

execState :: State s a -> s -> s
execState m = snd . runState m

mapState :: ((a, s) -> (b, s)) -> State s a -> State s b
mapState f m = State $ f . runState m

withState :: (s -> s) -> State s a -> State s a
withState f m = State $ runState m . f
