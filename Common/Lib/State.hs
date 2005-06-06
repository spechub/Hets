-----------------------------------------------------------------------------
-- |
-- Module      :  $Header$
-- Copyright   :  (c) Andy Gill 2001,
--		  (c) Oregon Graduate Institute of Science and Technology, 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  hets@tzi.de
-- Stability   :  experimental
-- Portability :  portable
--
-- State type from Control.Monad.State without State Monad
--
-----------------------------------------------------------------------------

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
put s = State $ \_ -> ((), s)

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
