{- |
Module      :  $Header$
Copyright   :  (c) Andy Gill 2001,
               (c) Oregon Graduate Institute of Science and Technology, 2001
Licence     :  BSD-style

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
a read only state (copied from Control.Monad.Reader and modified)

-}

module HasCASL.Reader where

import Common.Result
import Common.Lib.State

-- ---------------------------------------------------------------------------
-- Our fixed reader monad 

newtype ReadR r a = ReadR { readR :: r -> Result a }

instance Functor (ReadR r) where
        fmap f m = ReadR $ \r -> do
                a <- readR m r
                return (f a)

instance Monad (ReadR r) where
        return a = ReadR $ \_ -> return a
        m >>= k  = ReadR $ \r -> do
                a <- readR m r
                readR (k a) r
        fail msg = ReadR $ \_ -> fail msg

ask :: ReadR r r
ask = ReadR return

local :: (r -> r') -> ReadR r' a -> ReadR r a
local f m = ReadR $ \r -> readR m (f r)

lift :: Result a -> ReadR r a
lift m = ReadR $ \_ -> m

mapReadR :: (Result a -> Result b) -> ReadR r a -> ReadR r b
mapReadR f m = ReadR $ f . readR m

foldReadR :: (a -> ReadR r b) -> [a] -> ReadR r [b]
foldReadR _ [] = return []
foldReadR m (h:t) = ReadR $ \ r ->
    let Result ds am = readR (m h) r 
	Result rs (Just ls) = readR (foldReadR m t) r  
	in Result (ds ++ rs) $ Just $
	   case am of 
		   Nothing -> ls
		   Just x -> x:ls

withReadR :: (r' -> r) -> ReadR r a -> ReadR r' a
withReadR f m = ReadR $ readR m . f

toResultState :: (s -> r) -> ReadR r a -> State s (Result a) 
toResultState f m = State $ \s -> (readR m $ f s, s)


{- 

-- not quite an instance of StateT
-- but different binding compared to: State s (Maybe a)
newtype StateS s a = StateS { stateS :: s -> (Maybe a, s) }

instance Functor (StateS s) where
        fmap f m = StateS $ \s -> let 
                (x, s') = stateS m s in 
                (fmap f x, s')

bindStateS :: StateS s a -> (a -> StateS s b) -> StateS s b
m `bindStateS` k = StateS $ \s -> let
                (x, s') = stateS m s in
                case x of Nothing -> (Nothing, s')
			  Just a -> stateS (k a) s'

toStateS :: State s a -> StateS s a
toStateS m = StateS $ \s -> let 
	   (x, s') = runState m s in (Just x, s')

fromStateS :: StateS s a -> State s (Maybe a)
fromStateS m = State $ \s -> stateS m s

-}
