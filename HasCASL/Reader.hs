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

mapReadR :: (Result a -> Result b) -> ReadR w a -> ReadR w b
mapReadR f m = ReadR $ f . readR m

withReadR :: (r' -> r) -> ReadR r a -> ReadR r' a
withReadR f m = ReadR $ readR m . f

toState :: (s -> r) -> ReadR r a -> State s (Result a) 
toState f m = State $ \s -> (readR m $ f s, s)
