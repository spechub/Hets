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

joinReadR :: ReadR r a -> ReadR r a -> ReadR r a 
joinReadR r1 r2 =
    ReadR $ \ r -> let re@(Result ds m1) = readR r1 r in
		   case m1 of Nothing -> 
				 let Result rs m2 = readR r2 r
				     in Result (ds++rs) m2
			      Just _ -> re

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

