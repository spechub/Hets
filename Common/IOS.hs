{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{- |
Module      :  ./Common/IOS.hs
Description :  An IO State Monad implementation
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable (various -fglasgow-exts extensions)

An IO State Monad implementation taken from
http://www.infosun.fim.uni-passau.de/cl/lehre/funcprog05/folien/s07.pdf

Appearently the IOS type comes from John O'Donnell as you can see in
http://www.mail-archive.com/haskell@haskell.org/msg07405.html

-}

module Common.IOS (IOS (..), runIOS, stmap) where

import Control.Monad.Trans (MonadIO (..))
import Control.Monad.State (MonadState (..))

-- * IO State Monad

-- | An IO State Monad
data IOS s a = IOS { unIOS :: s -> IO (a, s) }

getIOS :: IOS s s
getIOS = IOS (\ s -> return (s, s))

setIOS :: s -> IOS s ()
setIOS s = IOS (\ _ -> return ((), s))

{- not needed
modifyIOS :: (s->s) -> IOS s s
modifyIOS f = IOS (\s -> return (s, f s))
-}

runIOS :: s -> IOS s a -> IO (a, s)
runIOS s cmd = unIOS cmd s

-- | Like fmap but changes the state type, this needs map and unmap functions
stmap :: (s -> s') -> (s' -> s) -> IOS s a -> IOS s' a
stmap map' unmap ios = let f (a, b) = (a, map' b)
                       in IOS (fmap f . unIOS ios . unmap)


instance Monad (IOS s) where
    return x = IOS (\ s -> return (x, s))
    m >>= f = IOS (\ s ->
                       do { (x, s1) <- unIOS m s
                         ; unIOS (f x) s1 } )

instance MonadIO (IOS s) where
    liftIO m = IOS (\ s -> do { a <- m; return (a, s) })

instance MonadState s (IOS s) where
    get = getIOS
    put = setIOS
