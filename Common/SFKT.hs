{-# LANGUAGE RankNTypes #-}
{- |
Module      :  ./Common/SFKT.hs
Copyright   :  (c) 2005, Amr Sabry, Chung-chieh Shan, Oleg Kiselyov
                and Daniel P. Friedman
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (RankNTypes)

Implementation of LogicT based on the two-continuation model of streams
-}

module Common.SFKT
  ( SFKT
  , runM
  , observe
  ) where

import Control.Applicative
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Monad.Trans
import Common.LogicT

{- Monad with success, failure continuations, mzero, and mplus
We can also split computations using msplit
Cf. Hinze's ICFP00 paper, Fig. 8: CPS implementation of BACKTR -}

{- The extra `r' is just to be compatible with the SRReifT.hs
type SG r m a = SFKT m a -}

newtype SFKT m a =
  SFKT { unSFKT :: forall ans . SK (m ans) a -> FK (m ans) -> m ans }

type FK ans = ans
type SK ans a = a -> FK ans -> ans
{- the success continuation gets one answer(value) and a computation
to run to get more answers -}

instance Monad m => Functor (SFKT m) where
  fmap = liftM

instance Monad m => Applicative (SFKT m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (SFKT m) where
  return e = SFKT (\ sk -> sk e)
  m >>= f = SFKT (\ sk -> unSFKT m (\ a -> unSFKT (f a) sk))

instance Monad m => Alternative (SFKT m) where
  (<|>) = mplus
  empty = mzero

instance Monad m => MonadPlus (SFKT m) where
  mzero = SFKT (\ _ fk -> fk)
  m1 `mplus` m2 = SFKT (\ sk fk -> unSFKT m1 sk (unSFKT m2 sk fk))

instance Fail.MonadFail m => Fail.MonadFail (SFKT m) where
  fail str = SFKT (\ _ _ -> Fail.fail str)

instance MonadTrans SFKT where
    -- Hinze's promote
    lift m = SFKT (\ sk fk -> m >>= (`sk` fk))

instance (MonadIO m) => MonadIO (SFKT m) where
        liftIO = lift . liftIO

-- But this is not in Hinze's paper
instance LogicT SFKT where
    msplit m = lift $ unSFKT m ssk (return Nothing)
        where ssk a fk = return $ Just (a, lift fk >>= reflect)


-- This is a poly-answer `observe' function of Hinze
runM :: (Monad m) => Maybe Int -> SFKT m a -> m [a]
runM Nothing (SFKT m) = m (\ a -> liftM (a :)) (return [])
runM (Just n) (SFKT _m) | n <= 0 = return []
runM (Just 1) (SFKT m) = m (\ a _fk -> return [a]) (return [])
runM (Just n) m = unSFKT (msplit m) runM' (return [])
    where runM' Nothing _ = return []
          runM' (Just (a, m')) _ = liftM (a :) (runM (Just (n - 1)) m')

observe :: Fail.MonadFail m => SFKT m a -> m a
observe m = unSFKT m (\ a _fk -> return a) (Fail.fail "no answer")
