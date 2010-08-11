{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
{-# LANGUAGE RankNTypes #-}

-- Implementation of LogicT based on the two-continuation model of streams

{- Copyright (c) 2005, Amr Sabry, Chung-chieh Shan, Oleg Kiselyov,
        and Daniel P. Friedman
-}

module Common.SFKT (
  SFKT, runM, observe
) where

import Control.Monad
import Control.Monad.Trans
import Common.LogicT

---------------------------------------------------------------
-- Monad with success, failure continuations, mzero, and mplus
-- We can also split computations using msplit
-- Cf. Hinze's ICFP00 paper, Fig. 8: CPS implementation of BACKTR

-- The extra `r' is just to be compatible with the SRReifT.hs
-- type SG r m a = SFKT m a

newtype SFKT m a  =
  SFKT { unSFKT :: (forall ans. SK (m ans) a -> FK (m ans) -> m ans) }

type FK ans = ans
type SK ans a = a -> FK ans -> ans
-- the success continuation gets one answer(value) and a computation
-- to run to get more answers

instance Monad m => Monad (SFKT m) where
  return e = SFKT (\sk fk -> sk e fk) -- can be eta-reduced, as in Hinze's papr
  m >>= f = -- can be eta-reduced
      SFKT (\sk fk ->
           (unSFKT m) (\a fk' -> unSFKT (f a) sk fk')
             fk)

instance Monad m => MonadPlus (SFKT m) where
  mzero = SFKT (\_ fk -> fk)
  m1 `mplus` m2 = SFKT (\sk fk -> unSFKT m1 sk (unSFKT m2 sk fk))

instance MonadTrans SFKT where
    -- Hinze's promote
    lift m = SFKT (\sk fk -> m >>= (\a -> sk a fk))

instance (MonadIO m) => MonadIO (SFKT m) where
        liftIO = lift . liftIO

-- But this is not in Hinze's paper
instance LogicT SFKT where
    msplit m = lift $ unSFKT m ssk (return Nothing)
        where ssk a fk = return $ Just (a, (lift fk >>= reflect))


-- This is a poly-answer `observe' function of Hinze
runM:: (Monad m) => Maybe Int -> SFKT m a -> m [a]
runM Nothing (SFKT m) = m (\a fk -> fk >>= (return . (a:))) (return [])
runM (Just n) (SFKT _m) | n <=0 = return []
runM (Just 1) (SFKT m) = m (\a _fk -> return [a]) (return [])
runM (Just n) m = unSFKT (msplit m) runM' (return [])
    where runM' Nothing _ = return []
          runM' (Just (a,m')) _ = runM (Just (n-1)) m' >>= (return . (a:))

observe :: Monad m => SFKT m a -> m a
observe m = unSFKT m (\a _fk -> return a) (fail "no answer")
