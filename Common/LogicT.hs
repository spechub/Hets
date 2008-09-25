{- |
Module      :  $Header$
Description :  colimit of an arbitrary diagram in Set
Copyright   :  (c) 2005, Amr Sabry, Chung-chieh Shan, Oleg Kiselyov,
        and Daniel P. Friedman
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Mihai.Codescu@dfki.de
Stability   :  provisional
Portability :  portable

Logic Monad Transformer: MonadPlusT with interleave, bindi, ifte and once
Definition and implementation of generic operations, in terms of msplit
-}

module Common.LogicT (
  LogicT(..), bagofN, reflect
) where

import Monad
import Control.Monad.Trans

class MonadTrans t => LogicT t where
    msplit :: (Monad m, MonadPlus (t m)) => t m a -> t m (Maybe (a, t m a))


    -- All other things are implemneted in terms of MonadPlus + msplit
    -- All the functions below have generic implementations

    -- fair disjunction
    interleave :: (Monad m, MonadPlus (t m)) =>
                  t m a -> t m a -> t m a
    -- Note the generic implementation below
    -- The code is *verbatim* from Logic.hs
    interleave sg1 sg2 =
        do r <- msplit sg1
           case r of
                  Nothing -> sg2
                  Just (sg11,sg12) -> (return sg11) `mplus`
                                      (interleave sg2 sg12)

    -- just conventional aliases
    gsuccess:: (Monad m, MonadPlus (t m)) => a -> t m a
    gsuccess = return
    gfail :: (Monad m, MonadPlus (t m)) => t m a
    gfail = mzero

    -- standard `bind' is the conjunction
    -- the following is a fair conjunction
    -- Again, the old Logic.hs code works verbatim
    bindi:: (Monad m, MonadPlus (t m)) =>
            t m a -> (a -> t m b) -> t m b
    bindi sg g = do r <- msplit sg
                    case r of
                       Nothing -> mzero
                       Just (sg1,sg2) ->  interleave
                                            (g sg1)
                                            (bindi sg2 g)

    -- Pruning things

    -- Soft-cut (aka if-then-else)
    -- ifte t th el = (or (and t th) (and (not t) el))
    -- However, t is evaluated only once
    ifte :: (Monad m, MonadPlus (t m)) =>
            t m a -> (a -> t m b) -> t m b -> t m b
    ifte t th el =
        do r <- msplit t
           case r of
                  Nothing -> el
                  Just (sg1,sg2) -> (th sg1) `mplus` (sg2 >>= th)

    once :: (Monad m, MonadPlus (t m)) => t m a -> t m a
    once m =
        do r <- msplit m
           case r of
                  Nothing -> mzero
                  Just (sg1,_) -> return sg1

{- A particular transformer must define
    -- The inverse of `lift'. Hinze calls it `observe'. Others may call
    -- it `down'. It gives the first answer (or fails if there aren't any)
    observe :: (Monad m) => t m a -> m a
 It can't be put into the LogicT class because of in teh case of SRReif,
 the variable `r' will escape
-}

-- The following functions are not in the class LogicT
-- Their implementation is generic

    -- Note: the following gives t m [a] answer. To get back `m [a]'
    -- we should call ``observe''
    -- This is similar to Hinze's `sol' (at the very end of Section
    -- 4.3, only we can select the arbitrary number of answers
    -- and do that even for non-stream-based monad)

bagofN :: (Monad m, LogicT t, MonadPlus (t m)) => Maybe Int -> t m a -> t m [a]
bagofN (Just n) _ | n <= 0  = return []
bagofN n m = msplit m >>= bagofN'
    where bagofN' Nothing = return []
          bagofN' (Just (a, m')) = bagofN (fmap ((-1) +) n) m'
                                   >>= return . (a :)


    -- This is like the opposite of `msplit'
    -- The law is: msplit tm >>= reflect === tm
reflect :: (Monad m, LogicT t, MonadPlus (t m)) => Maybe (a, t m a) -> t m a
reflect r = case r of
                   Nothing -> mzero
                   Just (a,tmr) -> return a `mplus` tmr
