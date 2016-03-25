{- |
Module      :  ./Common/Lattice.hs
Description :  lattice classes
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Common.Lattice where

class (Ord l, Show l) => Lattice l where
  cjoin :: l -> l -> l
  ctop :: l
  bot :: l

instance Lattice () where
  cjoin _ _ = ()
  ctop = ()
  bot = ()

instance Lattice Bool where
  cjoin = (||)
  ctop = True
  bot = False

instance (Lattice a, Lattice b) => Lattice (a, b) where
  cjoin (a, b) (c, d) = (cjoin a c, cjoin b d)
  ctop = (ctop, ctop)
  bot = (bot, bot)
