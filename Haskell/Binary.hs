{- |
Module      :  $Header$
Description :  basic Binary instance
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Haskell.Binary () where

import Haskell.BaseATC ()
import Common.BinaryInstances
import SrcLoc

instance Binary SrcLoc where
  put xv = case xv of
    SrcLoc a b c d -> do
      put a
      put b
      put c
      put d
  get = do
      a <- get
      b <- get
      c <- get
      d <- get
      return $ SrcLoc a b c d
