{- |
Module      :  $Header$
Description :  analyse xml update input
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Main (main) where

import Common.XUpdate
import Control.Monad.Error
import Control.Monad.Identity

main :: IO ()
main = do
  str <- getContents
  case runIdentity $ runErrorT $ anaXUpdates str of
    Left e -> fail e
    Right cs -> mapM_ print cs
